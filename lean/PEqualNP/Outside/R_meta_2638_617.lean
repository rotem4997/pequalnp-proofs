import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds SimpleGraph BigOperators

-- The leaf bound is established here for a monotone tree.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2638_617
    (toMono : ∀ (n s : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (z : Fin n)
        (f : (Fin n → Bool) → Bool),
        (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
        (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
        (∀ i j, G.Adj i j → i ∉ A) → z ∉ A →
        (∀ x, f x = true ↔ (∃ i ∈ A, x i = true) ∨
          ∃ i j, (G.deleteEdges (G.incidenceSet z)).Adj i j ∧ x i = true ∧ x j = true) →
        HasCircuitSize n f s →
        ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = f x)
    (toTree : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (z : Fin n)
        (C : Circuit),
        (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
        (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
        (∀ i j, G.Adj i j → i ∉ A) → z ∉ A →
        Monotone2 C →
        (∀ x, C.eval (List.ofFn x) = true ↔ (∃ i ∈ A, x i = true) ∨
          ∃ i j, (G.deleteEdges (G.incidenceSet z)).Adj i j ∧ x i = true ∧ x j = true) →
        ∃ t : DMFormula n, t.leaves ≤ C.size + 1 ∧
          (DMFormula.rec (motive := fun _ => Prop) (fun _ b => b = true) (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b) t) ∧ ∀ x, t.eval x = C.eval (List.ofFn x))
    : ∀ (x1 x2 x3 : ℕ) (x4 : SimpleGraph (Fin x1)) (x5 : Finset (Fin x1)) (x6 : Fin x1) (x7 : (Fin x1 → Bool) → Bool), (∀ x8 ∉ x5, (x4.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x4.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x4.Adj x10 x11 → x10 ∉ x5) → (∃ (x11 : Fin x1) (x12 : Fin x1), x4.Adj x11 x12) → x6 ∉ x5 → (∀ (x13 : Fin x1 → Bool), x7 x13 = Bool.true ↔ (∃ x14 ∈ x5, x13 x14 = Bool.true) ∨ ∃ (x14 : Fin x1) (x15 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x14 x15 ∧ x13 x14 = Bool.true ∧ x13 x15 = Bool.true) → (∀ (x14 : Finset (Fin x1)), (∀ (x15 x16 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x15 x16 → x15 ∈ x14 ∨ x16 ∈ x14) → x2 ≤ x14.card) → PEqualNP.MetaComplexity.HasCircuitSize x1 x7 x3 → x5.card + (x4.deleteEdges (x4.incidenceSet x6)).edgeSet.ncard + x2 ≤ x3 + (1 : ℕ) := by
  classical
  have noEdge (n : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
      (sub : H ≤ G) (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
      (v w : Fin n) (col : v = w ∨ H.Adj v w) :
      let U : Fin n → Bool := fun a => decide ((H.Adj v a ∨ H.Adj w a) ∧ a ≠ v ∧ a ≠ w)
      ∀ i j, H.Adj i j → ¬ (U i = true ∧ U j = true) := by
    have tri (a b c : Fin n) (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a) : False := by
      let p : G.Walk a a := Walk.cons ab (Walk.cons bc (Walk.cons ca Walk.nil))
      have h : p.IsCycle := by
        change (Walk.cons ab (Walk.cons bc (Walk.cons ca Walk.nil))).IsCycle
        rw [Walk.cons_isCycle_iff]
        constructor
        · simp [Walk.cons_isPath_iff, bc.ne, ca.ne, ab.ne.symm]
        · simp [ab.ne, ab.ne.symm, bc.ne, ca.ne.symm]
      have bad := girth a p h
      simp [p] at bad
    have square (a b c d : Fin n) (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d)
        (da : G.Adj d a) (ac : a ≠ c) (bd : b ≠ d) : False := by
      let p : G.Walk a a := Walk.cons ab (Walk.cons bc (Walk.cons cd (Walk.cons da Walk.nil)))
      have h : p.IsCycle := by
        change (Walk.cons ab (Walk.cons bc (Walk.cons cd (Walk.cons da Walk.nil)))).IsCycle
        rw [Walk.cons_isCycle_iff]
        constructor
        · simp [Walk.cons_isPath_iff, bc.ne, cd.ne, da.ne, bd, ab.ne.symm, Ne.symm ac]
        · simp [ab.ne, bc.ne, ac, bd, ab.ne.symm, da.ne.symm]
      have bad := girth a p h
      simp [p] at bad
    dsimp only
    intro i j ij pair
    obtain ⟨hi,hj⟩ := pair
    obtain ⟨nearI, iv, iw⟩ := of_decide_eq_true hi
    obtain ⟨nearJ, jv, jw⟩ := of_decide_eq_true hj
    rcases col with eq | vw
    · subst w
      exact tri v i j (sub (nearI.elim id id)) (sub ij) (sub (nearJ.elim id id)).symm
    · rcases nearI with vi | wi <;> rcases nearJ with vj | wj
      · exact tri v i j (sub vi) (sub ij) (sub vj).symm
      · exact square v i j w (sub vi) (sub ij) (sub wj).symm (sub vw).symm (Ne.symm jv) iw
      · exact square w i j v (sub wi) (sub ij) (sub vj).symm (sub vw) (Ne.symm jw) iv
      · exact tri w i j (sub wi) (sub ij) (sub wj).symm
  have formulaRect (n : ℕ) (t : DMFormula n)
      (positive : DMFormula.rec (motive := fun _ => Prop) (fun _ b => b = true) (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b) t) :
      ∃ (X Y : Fin t.leaves → (Fin n → Bool) → Prop) (lab : Fin t.leaves → Fin n),
        ∀ x y : Fin n → Bool, t.eval x = true → t.eval y = false →
        (∃! i, X i x ∧ Y i y) ∧
        ∀ i, X i x → Y i y → x (lab i) = true ∧ y (lab i) = false := by
    let Pos : DMFormula n → Prop := DMFormula.rec (motive := fun _ => Prop) (fun _ b => b = true) (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b)
    let Cert (t : DMFormula n) : Prop :=
      ∃ (X Y : Fin t.leaves → (Fin n → Bool) → Prop) (lab : Fin t.leaves → Fin n),
        ∀ x y : Fin n → Bool, t.eval x = true → t.eval y = false →
        (∃! i, X i x ∧ Y i y) ∧
        ∀ i, X i x → Y i y → x (lab i) = true ∧ y (lab i) = false
    have combine (p q t : DMFormula n) (e : Fin p.leaves ⊕ Fin q.leaves ≃ Fin t.leaves)
        (lx ly rx ry : (Fin n → Bool) → Prop)
        (route : ∀ x y, t.eval x = true → t.eval y = false →
          ((lx x ∧ ly y) ∧ ¬(rx x ∧ ry y) ∧ p.eval x = true ∧ p.eval y = false) ∨
          ((rx x ∧ ry y) ∧ ¬(lx x ∧ ly y) ∧ q.eval x = true ∧ q.eval y = false))
        (cp : Cert p) (cq : Cert q) : Cert t := by
      obtain ⟨xp, yp, lp, hp⟩ := cp
      obtain ⟨xq, yq, lq, hq⟩ := cq
      let X : Fin p.leaves ⊕ Fin q.leaves → (Fin n → Bool) → Prop :=
        Sum.elim (fun i x => lx x ∧ xp i x) (fun i x => rx x ∧ xq i x)
      let Y : Fin p.leaves ⊕ Fin q.leaves → (Fin n → Bool) → Prop :=
        Sum.elim (fun i y => ly y ∧ yp i y) (fun i y => ry y ∧ yq i y)
      let L : Fin p.leaves ⊕ Fin q.leaves → Fin n := Sum.elim lp lq
      refine ⟨fun i => X (e.symm i), fun i => Y (e.symm i), fun i => L (e.symm i), ?_⟩
      intro x y hx hy
      have localResult :
          (∃! i, X i x ∧ Y i y) ∧
          ∀ i, X i x → Y i y → x (L i) = true ∧ y (L i) = false := by
        rcases route x y hx hy with leftRoute | rightRoute
        · obtain ⟨⟨dx, dy⟩, excl, ax, ay⟩ := leftRoute
          obtain ⟨⟨i, ⟨ix, iy⟩, only⟩, label⟩ := hp x y ax ay
          constructor
          · refine ⟨.inl i, ⟨⟨dx, ix⟩, ⟨dy, iy⟩⟩, ?_⟩
            rintro (j | j) ⟨xj, yj⟩
            · exact congrArg Sum.inl (only j ⟨xj.2, yj.2⟩)
            · exact (excl ⟨xj.1, yj.1⟩).elim
          · rintro (j | j) xj yj
            · exact label j xj.2 yj.2
            · exact (excl ⟨xj.1, yj.1⟩).elim
        · obtain ⟨⟨dx, dy⟩, excl, ax, ay⟩ := rightRoute
          obtain ⟨⟨i, ⟨ix, iy⟩, only⟩, label⟩ := hq x y ax ay
          constructor
          · refine ⟨.inr i, ⟨⟨dx, ix⟩, ⟨dy, iy⟩⟩, ?_⟩
            rintro (j | j) ⟨xj, yj⟩
            · exact (excl ⟨xj.1, yj.1⟩).elim
            · exact congrArg Sum.inr (only j ⟨xj.2, yj.2⟩)
          · rintro (j | j) xj yj
            · exact (excl ⟨xj.1, yj.1⟩).elim
            · exact label j xj.2 yj.2
      obtain ⟨⟨i, hi, unq⟩, labels⟩ := localResult
      constructor
      · refine ⟨e i, by simpa using hi, ?_⟩
        intro j hj
        exact e.symm_apply_eq.mp (unq (e.symm j) hj)
      · exact fun j => labels (e.symm j)
    have go (t : DMFormula n) : Pos t → Cert t := by
      induction t with
      | lit i b =>
        intro hb
        change b = true at hb
        subst b
        refine ⟨fun _ x => x i = true, fun _ y => y i = false, fun _ => i, ?_⟩
        intro x y hx hy
        change x i = true at hx
        change y i = false at hy
        refine ⟨⟨⟨0, Nat.zero_lt_one⟩, ⟨hx,hy⟩, ?_⟩, ?_⟩
        · intro j _
          apply Fin.ext
          change j.val = 0
          have h : j.val < 1 := j.isLt
          omega
        · exact fun _ a b => ⟨a,b⟩
      | and p q ip iq =>
        intro h
        change Pos p ∧ Pos q at h
        apply combine p q (.and p q) finSumFinEquiv (fun _ => True) (fun y => p.eval y = false)
          (fun _ => True) (fun y => p.eval y = true) _ (ip h.1) (iq h.2)
        intro x y hx hy
        change (p.eval x && q.eval x) = true at hx
        change (p.eval y && q.eval y) = false at hy
        cases ax : p.eval x <;> cases bx : q.eval x <;> cases ay : p.eval y <;> cases byq : q.eval y <;>
          simp [ax,bx,ay,byq] at hx hy ⊢
      | or p q ip iq =>
        intro h
        change Pos p ∧ Pos q at h
        apply combine p q (.or p q) finSumFinEquiv (fun x => p.eval x = true) (fun _ => True)
          (fun x => p.eval x = false) (fun _ => True) _ (ip h.1) (iq h.2)
        intro x y hx hy
        change (p.eval x || q.eval x) = true at hx
        change (p.eval y || q.eval y) = false at hy
        cases ax : p.eval x <;> cases bx : q.eval x <;> cases ay : p.eval y <;> cases byq : q.eval y <;>
          simp [ax,bx,ay,byq] at hx hy ⊢
    exact go t positive
  have tableBound (n m : ℕ) (H : SimpleGraph (Fin n)) (X Y : Fin m → Fin n → Fin n → Prop)
      (lab : Fin m → Fin n) (table : ∀ a b v w, H.Adj a b → (v = w ∨ H.Adj v w) →
          (∃! i, X i a b ∧ Y i v w) ∧
          (∀ i, X i a b → Y i v w → (lab i = a ∨ lab i = b) ∧
            ¬ ((H.Adj v (lab i) ∨ H.Adj w (lab i)) ∧ lab i ≠ v ∧ lab i ≠ w))) :
        ∃ T : Finset (Fin n), (∀ a b, H.Adj a b → a ∈ T ∨ b ∈ T) ∧
          H.edgeSet.ncard + T.card ≤ m := by
    classical
    let E := H.edgeSet
    let V := Fin n
    let p (e : E) : V := e.1.out.1
    let q (e : E) : V := e.1.out.2
    have ends (e : E) : s(p e,q e) = e.1 := Sym2.mk_fst_out_snd_out _
    have edge (e : E) : H.Adj (p e) (q e) := H.mem_edgeSet.mp (by rw [ends]; exact e.2)
    let pick (e : E) (a b : V) (h : a = b ∨ H.Adj a b) : Fin m :=
      (table _ _ a b (edge e) h).1.exists.choose
    have chosen (e : E) (a b : V) (h : a = b ∨ H.Adj a b) :
        X (pick e a b h) (p e) (q e) ∧ Y (pick e a b h) a b :=
      (table _ _ a b (edge e) h).1.exists.choose_spec
    let cell (e : E) (a b : V) (h : a = b ∨ H.Adj a b) := lab (pick e a b h)
    have cellProp (e : E) (a b : V) (h : a = b ∨ H.Adj a b) :
        cell e a b h ∈ e.1 ∧ ¬ ((H.Adj a (cell e a b h) ∨ H.Adj b (cell e a b h)) ∧
          cell e a b h ≠ a ∧ cell e a b h ≠ b) := by
      have rule := (table _ _ a b (edge e) h).2 _ (chosen e a b h).1 (chosen e a b h).2
      exact ⟨by rw [← ends e]; exact Sym2.mem_iff.mpr rule.1, rule.2⟩
    have near (e : E) (u v : V) (hu : u ∈ e.1) (hv : v ∈ e.1) (hne : u ≠ v) : H.Adj u v :=
      H.mem_edgeSet.mp (by rw [← (Sym2.mem_and_mem_iff hne).mp ⟨hu,hv⟩]; exact e.2)
    have single (e : E) (v : V) (hv : v ∈ e.1) : cell e v v (.inl rfl) = v := by
      obtain ⟨hr,hn⟩ := cellProp e v v (.inl rfl)
      by_contra ne
      exact hn ⟨Or.inl (near e v _ hv hr (Ne.symm ne)),ne,ne⟩
    have across (e d : E) (v : V) (hv : v ∈ e.1) (hd : v ∈ d.1) (diff : e ≠ d) :
        cell e (p d) (q d) (.inr (edge d)) = v := by
      let u := cell e (p d) (q d) (.inr (edge d))
      obtain ⟨hu,hn⟩ := cellProp e (p d) (q d) (.inr (edge d))
      change u ∈ e.1 at hu
      change u = v
      by_contra ne
      have ud : u ∉ d.1 := fun hud => diff (Subtype.ext
        (((Sym2.mem_and_mem_iff ne).mp ⟨hu,hv⟩).trans ((Sym2.mem_and_mem_iff ne).mp ⟨hud,hd⟩).symm))
      rw [← ends d, Sym2.mem_iff] at hd ud
      have adjacent := near e v u hv hu (Ne.symm ne)
      change ¬ ((H.Adj (p d) u ∨ H.Adj (q d) u) ∧ u ≠ p d ∧ u ≠ q d) at hn
      exact hn ⟨hd.elim (fun h => Or.inl ((congrArg (fun k => H.Adj k u) h).mp adjacent))
        (fun h => Or.inr ((congrArg (fun k => H.Adj k u) h).mp adjacent)),
        fun h => ud (Or.inl h),fun h => ud (Or.inr h)⟩
    let win (e : E) := cell e (p e) (q e) (.inr (edge e))
    have winMem (e : E) : win e ∈ e.1 := (cellProp e (p e) (q e) (.inr (edge e))).1
    let lose (e : E) := Sym2.Mem.other (winMem e)
    have loseMem (e : E) : lose e ∈ e.1 := Sym2.other_mem _
    have opposite (e : E) : lose e ≠ win e := Sym2.other_ne (H.not_isDiag_of_mem_edgeSet e.2) _
    let T : Finset V := Finset.univ.image win
    have cover (a b : V) (h : H.Adj a b) : a ∈ T ∨ b ∈ T := by
      let e : E := ⟨s(a,b), H.mem_edgeSet.mpr h⟩
      have memWin : win e ∈ T := Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩
      rcases Sym2.mem_iff.mp (winMem e) with eq | eq
      · exact Or.inl (eq ▸ memWin)
      · exact Or.inr (eq ▸ memWin)
    let col (v a b : V) : Fin m → ℚ := fun i => if lab i = v ∧ Y i a b then 1 else 0
    let obs (v : V) (e : E) : (Fin m → ℚ) →ₗ[ℚ] ℚ :=
      ∑ i : Fin m, if X i (p e) (q e) ∧ lab i = v then LinearMap.proj i else 0
    have measure (v u : V) (e : E) (a b : V) (h : a = b ∨ H.Adj a b) :
        obs v e (col u a b) = if cell e a b h = v ∧ v = u then 1 else 0 := by
      let j := pick e a b h
      have hj := chosen e a b h
      have formula : obs v e (col u a b) =
          ∑ i : Fin m, if X i (p e) (q e) ∧ lab i = v then col u a b i else 0 := by
        dsimp only [obs]
        rw [LinearMap.sum_apply]
        apply Finset.sum_congr rfl
        intro i _
        split <;> simp_all only [LinearMap.proj_apply, LinearMap.zero_apply]
      rw [formula, Finset.sum_eq_single j]
      · change (if X j (p e) (q e) ∧ lab j = v then col u a b j else 0) =
          if lab j = v ∧ v = u then 1 else 0
        change X j (p e) (q e) ∧ Y j a b at hj
        by_cases hv : lab j = v
        · simp [hj.1,hj.2,hv,col]
        · simp [hj.1,hv]
      · intro i _ ne
        by_cases hx : X i (p e) (q e) ∧ lab i = v
        · have hy : ¬ Y i a b := fun y => ne ((table _ _ a b (edge e) h).1.unique ⟨hx.1,y⟩ hj)
          simp [hx,col,hy]
        · simp [hx]
      · simp
    let ve (e : E) : Fin m → ℚ := col (lose e) (lose e) (lose e) - col (lose e) (p e) (q e)
    let vt (v : V) : Fin m → ℚ := col v v v
    have vtest (v u : V) (e : E) (hv : v ∈ e.1) :
        obs v e (vt u) = if v = u then 1 else 0 := by
      dsimp only [vt]
      rw [measure v u e u u (.inl rfl)]
      by_cases he : v = u
      · subst u
        simp [single e v hv]
      · simp [he]
    have etest (v : V) (e d : E) (hv : v ∈ e.1) :
        obs v e (ve d) = if v = lose d ∧ e = d then 1 else 0 := by
      dsimp only [ve]
      rw [map_sub, measure v (lose d) e (lose d) (lose d) (.inl rfl),
        measure v (lose d) e (p d) (q d) (.inr (edge d))]
      by_cases he : v = lose d
      · subst v
        by_cases ed : e = d
        · subst e
          have ne : cell d (p d) (q d) (.inr (edge d)) ≠ lose d := (opposite d).symm
          simp [single d (lose d) (loseMem d),ne]
        · simp [single e (lose d) hv,across e d (lose d) hv (loseMem d) ed,ed]
      · simp [he]
    let vec : E ⊕ T → Fin m → ℚ := Sum.elim ve (fun v => vt v.1)
    have independent : LinearIndependent ℚ vec := by
      apply Fintype.linearIndependent_iff.mpr
      intro c hc
      have line (v : V) (e : E) (hv : v ∈ e.1) :
          (if v = lose e then c (.inl e) else 0) +
            (∑ t : T, if v = t.1 then c (.inr t) else 0) = 0 := by
        have z := congrArg (obs v e) hc
        simp only [map_add, map_sum, map_smul, map_zero, Fintype.sum_sum_type, vec, Sum.elim_inl, Sum.elim_inr] at z
        simp_rw [etest v e _ hv, vtest v _ e hv] at z
        have sx : (∑ d : E, c (.inl d) • (if v = lose d ∧ e = d then (1 : ℚ) else 0)) =
            (if v = lose e then c (.inl e) else 0) := by
          rw [Finset.sum_eq_single e]
          · by_cases he : v = lose e <;> simp [he]
          · intro d _ ne
            simp [Ne.symm ne]
          · simp
        rw [sx] at z
        simpa only [smul_eq_mul, mul_ite, mul_one, mul_zero] using z
      have zeroT (t : T) : c (.inr t) = 0 := by
        obtain ⟨e, _, he⟩ := Finset.mem_image.mp t.2
        have mem : t.1 ∈ e.1 := he ▸ winMem e
        have neq : t.1 ≠ lose e := he ▸ (opposite e).symm
        have row := line t.1 e mem
        simp only [ite_eq_right neq,zero_add] at row
        rw [Finset.sum_eq_single t] at row
        · simpa using row
        · intro d _ ne
          have hn : t.1 ≠ d.1 := fun eq => ne (Subtype.ext eq.symm)
          simp [hn]
        · simp
      intro j
      cases j with
      | inl e => simpa [zeroT] using line (lose e) e (loseMem e)
      | inr t => exact zeroT t
    refine ⟨T,cover,?_⟩
    have count := independent.fintype_card_le_finrank
    have countE : Fintype.card E = H.edgeSet.ncard := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_coe_set_eq _
    simpa [Fintype.card_sum,countE,Module.finrank_pi] using count

  -- Every monotone formula for an edge function with isolated OR inputs obeys this bound
  -- whenever the ambient graph has no triangles or squares.
  have formulaLower (n : ℕ) (G H : SimpleGraph (Fin n)) (sub : H ≤ G)
      (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
      (A : Finset (Fin n)) (disjoint : ∀ a b, H.Adj a b → a ∉ A)
      (t : DMFormula n) (positive : DMFormula.rec (motive := fun _ => Prop) (fun _ b => b = true) (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b) t)
      (yes : ∀ x, t.eval x = true ↔ (∃ a ∈ A, x a = true) ∨
        ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true) :
      ∃ T : Finset (Fin n), (∀ a b, H.Adj a b → a ∈ T ∨ b ∈ T) ∧
        A.card + H.edgeSet.ncard + T.card ≤ t.leaves := by
    obtain ⟨X, Y, lab, cert⟩ := formulaRect n t positive
    let row (a b : Fin n) : Fin n → Bool := fun v => decide (v = a ∨ v = b)
    let col (a b : Fin n) : Fin n → Bool := fun v =>
      decide ((H.Adj a v ∨ H.Adj b v) ∧ v ≠ a ∧ v ≠ b)
    have rowOn (a b : Fin n) (h : H.Adj a b) : t.eval (row a b) = true :=
      (yes _).mpr (Or.inr ⟨a,b,h,by simp [row],by simp [row]⟩)
    have colOff (a b : Fin n) (hab : a = b ∨ H.Adj a b) : t.eval (col a b) = false := by
      apply Bool.eq_false_iff.mpr
      intro on
      rcases (yes _).mp on with ⟨v, mem, hv⟩ | ⟨i,j,he,hi,hj⟩
      · have hv' : (H.Adj a v ∨ H.Adj b v) ∧ v ≠ a ∧ v ≠ b := of_decide_eq_true hv
        rcases hv'.1 with h | h
        · exact disjoint v a h.symm mem
        · exact disjoint v b h.symm mem
      · exact noEdge n G H sub girth a b hab i j he ⟨hi,hj⟩
    -- Every marked vertex needs its own leaf, by comparing its singleton with the empty input.
    have noneOn : t.eval (fun _ => false) = false := by
      apply Bool.eq_false_iff.mpr
      intro on
      simpa using (yes _).mp on
    have markLeaf (a : A) : ∃ i : Fin t.leaves, lab i = a.val := by
      let x : Fin n → Bool := fun v => decide (v = a.val)
      have on : t.eval x = true := (yes _).mpr (Or.inl ⟨a.val,a.property,by simp [x]⟩)
      obtain ⟨⟨i, ⟨ix,iy⟩, _⟩, sound⟩ := cert x (fun _ => false) on noneOn
      exact ⟨i, of_decide_eq_true (sound i ix iy).1⟩
    choose pick picked using markLeaf
    let I := {i : Fin t.leaves // lab i ∉ A}
    let m := Fintype.card I
    let e : Fin m ≃ I := (Fintype.equivFin I).symm
    have budget : A.card + m ≤ t.leaves := by
      let embed : A ⊕ I → Fin t.leaves := Sum.elim pick Subtype.val
      have injective : Function.Injective embed := by
        rintro (a | i) (b | j) h
        · change pick a = pick b at h
          have eq := congrArg lab h
          rw [picked, picked] at eq
          exact congrArg Sum.inl (Subtype.ext eq)
        · change pick a = j.val at h
          exact (j.property (by rw [← h, picked]; exact a.property)).elim
        · change i.val = pick b at h
          exact (i.property (by rw [h, picked]; exact b.property)).elim
        · exact congrArg Sum.inr (Subtype.ext h)
      simpa [m] using Fintype.card_le_of_injective embed injective
    -- The remaining leaves partition edge rows against independent neighbourhood rows.
    let X' (i : Fin m) (a b : Fin n) := X (e i).val (row a b)
    let Y' (i : Fin m) (a b : Fin n) := Y (e i).val (col a b)
    let label (i : Fin m) := lab (e i).val
    have partition : ∀ a b v w, H.Adj a b → (v = w ∨ H.Adj v w) →
        (∃! i, X' i a b ∧ Y' i v w) ∧
        (∀ i, X' i a b → Y' i v w → (label i = a ∨ label i = b) ∧
          ¬ ((H.Adj v (label i) ∨ H.Adj w (label i)) ∧ label i ≠ v ∧ label i ≠ w)) := by
      intro a b v w hab hvw
      obtain ⟨⟨j, ⟨jx,jy⟩, uniq⟩, sound⟩ := cert (row a b) (col v w) (rowOn a b hab) (colOff v w hvw)
      have labelInfo (i : Fin t.leaves) (ix : X i (row a b)) (iy : Y i (col v w)) :
          (lab i = a ∨ lab i = b) ∧
          ¬ ((H.Adj v (lab i) ∨ H.Adj w (lab i)) ∧ lab i ≠ v ∧ lab i ≠ w) := by
        obtain ⟨hp,hn⟩ := sound i ix iy
        exact ⟨of_decide_eq_true hp, of_decide_eq_false hn⟩
      have unmarkedJ : lab j ∉ A := by
        rcases (labelInfo j jx jy).1 with h | h
        · exact h ▸ disjoint a b hab
        · exact h ▸ disjoint b a hab.symm
      let raw : I := ⟨j, unmarkedJ⟩
      have reindex : (e (e.symm raw)).val = j := by simp [raw]
      constructor
      · refine ⟨e.symm raw, ⟨?_,?_⟩, ?_⟩
        · change X _ _
          simpa only [reindex] using jx
        · change Y _ _
          simpa only [reindex] using jy
        · intro i hi
          apply e.injective
          apply Subtype.ext
          rw [reindex]
          exact uniq (e i).val hi
      · exact fun i ix iy => labelInfo (e i).val ix iy
    obtain ⟨T, cover, lower⟩ := tableBound n m H X' Y' label partition
    exact ⟨T, cover, by omega⟩
  intro n k s G A z f degree girth isolated _hasEdge unmarked spec minCover size
  let H := G.deleteEdges (G.incidenceSet z)
  have sub : H ≤ G := fun _ _ h => (SimpleGraph.deleteIncidenceSet_adj.mp h).1
  have disjoint (a b : Fin n) (edge : H.Adj a b) : a ∉ A := isolated a b (sub edge)
  obtain ⟨C, mono, small, computes⟩ := toMono n s G A z f degree girth isolated unmarked spec size
  have onC : ∀ x, C.eval (List.ofFn x) = true ↔
      (∃ a ∈ A, x a = true) ∨ ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true := by
    intro x
    rw [computes]
    exact spec x
  obtain ⟨t, short, positive, evalT⟩ := toTree n G A z C degree girth isolated unmarked mono onC
  have yes (x : Fin n → Bool) : t.eval x = true ↔
      (∃ a ∈ A, x a = true) ∨ ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true := by
    rw [evalT]
    exact onC x
  have atLeastFive (v : Fin n) (p : G.Walk v v) (hc : p.IsCycle) : 5 ≤ p.length :=
    le_trans (by decide : 5 ≤ 7) (girth v p hc)
  obtain ⟨T, cover, bound⟩ := formulaLower n G H sub atLeastFive A disjoint t positive yes
  have hT := minCover T cover
  change A.card + H.edgeSet.ncard + k ≤ s + 1
  omega
