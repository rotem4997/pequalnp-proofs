import Mathlib
import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_8181_429
    (core : ∀ m n : ℕ,
      let G := fun (E : Finset (Fin m × Fin n)) => SimpleGraph.fromRel fun x y =>
        ∃ e ∈ E, x = Fin.castAdd n e.1 ∧ y = Fin.natAdd m e.2
      let ok := fun (E : Finset (Fin m × Fin n)) (C : Circuit) => IsAO2 (m+n) C ∧
        circuitFun (m+n) C = ReadTwo.fpl m (fun a b => (a,b) ∈ E)
      let leaf := fun (E : Finset (Fin m × Fin n)) (e : Fin m × Fin n) =>
        ((∀ f ∈ E, f.1 = e.1 → f = e) ∨ (∀ f ∈ E, f.2 = e.2 → f = e))
      let bad := fun (E : Finset (Fin m × Fin n)) => 6 ≤ E.card ∧ ∃ C : Circuit,
        let Q : Set (Fin m × Fin n) := {e | e ∈ E ∧ (leaf E e ∨ ∃ D : Circuit, D.size < C.size ∧ ok (E.erase e) D)}
        C.size + 3 ≤ 2 * E.card ∧ ok E C ∧ ReadTwo.Lin (fun a b => (a,b) ∈ E) ∧ ¬(G E).IsAcyclic ∧
          (∀ v : Fin (m+n), let d := ((G E).neighborSet v).ncard
            let R := readers 0 C v.val
            2 ≤ d → R.card ≤ d ∧ (d = R.card → ∀ j ∈ R, (gateAt C j).op = GateOp.and → readers (m+n) C j ⊆ R)) ∧
          Set.InjOn Prod.fst Q ∧ Set.InjOn Prod.snd Q
      ∀ E, (∀ e ∈ E, ¬leaf E e) → ¬bad E)
    (descent : ∀ m n : ℕ,
      let G := fun (E : Finset (Fin m × Fin n)) => SimpleGraph.fromRel fun x y =>
        ∃ e ∈ E, x = Fin.castAdd n e.1 ∧ y = Fin.natAdd m e.2
      let ok := fun (E : Finset (Fin m × Fin n)) (C : Circuit) => IsAO2 (m+n) C ∧
        circuitFun (m+n) C = ReadTwo.fpl m (fun a b => (a,b) ∈ E)
      let leaf := fun (E : Finset (Fin m × Fin n)) (e : Fin m × Fin n) =>
        ((∀ f ∈ E, f.1 = e.1 → f = e) ∨ (∀ f ∈ E, f.2 = e.2 → f = e))
      let bad := fun (E : Finset (Fin m × Fin n)) => 6 ≤ E.card ∧ ∃ C : Circuit,
        let Q : Set (Fin m × Fin n) := {e | e ∈ E ∧ (leaf E e ∨ ∃ D : Circuit, D.size < C.size ∧ ok (E.erase e) D)}
        C.size + 3 ≤ 2 * E.card ∧ ok E C ∧ ReadTwo.Lin (fun a b => (a,b) ∈ E) ∧ ¬(G E).IsAcyclic ∧
          (∀ v : Fin (m+n), let d := ((G E).neighborSet v).ncard
            let R := readers 0 C v.val
            2 ≤ d → R.card ≤ d ∧ (d = R.card → ∀ j ∈ R, (gateAt C j).op = GateOp.and → readers (m+n) C j ⊆ R)) ∧
          Set.InjOn Prod.fst Q ∧ Set.InjOn Prod.snd Q
      ∀ E, bad E → (∃ e ∈ E, leaf E e) → ∃ F ⊂ E, bad F) :
    (∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))),   have x7 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : Finset (Fin x1 × Fin x2)) (x8 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x8 ∧ ∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x8 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x7 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true);   have x8 : Prop :=     ∃ (x8 : Fin (x1 + x2)),       have x9 : ℕ := (x6.neighborSet x8).ncard;       have x10 : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) x5 ↑x8;       (2 : ℕ) ≤ x9 ∧ (x9 < x10.card ∨ x9 = x10.card ∧ ∃ x11 ∈ x10, (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.readers (x1 + x2) x5 x11 ⊆ x10);   (∀ (x9 x10 : Fin (x1 + x2)), x6.Adj x9 x10 ↔ ∃ x11 ∈ x3, x9 = Fin.castAdd x2 x11.1 ∧ x10 = Fin.natAdd x1 x11.2 ∨ x10 = Fin.castAdd x2 x11.1 ∧ x9 = Fin.natAdd x1 x11.2) → ¬x6.IsAcyclic → x7 x3 x5 → (∀ x12 ∈ x4, ∀ x14 ∈ x4, x12.1 = x14.1 → x12 = x14) → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.2 = x15.2 → x13 = x15) → x4 ⊆ x3 → (∀ (x15 x16 : Fin x1) (x17 x18 : Fin x2), x15 ≠ x16 → x17 ≠ x18 → ¬((x15, x17) ∈ x3 ∧ (x15, x18) ∈ x3 ∧ (x16, x17) ∈ x3 ∧ (x16, x18) ∈ x3)) → (∀ x16 ∈ x3, ((∀ x18 ∈ x3, x18.1 = x16.1 → x18 = x16) ∨ ∀ x18 ∈ x3, x18.2 = x16.2 → x18 = x16) → (x3.erase x16).Nonempty → x16 ∈ x4) → ¬x8 → ∃ x18 ∈ x3, x18 ∉ x4 ∧ ∃ (x19 : PEqualNP.CircuitLowerBounds.Circuit), x19.size < x5.size ∧ x7 (x3.erase x18) x19) := by
  classical
  intro m n E M C K realizes overflow adj cycle eval left right Msub square pendant quiet
  let G := fun (E : Finset (Fin m × Fin n)) => SimpleGraph.fromRel fun x y =>
    ∃ e ∈ E, x = Fin.castAdd n e.1 ∧ y = Fin.natAdd m e.2
  let ok := fun (E : Finset (Fin m × Fin n)) (C : Circuit) => IsAO2 (m+n) C ∧
    circuitFun (m+n) C = ReadTwo.fpl m (fun a b => (a,b) ∈ E)
  let leaf := fun (E : Finset (Fin m × Fin n)) (e : Fin m × Fin n) =>
    ((∀ f ∈ E, f.1 = e.1 → f = e) ∨ (∀ f ∈ E, f.2 = e.2 → f = e))
  let bad := fun (E : Finset (Fin m × Fin n)) => 6 ≤ E.card ∧ ∃ C : Circuit,
    let Q : Set (Fin m × Fin n) := {e | e ∈ E ∧ (leaf E e ∨ ∃ D : Circuit, D.size < C.size ∧ ok (E.erase e) D)}
    C.size + 3 ≤ 2 * E.card ∧ ok E C ∧ ReadTwo.Lin (fun a b => (a,b) ∈ E) ∧ ¬(G E).IsAcyclic ∧
      (∀ v : Fin (m+n), let d := ((G E).neighborSet v).ncard
        let R := readers 0 C v.val
        2 ≤ d → R.card ≤ d ∧ (d = R.card → ∀ j ∈ R, (gateAt C j).op = GateOp.and → readers (m+n) C j ⊆ R)) ∧
      Set.InjOn Prod.fst Q ∧ Set.InjOn Prod.snd Q
  have girth (n m : ℕ) (E : Finset (Fin n × Fin m)) (G : SimpleGraph (Fin (n+m)))
      (adj : ∀ u v, G.Adj u v ↔ ∃ e ∈ E,
        (u = Fin.castAdd m e.1 ∧ v = Fin.natAdd n e.2) ∨
        (v = Fin.castAdd m e.1 ∧ u = Fin.natAdd n e.2))
      (cyc : ¬G.IsAcyclic)
      (rect : ∀ a b i j, a ≠ b → i ≠ j → ¬ ((a,i) ∈ E ∧ (a,j) ∈ E ∧ (b,i) ∈ E ∧ (b,j) ∈ E)) :
      6 ≤ E.card := by
    classical
    have sep (a : Fin n) (b : Fin m) : Fin.castAdd m a ≠ Fin.natAdd n b := by
      intro eq
      have h := congrArg Fin.val eq
      change a.val = n + b.val at h
      omega
    have left (a b : Fin n) : ¬G.Adj (Fin.castAdd m a) (Fin.castAdd m b) := by
      rintro h
      obtain ⟨e, _, ⟨_, bad⟩ | ⟨_, bad⟩⟩ := (adj _ _).1 h <;> exact sep _ _ bad
    have right (a b : Fin m) : ¬G.Adj (Fin.natAdd n a) (Fin.natAdd n b) := by
      intro h
      obtain ⟨e, _, ⟨bad,_⟩ | ⟨bad,_⟩⟩ := (adj _ _).1 h <;> exact sep _ _ bad.symm
    have lr (a : Fin n) (b : Fin m) (h : G.Adj (Fin.castAdd m a) (Fin.natAdd n b)) : (a,b) ∈ E := by
      obtain ⟨⟨c,d⟩, he, ⟨ac,bd⟩ | ⟨bad,_⟩⟩ := (adj _ _).1 h
      · have : a = c := Fin.castAdd_inj.mp ac
        have : b = d := by simpa [Fin.ext_iff] using congrArg Fin.val bd
        subst c; subst d; exact he
      · exact (sep _ _ bad.symm).elim
    have square (v w x y : Fin (n+m)) (hv : v ≠ x) (hw : w ≠ y)
        (h1 : G.Adj v w) (h2 : G.Adj w x) (h3 : G.Adj x y) (h4 : G.Adj y v) : False := by
      cases v using Fin.addCases <;> cases w using Fin.addCases <;> cases x using Fin.addCases <;>
        cases y using Fin.addCases <;> first
        | exact (left _ _) h1 | exact (right _ _) h1 | exact (left _ _) h2 | exact (right _ _) h2
        | exact (left _ _) h3 | exact (right _ _) h3
        | exact rect _ _ _ _ (fun h => hv (congrArg _ h)) (fun h => hw (congrArg _ h))
            ⟨lr _ _ h1,lr _ _ h4.symm,lr _ _ h2.symm,lr _ _ h3⟩
        | exact rect _ _ _ _ (fun h => hw (congrArg _ h)) (fun h => hv (congrArg _ h))
            ⟨lr _ _ h1.symm,lr _ _ h2,lr _ _ h4,lr _ _ h3.symm⟩
    obtain ⟨v,w,hw⟩ := SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp cyc
    let col : G.Coloring Bool := SimpleGraph.Coloring.mk (fun u => decide (u.val < n)) (by
      intro i j hij
      obtain ⟨⟨a,b⟩, _, ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adj _ _).1 hij <;> simp)
    have ev := (col.even_length_iff_congr w).2 Iff.rfl
    have three := hw.three_le_length
    have six : 6 ≤ w.length := by
      by_contra! h
      obtain ⟨k,hk⟩ := ev
      have four : w.length = 4 := by omega
      have neq (a b : ℕ) (ha : a < 4) (hb : b < 4) (ne : a ≠ b) : w.getVert a ≠ w.getVert b :=
        fun eq => ne (hw.getVert_injOn' (by change a ≤ w.length-1; omega) (by change b ≤ w.length-1; omega) eq)
      apply square (w.getVert 0) (w.getVert 1) (w.getVert 2) (w.getVert 3)
        (neq _ _ (by decide) (by decide) (by decide)) (neq _ _ (by decide) (by decide) (by decide))
        (w.adj_getVert_succ (by omega)) (w.adj_getVert_succ (by omega)) (w.adj_getVert_succ (by omega))
      simpa [←four, SimpleGraph.Walk.getVert_length] using (w.adj_getVert_succ (i:=3) (by omega))
    let edge := fun e : Fin n × Fin m => s(Fin.castAdd m e.1, Fin.natAdd n e.2)
    have sub : G.edgeSet ⊆ ↑(E.image edge) := by
      intro z hz
      induction z using Sym2.inductionOn with
      | _ i j =>
        obtain ⟨e, he, ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adj i j).1 hz
        · exact Finset.mem_image_of_mem edge he
        · rw [Sym2.eq_swap]; exact Finset.mem_image_of_mem edge he
    exact six.trans (hw.isTrail.length_le_ncard_edgeSet.trans
      ((Set.ncard_le_ncard sub).trans (by simpa only [Set.ncard_coe_finset] using Finset.card_image_le (s:=E) (f:=edge))))
  have six := girth m n E K adj cycle square
  have hK : K = G E := by
    apply SimpleGraph.ext
    funext a b
    apply propext
    rw [adj]
    constructor
    · rintro ⟨e,he,h | h⟩
      · exact ⟨((adj a b).2 ⟨e,he,Or.inl h⟩).ne, Or.inl ⟨e,he,h⟩⟩
      · exact ⟨((adj a b).2 ⟨e,he,Or.inr h⟩).ne, Or.inr ⟨e,he,h⟩⟩
    · rintro ⟨_,⟨e,he,h⟩ | ⟨e,he,h⟩⟩
      · exact ⟨e,he,Or.inl h⟩
      · exact ⟨e,he,Or.inr h⟩
  have imposs (A : Finset (Fin m × Fin n)) : ¬bad A := by
    induction A using Finset.strongInductionOn
    rename_i A ih
    intro hA
    by_cases leaves : ∃ e ∈ A, leaf A e
    · obtain ⟨F,ss,hF⟩ := descent m n A hA leaves
      exact ih F ss hF
    · exact core m n A (fun e he hleaf => leaves ⟨e,he,hleaf⟩) hA
  have unmatched (n m : ℕ) (E M : Finset (Fin n × Fin m)) (G : SimpleGraph (Fin (n+m)))
      (adj : ∀ u v, G.Adj u v ↔ ∃ e ∈ E,
        (u = Fin.castAdd m e.1 ∧ v = Fin.natAdd n e.2) ∨
        (v = Fin.castAdd m e.1 ∧ u = Fin.natAdd n e.2))
      (cyc : ¬G.IsAcyclic)
      (ml : ∀ a ∈ M, ∀ b ∈ M, a.1 = b.1 → a = b)
      (mr : ∀ a ∈ M, ∀ b ∈ M, a.2 = b.2 → a = b) : ∃ e ∈ E, e ∉ M := by
    classical
    by_contra! allM
    have sep (a : Fin n) (b : Fin m) : Fin.castAdd m a ≠ Fin.natAdd n b := by
      intro eq
      have h := congrArg Fin.val eq
      change a.val = n + b.val at h
      omega
    have unique (v u w : Fin (n+m)) (hu : G.Adj v u) (hw : G.Adj v w) : u = w := by
      obtain ⟨e, he, ⟨ve,ue⟩ | ⟨ue,ve⟩⟩ := (adj _ _).mp hu <;>
        obtain ⟨f, hf, ⟨vf,wf⟩ | ⟨wf,vf⟩⟩ := (adj _ _).mp hw
      · have ef := ml e (allM e he) f (allM f hf) (Fin.castAdd_inj.mp (ve.symm.trans vf))
        simp [ue,wf,ef]
      · exact (sep _ _ (ve.symm.trans vf)).elim
      · exact (sep _ _ (vf.symm.trans ve)).elim
      · have eq := congrArg Fin.val (ve.symm.trans vf)
        have ef := mr e (allM e he) f (allM f hf) (by simpa [Fin.ext_iff] using eq)
        simp [ue,wf,ef]
    obtain ⟨v,w,hw⟩ := SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp cyc
    have h3 := hw.three_le_length
    have eq := unique (w.getVert 1) (w.getVert 0) (w.getVert 2)
      (w.adj_getVert_succ (i:=0) (by omega)).symm (w.adj_getVert_succ (i:=1) (by omega))
    have bad := hw.getVert_injOn' (x₁:=0) (x₂:=2) (by change 0 ≤ w.length-1; omega)
      (by change 2 ≤ w.length-1; omega) eq
    contradiction
  have synth : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)), E.Nonempty →
        ∃ D : Circuit, D.size + 1 = 2 * E.card ∧ IsAO2 (n+m) D ∧
          ∀ x : Fin (n+m) → Bool, circuitFun (n+m) D x = decide
            (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd m a) = true ∧ x (Fin.natAdd n b) = true) := by
    classical
    let wf (gs : List Gate) (w : List Bool) : List Bool :=
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
    have wf_length (gs : List Gate) (w : List Bool) : (wf gs w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp [wf]
      | cons g gs ih =>
        have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        simp only [wf, List.foldl_cons] at this ⊢
        rw [this]
        simp
        omega
    have wf_append (gs hs : List Gate) (w : List Bool) : wf (gs ++ hs) w = wf hs (wf gs w) := by
      simp [wf, List.foldl_append]
    have wf_getD_lt (hs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (wf hs w).getD i false = w.getD i false := by
      induction hs generalizing w with
      | nil => rfl
      | cons g hs ih =>
        have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (by simp; omega)
        simp only [wf, List.foldl_cons] at this ⊢
        rw [this, List.getD_append _ _ _ _ hi]
    let val (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
      (wf gs (List.ofFn x)).getD w false
    let inp {n : ℕ} (x : Fin n → Bool) (i : ℕ) : Bool := (List.ofFn x).getD i false
    have val_old (n : ℕ) (gs hs : List Gate) (x : Fin n → Bool) (w : ℕ) (hw : w < n + gs.length) :
        val n (gs ++ hs) x w = val n gs x w := by
      unfold val
      rw [wf_append]
      exact wf_getD_lt _ _ _ (by rw [wf_length]; simpa using hw)
    have val_new (n : ℕ) (gs : List Gate) (op : GateOp) (a b : ℕ) (x : Fin n → Bool) :
        val n (gs ++ [⟨op, [a, b]⟩]) x (n + gs.length) = op.eval [val n gs x a, val n gs x b] := by
      unfold val
      rw [wf_append]
      have hl : (wf gs (List.ofFn x)).length = n + gs.length := by rw [wf_length]; simp
      have e : wf [⟨op, [a, b]⟩] (wf gs (List.ofFn x)) = wf gs (List.ofFn x) ++
          [op.eval [(wf gs (List.ofFn x)).getD a false, (wf gs (List.ofFn x)).getD b false]] := rfl
      rw [e, ← hl, List.getD_append_right _ _ _ _ le_rfl]
      simp
    have val_lt (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
        val n gs x i = inp x i := by
      unfold val inp
      exact wf_getD_lt _ _ _ (by simpa using hi)
    have inp_of_lt {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) : inp x i = x ⟨i, hi⟩ := by
      unfold inp
      simp [List.getD_eq_getElem?_getD, hi]
    let OK (n : ℕ) (gs : List Gate) : Prop :=
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j
    have ok_snoc {n : ℕ} {gs : List Gate} (h : OK n gs) (op : GateOp)
        (hop : op = GateOp.and ∨ op = GateOp.or) (a b : ℕ) (ha : a < n + gs.length)
        (hb : b < n + gs.length) : OK n (gs ++ [⟨op, [a, b]⟩]) := by
      refine ⟨?_, ?_⟩
      · intro g hg
        rcases List.mem_append.1 hg with hg | hg
        · exact h.1 g hg
        · simp only [List.mem_singleton] at hg
          subst hg
          exact ⟨hop, rfl⟩
      · intro j hj i hi
        rw [List.length_append, List.length_singleton] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · rw [List.getD_append _ _ _ _ hj] at hi
          exact h.2 j hj i hi
        · subst hj
          rw [List.getD_append_right _ _ _ _ le_rfl] at hi
          simp only [Nat.sub_self, List.getD_cons_zero, List.mem_cons, List.not_mem_nil,
            or_false] at hi
          rcases hi with rfl | rfl <;> assumption

    have andTwo (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by cases a <;> cases b <;> rfl
    have orTwo (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl
    intro n m E hE
    let N := n+m
    let F := fun (T : Finset (Fin n × Fin m)) (x : Fin N → Bool) =>
      ∃ e ∈ T, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true
    have work (T : Finset (Fin n × Fin m)) : T.Nonempty →
        ∃ (L : List Gate) (w : ℕ), OK N L ∧ w < N + L.length ∧
          L.length + 1 = 2*T.card ∧ ∀ x, val N L x w = true ↔ F T x := by
      induction T using Finset.induction_on with
      | empty => simp
      | @insert e T hn ih =>
        intro _
        let i := (Fin.castAdd m e.1).val
        let j := (Fin.natAdd n e.2).val
        have hi : i < N := (Fin.castAdd m e.1).isLt
        have hj : j < N := (Fin.natAdd n e.2).isLt
        let g : Gate := ⟨GateOp.and,[i,j]⟩
        have fresh (L : List Gate) (x : Fin N → Bool) :
            val N (L++[g]) x (N+L.length) =
              (x (Fin.castAdd m e.1) && x (Fin.natAdd n e.2)) := by
          rw [val_new, andTwo, val_lt _ _ _ _ hi, val_lt _ _ _ _ hj,
            inp_of_lt _ _ hi, inp_of_lt _ _ hj]
        by_cases non : T.Nonempty
        · obtain ⟨L,w,ok,hw,sz,eval⟩ := ih non
          let K := L ++ [g]
          let h : Gate := ⟨GateOp.or,[w,N+L.length]⟩
          have okK : OK N K := ok_snoc ok GateOp.and (Or.inl rfl) i j (by omega) (by omega)
          have lenK : K.length = L.length+1 := by simp [K]
          refine ⟨K++[h], N+K.length, ok_snoc okK GateOp.or (Or.inr rfl) _ _ (by omega) (by omega),
            by simp, ?_, ?_⟩
          · simp only [List.length_append,List.length_singleton,Finset.card_insert_of_notMem hn]
            omega
          · intro x
            rw [val_new,orTwo, show val N K x w = val N L x w from val_old _ _ _ _ _ hw,
              show val N K x (N+L.length) = _ from fresh L x]
            rw [Bool.or_eq_true,eval, Bool.and_eq_true]
            change (_ ∨ _) ↔ ∃ u ∈ insert e T, _
            constructor
            · rintro (⟨u,hu,hx⟩|h)
              · exact ⟨u,Finset.mem_insert_of_mem hu,hx⟩
              · exact ⟨e,Finset.mem_insert_self _ _,h⟩
            · rintro ⟨u,hu,hx⟩
              rcases Finset.mem_insert.mp hu with rfl|hu
              · exact Or.inr hx
              · exact Or.inl ⟨u,hu,hx⟩
        · have ht := Finset.not_nonempty_iff_eq_empty.mp non
          subst T
          have okNil : OK N [] := by simp [OK]
          refine ⟨[g],N,ok_snoc okNil GateOp.and (Or.inl rfl) _ _ (by simpa using hi)
            (by simpa using hj),by simp,by simp,?_⟩
          intro x
          have eq : val N [g] x N = _ := fresh [] x
          rw [eq,Bool.and_eq_true]
          change _ ↔ ∃ u ∈ insert e ∅, _
          constructor
          · exact fun h => ⟨e,Finset.mem_insert_self _ _,h⟩
          · rintro ⟨u,hu,h⟩
            have he : u=e := by simpa using hu
            exact he ▸ h
    obtain ⟨L,w,ok,_,size,eval⟩ := work E hE
    refine ⟨⟨L,w⟩,size,⟨fun g hg => (ok.1 g hg).1,ok.2,fun g hg => (ok.1 g hg).2⟩,?_⟩
    intro x
    change val N L x w = _
    apply Bool.eq_iff_iff.mpr
    rw [eval]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨⟨a,b⟩,h,ha,hb⟩; exact ⟨a,b,h,ha,hb⟩
    · rintro ⟨a,b,h,ha,hb⟩; exact ⟨⟨a,b⟩,h,ha,hb⟩
  by_contra noDrop
  have small : C.size + 3 ≤ 2 * E.card := by
    by_contra! large
    obtain ⟨e,he,hm⟩ := unmatched m n E M K adj cycle left right
    have er := Finset.card_erase_of_mem he
    have pos : (E.erase e).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨D,sz,hd,ev⟩ := synth m n (E.erase e) pos
    exact noDrop ⟨e,he,hm,D,by omega,hd,ev⟩
  have inside (e : Fin m × Fin n) (he : e ∈ E)
      (hr : leaf E e ∨ ∃ D : Circuit, D.size < C.size ∧ ok (E.erase e) D) : e ∈ M := by
    rcases hr with hl | ⟨D,cost,works⟩
    · apply pendant e he hl
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem he]
      omega
    · by_contra notIn
      exact noDrop ⟨e,he,notIn,D,cost,works.1,fun x => congrFun works.2 x⟩
  apply imposs E
  refine ⟨six, C, small, ⟨eval.1,funext eval.2⟩, ?_, hK ▸ cycle, ?_, ?_, ?_⟩
  · intro a b i j ab ij rect
    exact square a b i j ab ij ⟨rect.1,rect.2.2.1,rect.2.1,rect.2.2.2⟩
  · intro v
    dsimp only
    rw [←hK]
    intro two
    constructor
    · exact le_of_not_gt fun gt => quiet ⟨v,two,Or.inl gt⟩
    · intro tight j hj hand
      by_contra no
      exact quiet ⟨v,two,Or.inr ⟨tight,j,hj,hand,no⟩⟩
  · intro a ha b hb eq
    exact left a (inside a ha.1 ha.2) b (inside b hb.1 hb.2) eq
  · intro a ha b hb eq
    exact right a (inside a ha.1 ha.2) b (inside b hb.1 hb.2) eq
