import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_1770_417
    (semantics :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), IsAO2 n C →
      let f := fun (g : ℕ) (S : Finset (Fin n)) => gateVal n C g (fun v => decide (v∈S))=true
      (∀ g<C.gates.length,∀ A B, A⊆B → f g A → f g B) ∧
      (∀ w g,OrReaches n C w g → g<C.gates.length) ∧
      ∀ a∈tops G C,∀ g h, OrReaches n C (opnd C a 0) g → OrReaches n C (opnd C a 1) h →
      ∀ S, f g S → f h S → ∃ u∈S,∃ v∈S,G.Adj u v)
    (cleanCenters :
      ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      let V := fun (g : ℕ) (u v : Fin n) => gateVal n C g (pairInput u v)=true
      let B := fun (g : ℕ) (c : Fin n) => ∃ S : Finset (Fin n), S.card≤2 ∧ c∉S ∧ (∀ a∈S,∀ b∈S,¬G.Adj a b) ∧ gateVal n C g (fun i => decide (i∈S))=true
      let O := fun (g h : ℕ) => ∃ a∈tops G C, OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h
      (∀ a (w : G.Walk a a), w.IsCycle → 5≤w.length) → IsLeastAO G C → PEqualNP.TopForm.TopForm G C → ∀ E : Finset (Sym2 (Fin n)), E⊆Ustar G C → (∀ e∈E, ∃ (u v : Fin n) (g h : ℕ), e=s(u,v) ∧ g∈junk G C ∧ h∈junk G C ∧ g≠h ∧ O g h ∧ V g u u ∧ V h v v ∧ (¬B g u ∨ ¬B h v)) → E.card ≤ k*(C.size+1))
    (unmatched :
      ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      let V := fun (g : ℕ) (u v : Fin n) => gateVal n C g (pairInput u v)=true
      let O := fun (g h : ℕ) => ∃ a∈tops G C, OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h
      (∀ a (w : G.Walk a a), w.IsCycle → 5≤w.length) → IsLeastAO G C → PEqualNP.TopForm.TopForm G C → ∀ E : Finset (Sym2 (Fin n)), E⊆Ustar G C → (∀ e∈E, ∃ (u v : Fin n) (g h : ℕ), e=s(u,v) ∧ g∈junk G C ∧ h∈junk G C ∧ g≠h ∧ O g h ∧ V g u v ∧ V h u v ∧ ¬(V g u u ∧ V h v v) ∧ ¬(V g v v ∧ V h u u)) → E.card ≤ k*(C.size+1))
    : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | (¬∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ (x13 : Fin (2 : ℕ)), ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x10 ∈ PEqualNP.TopForm.side x5 x12 x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true) ∧ ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ x13 ∈ PEqualNP.TopForm.junk x3 x5, ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x13 ≠ x14 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 (0 : Fin (2 : ℕ))) x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 (1 : Fin (2 : ℕ))) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x13 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  classical
  let input {V : Type} [DecidableEq V] (S : Finset V) : V → Bool := fun v => decide (v∈S)
  let hit {V : Type} (G : SimpleGraph V) (S : Finset V) := ∃ u∈S,∃ v∈S,G.Adj u v
  have singleton_cross {V : Type} [DecidableEq V] (G : SimpleGraph V) (f h : Finset V → Prop)
      (mf : ∀ A B, A⊆B → f A → f B) (mh : ∀ A B,A⊆B → h A → h B)
      (clean : ∀ S, f S → h S → hit G S) (x y : V) (fx : f {x}) (hy : h {y}) : G.Adj x y := by
    have fxy := mf {x} {x,y} (by simp) fx
    have hxy := mh {y} {x,y} (by simp) hy
    obtain ⟨i,hi,j,hj,e⟩ := clean {x,y} fxy hxy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi hj
    rcases hi with rfl|rfl <;> rcases hj with rfl|rfl
    · exact False.elim (e.ne rfl)
    · exact e
    · exact e.symm
    · exact False.elim (e.ne rfl)
  have singleton_star {V : Type} [DecidableEq V] (G : SimpleGraph V) (f h : Finset V → Prop)
      (mf : ∀ A B,A⊆B → f A → f B) (mh : ∀ A B,A⊆B → h A → h B)
      (clean : ∀ S, f S → h S → hit G S)
      (square : ∀ a b c d, a≠c → b≠d → G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False) :
      (∀ a c, f {a} → f {c} → a=c) ∨ (∀ b d,h {b} → h {d} → b=d) := by
    by_cases left : ∀ a c, f {a} → f {c} → a=c
    · exact Or.inl left
    right
    push Not at left
    obtain ⟨a,c,ha,hc,ac⟩ := left
    intro b d hb hd
    by_contra bd
    have edge := singleton_cross G f h mf mh clean
    exact square a b c d ac bd (edge a b ha hb) (edge c b hc hb).symm (edge c d hc hd) (edge a d ha hd).symm
  have witness_neighbor {V : Type} [DecidableEq V] (G : SimpleGraph V) {S : Finset V} {t : V}
      (indep : ¬hit G S) (h : hit G (insert t S)) : ∃ v∈S, G.Adj v t := by
    obtain ⟨a,ha,b,hb,e⟩ := h
    rcases Finset.mem_insert.mp ha with at'|as'
    · rcases Finset.mem_insert.mp hb with bt'|bs'
      · exact False.elim (e.ne (at'.trans bt'.symm))
      · exact ⟨b,bs',at' ▸ e.symm⟩
    · rcases Finset.mem_insert.mp hb with bt'|bs'
      · exact ⟨a,as',bt' ▸ e⟩
      · exact False.elim (indep ⟨a,as',b,bs',e⟩)
  have shared_leaves_bound {V : Type} [DecidableEq V] (G : SimpleGraph V) (c : V) (S T : Finset V)
      (f : Finset V → Prop) (mf : ∀ A B,A⊆B → f A → f B)
      (fc : f {c}) (fs : f S) (indep : ¬hit G S) (avoid : c∉S)
      (partners : ∀ t∈T, ∃ h : Finset V → Prop,
        (∀ A B,A⊆B → h A → h B) ∧ (∀ X,f X → h X → hit G X) ∧ h {t})
      (square : ∀ a b c d, a≠c → b≠d → G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False) :
      T.card ≤ S.card := by
    classical
    let L := fun v => T.filter fun t => G.Adj v t
    have center : ∀ t∈T,G.Adj c t := by
      intro t ht
      obtain ⟨h,mh,clean,ht'⟩ := partners t ht
      exact singleton_cross G f h mf mh clean c t fc ht'
    have cover : T ⊆ S.biUnion L := by
      intro t ht
      obtain ⟨h,mh,clean,ht'⟩ := partners t ht
      have joined := clean (insert t S) (mf _ _ (Finset.subset_insert _ _) fs)
        (mh {t} _ (by simp) ht')
      obtain ⟨v,hv,adj⟩ := witness_neighbor G indep joined
      exact Finset.mem_biUnion.mpr ⟨v,hv,Finset.mem_filter.mpr ⟨ht,adj⟩⟩
    have small : ∀ v∈S,(L v).card ≤ 1 := by
      intro v hv
      apply Finset.card_le_one.mpr
      intro p hp q hq
      obtain ⟨pt,ep⟩ := Finset.mem_filter.mp hp
      obtain ⟨qt,eq'⟩ := Finset.mem_filter.mp hq
      by_contra pq
      exact square c p v q (fun he => avoid (he ▸ hv)) pq
        (center p pt) ep.symm eq' (center q qt).symm
    calc T.card ≤ (S.biUnion L).card := Finset.card_le_card cover
         _ ≤ S.card * 1 := Finset.card_biUnion_le_card_mul S L 1 small
         _ = S.card := Nat.mul_one _
  let fires {n : ℕ} (C : Circuit) (i : ℕ) (S : Finset (Fin n)) : Prop :=
    gateVal n C i (input S) = true
  have fires_mono {n : ℕ} {C : Circuit} (ao : IsAO2 n C) {i : ℕ} (hi : i<C.gates.length)
      (A B : Finset (Fin n)) (sub : A⊆B) : fires C i A → fires C i B :=
    (semantics n ⊥ C ao).1 i hi A B sub
  have top_clean {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
      (ao : IsAO2 n C) {a g h : ℕ} (top : a∈tops G C)
      (l : OrReaches n C (opnd C a 0) g) (r : OrReaches n C (opnd C a 1) h)
      (S : Finset (Fin n)) (fg : fires C g S) (fh : fires C h S) : hit G S :=
    (semantics n G C ao).2.2 a top g h l r S fg fh
  let Partner {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (g : ℕ) (t : Fin n) := ∃ a∈tops G C, ∃ h, ∃ b : Fin 2,
        OrReaches n C (opnd C a b) g ∧ OrReaches n C (opnd C a (1-b)) h ∧ fires C h {t}
  have partner_predicate {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
      (ao : IsAO2 n C) {g : ℕ} {t : Fin n} (pt : Partner G C g t) :
      ∃ h : Finset (Fin n) → Prop, (∀ A B,A⊆B → h A → h B) ∧
          (∀ X,fires C g X → h X → hit G X) ∧ h {t} := by
    obtain ⟨a,top,h,b,l,r,fh⟩ := pt
    refine ⟨fires C h,fires_mono ao ((semantics n G C ao).2.1 _ h r),?_,fh⟩
    fin_cases b
    · simp only [Fin.zero_eta, sub_zero] at l r
      exact top_clean ao top l r
    · simp only [Fin.mk_one,sub_self] at l r
      intro X fg fh'
      exact top_clean ao top r l X fh' fg
  let CenterCert {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (K g : ℕ) (c : Fin n) :=
    fires C g {c} ∧ (∀ d : Fin n,fires C g {d} → d=c) ∧
      ∃ S : Finset (Fin n), fires C g S ∧ ¬hit G S ∧ c∉S ∧ S.card≤K
  let CertifiedEdge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (K : ℕ) (e : Sym2 (Fin n)) :=
    ∃ g<C.gates.length, ∃ c t, e=s(c,t) ∧ CenterCert G C K g c ∧ Partner G C g t
  have certified_edge_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (ao : IsAO2 n C) (K : ℕ) (E : Finset (Sym2 (Fin n))) (eligible : ∀ e∈E, CertifiedEdge G C K e)
      (square : ∀ a b c d, a≠c → b≠d → G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False) :
      E.card ≤ C.size * K := by
    classical
    let cells := fun g => E.filter fun e => ∃ c t, e=s(c,t) ∧ CenterCert G C K g c ∧ Partner G C g t
    have cover : E ⊆ (Finset.range C.gates.length).biUnion cells := by
      intro e he
      obtain ⟨g,hg,hit⟩ := eligible e he
      exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_range.mpr hg,Finset.mem_filter.mpr ⟨he,hit⟩⟩
    apply (Finset.card_le_card cover).trans
    change _ ≤ C.gates.length * K
    conv_rhs => rw [← Finset.card_range C.gates.length]
    apply Finset.card_biUnion_le_card_mul
    intro g hg
    by_cases hne : (cells g).Nonempty
    · obtain ⟨e,he⟩ := hne
      obtain ⟨_,c,t,_,⟨fc,unique,S,fs,ind,away,sz⟩,pt⟩ := Finset.mem_filter.mp he
      let leaves := Finset.univ.filter (Partner G C g)
      have bound : leaves.card ≤ S.card :=
        shared_leaves_bound G c S leaves _ (fires_mono ao (Finset.mem_range.mp hg)) fc fs ind away
          (fun t ht => partner_predicate ao (Finset.mem_filter.mp ht).2) square
      have inc : cells g ⊆ leaves.image (fun v => s(c,v)) := by
        intro e he
        obtain ⟨_,d,v,eqn,cc,hv⟩ := Finset.mem_filter.mp he
        obtain rfl := unique d cc.1
        exact Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,eqn.symm⟩
      exact (Finset.card_le_card inc).trans (Finset.card_image_le.trans (bound.trans sz))
    · simp [Finset.not_nonempty_iff_eq_empty.mp hne]
  have girth_no_square {n : ℕ} (G : SimpleGraph (Fin n))
      (girth : ∀ a (w : G.Walk a a), w.IsCycle → 5≤w.length) :
      ∀ a b c d, a≠c → b≠d → G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False := by
    intro a b c d hac hbd hab hbc hcd hda
    let W : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
    have cycle : W.IsCycle := by
      refine SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, by simp [W]⟩
      simp only [W, SimpleGraph.Walk.tail_cons]
      simp [hab.ne.symm,hbc.ne,hcd.ne,hda.ne,hac.symm,hbd]
    have := girth a W cycle
    have len : W.length=4 := rfl
    omega
  let LocallyCleanAway {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (K g : ℕ) (c : Fin n) :=
    ∀ S : Finset (Fin n), S.card≤K → c∉S → fires C g S → hit G S
  have center_or_clean {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (K g : ℕ) (c : Fin n)
      (fc : fires C g {c}) (uniq : ∀ d : Fin n,fires C g {d} → d=c) :
      CenterCert G C K g c ∨ LocallyCleanAway G C K g c := by
    classical
    by_cases hc : LocallyCleanAway G C K g c
    · exact Or.inr hc
    unfold LocallyCleanAway at hc
    push Not at hc
    obtain ⟨S,sz,outside,fS,ind⟩ := hc
    exact Or.inl ⟨fc,uniq,S,fS,ind,outside,sz⟩
  have singleton_witness_residual {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
      {C : Circuit} (ao : IsAO2 n C) (girth : ∀ a (w : G.Walk a a), w.IsCycle → 5≤w.length)
      (K : ℕ) {a g h : ℕ} (top : a∈tops G C) (l : OrReaches n C (opnd C a 0) g)
      (r : OrReaches n C (opnd C a 1) h) (c t : Fin n) (fc : fires C g {c}) (ft : fires C h {t}) :
      CertifiedEdge G C K s(c,t) ∨ LocallyCleanAway G C K g c ∨ LocallyCleanAway G C K h t := by
    have hg := ((semantics n G C ao).2.1 _ g l)
    have hh := ((semantics n G C ao).2.1 _ h r)
    have single := singleton_star G _ _ (fires_mono ao hg) (fires_mono ao hh)
      (top_clean ao top l r) (girth_no_square G girth)
    rcases single with ug|uh
    · rcases center_or_clean G C K g c fc (fun d fd => ug d c fd fc) with cc|cl
      · left
        exact ⟨g,hg,c,t,rfl,cc,a,top,h,0,l,by simpa only [sub_zero] using r,ft⟩
      · exact Or.inr (Or.inl cl)
    · rcases center_or_clean G C K h t ft (fun d fd => uh d t fd ft) with cc|cl
      · left
        exact ⟨h,hh,t,c,Sym2.eq_swap,cc,a,top,g,1,r,by simpa only [sub_self] using l,fc⟩
      · exact Or.inr (Or.inr cl)
  have short : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    let V := fun (g : ℕ) (u v : Fin n) => gateVal n C g (pairInput u v)=true
    let B := fun (g : ℕ) (c : Fin n) => ∃ S : Finset (Fin n), S.card≤2 ∧ c∉S ∧ (∀ a∈S,∀ b∈S,¬G.Adj a b) ∧ gateVal n C g (fun i => decide (i∈S))=true
    let O := fun (g h : ℕ) => ∃ a∈tops G C, OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h
    (∀ a (w : G.Walk a a), w.IsCycle → 5≤w.length) → IsAO2 n C → ∀ E : Finset (Sym2 (Fin n)), (∀ e∈E, ∃ (u v : Fin n) (g h : ℕ), e=s(u,v) ∧ O g h ∧ V g u u ∧ V h v v ∧ B g u ∧ B h v) → E.card ≤ 2*C.size := by
    intro n G _ C
    dsimp only
    intro girth ao E eligible
    rw [Nat.mul_comm]
    apply certified_edge_bound G C ao 2 E _ (girth_no_square G girth)
    intro e he
    obtain ⟨u,v,g,h,ee,⟨a,ha,l,r⟩,fu,fv,bg,bh⟩ := eligible e he
    have conv (k : ℕ) (c : Fin n) (f : gateVal n C k (pairInput c c)=true) : fires C k {c} := by
      have eqn : input {c}=pairInput c c := by funext w; change decide (w∈({c} : Finset (Fin n))) = decide (w=c ∨ w=c); simp
      simpa only [fires,eqn] using f
    have obstruction (k : ℕ) (c : Fin n)
        (b : ∃ S : Finset (Fin n), S.card≤2 ∧ c∉S ∧ (∀ a∈S,∀ b∈S,¬G.Adj a b) ∧ gateVal n C k (fun i => decide (i∈S))=true) :
        ¬LocallyCleanAway G C 2 k c := by
      rintro clean
      obtain ⟨S,sz,nc,ind,fs⟩ := b
      obtain ⟨i,hi,j,hj,edge⟩ := clean S sz nc fs
      exact ind i hi j hj edge
    subst e
    exact (singleton_witness_residual ao girth 2 ha l r u v (conv _ _ fu) (conv _ _ fv)).resolve_right
      (fun dis => dis.elim (obstruction _ _ bg) (obstruction _ _ bh))

  obtain ⟨k,kh⟩ := cleanCenters
  obtain ⟨l,lh⟩ := unmatched
  refine ⟨2+k+l,?_⟩
  intro n G _ C girth least topform
  let V := fun (g : ℕ) (u v : Fin n) => gateVal n C g (pairInput u v)=true
  let B := fun (g : ℕ) (c : Fin n) => ∃ S : Finset (Fin n), S.card≤2 ∧ c∉S ∧ (∀ a∈S,∀ b∈S,¬G.Adj a b) ∧ gateVal n C g (fun i => decide (i∈S))=true
  let O := fun (g h : ℕ) => ∃ a∈tops G C, OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h
  let P := fun e : Sym2 (Fin n) => ∃ (u v : Fin n) (g h : ℕ), e=s(u,v) ∧ O g h ∧ V g u u ∧ V h v v ∧ B g u ∧ B h v
  let Q := fun e : Sym2 (Fin n) => ∃ (u v : Fin n) (g h : ℕ), e=s(u,v) ∧ g∈junk G C ∧ h∈junk G C ∧ g≠h ∧ O g h ∧ V g u u ∧ V h v v ∧ (¬B g u ∨ ¬B h v)
  let R := fun e : Sym2 (Fin n) => ∃ (u v : Fin n) (g h : ℕ), e=s(u,v) ∧ g∈junk G C ∧ h∈junk G C ∧ g≠h ∧ O g h ∧ V g u v ∧ V h u v ∧ ¬(V g u u ∧ V h v v) ∧ ¬(V g v v ∧ V h u u)
  let U := Ustar G C
  let A := U.filter P
  let D := U.filter Q
  let F := U.filter R
  have aa : A.card ≤ 2*C.size := short n G C girth least.1 A (fun _ he => (Finset.mem_filter.mp he).2)
  have dd : D.card ≤ k*(C.size+1) := kh n G C girth least topform D (Finset.filter_subset _ _) (fun _ he => (Finset.mem_filter.mp he).2)
  have ff : F.card ≤ l*(C.size+1) := lh n G C girth least topform F (Finset.filter_subset _ _) (fun _ he => (Finset.mem_filter.mp he).2)
  apply le_trans (Finset.card_le_card (t := (A∪D)∪F) ?_)
  · have h := Finset.card_union_le (A∪D) F
    have j := Finset.card_union_le A D
    rw [Nat.add_mul,Nat.add_mul]
    omega
  · intro e he
    obtain ⟨eu,_,u,v,ee,a,ha,g,hg,h,hh,ne,lg,rh,guv,huv⟩ := Finset.mem_filter.mp he
    have opp : O g h := ⟨a,ha,lg,rh⟩
    have useSing (s t : Fin n) (et : e=s(s,t)) (gs : V g s s) (ht : V h t t) :
        e∈(A∪D)∪F := by
      apply Finset.mem_union_left
      by_cases bg : B g s
      · by_cases bh : B h t
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨eu,s,t,g,h,et,opp,gs,ht,bg,bh⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨eu,s,t,g,h,et,hg,hh,ne,opp,gs,ht,Or.inr bh⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨eu,s,t,g,h,et,hg,hh,ne,opp,gs,ht,Or.inl bg⟩)
    by_cases st : V g u u ∧ V h v v
    · exact useSing u v ee st.1 st.2
    by_cases ts : V g v v ∧ V h u u
    · exact useSing v u (ee.trans Sym2.eq_swap) ts.1 ts.2
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨eu,u,v,g,h,ee,hg,hh,ne,opp,guv,huv,st,ts⟩)
