import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5322

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

abbrev Test (n : ℕ) := (Fin n → Bool) → Prop
abbrev Term (n : ℕ) := Test n × Test n

def binary (b : Bool) (u v : ℕ) : Gate :=
  ⟨if b then .and else .or, [u, v]⟩

def combine {n} (b : Bool) (p q : Test n) : Test n :=
  fun x => if b then p x ∧ q x else p x ∨ q x

def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (n : ℕ) (gs : List Gate) (i : ℕ) : Test n :=
  fun x => ((gs.foldl step (List.ofFn x)).getD i false) = true

lemma length_fold (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl, ih, step]; omega

lemma old_wire {n gs i} (hi : i < n + gs.length) (g : Gate) :
    W n (gs ++ [g]) i = W n gs i := by
  funext x
  have hl := length_fold gs (List.ofFn x)
  simp only [List.length_ofFn] at hl
  simp [W, List.foldl_append, step, List.getD, List.getElem?_append_left (hl ▸ hi : i < (gs.foldl step (List.ofFn x)).length)]

lemma new_wire (n) (gs : List Gate) (b u v) :
    W n (gs ++ [binary b u v]) (n + gs.length) =
      combine b (W n gs u) (W n gs v) := by
  funext x
  have hl := length_fold gs (List.ofFn x)
  simp only [List.length_ofFn] at hl
  cases b <;> simp [W, List.foldl_append, step, binary, GateOp.eval, combine,
    ← hl, List.getD]

def Layout (n : ℕ) (gs : List Gate) : Prop :=
  ∀ i (hi : i < gs.length), ∃ b u v, gs[i] = binary b u v ∧ u < n+i ∧ v < n+i

lemma layout_of {n} {C : Circuit} (h : IsAO2 n C) : Layout n C.gates := by
  intro i hi
  have hm := List.getElem_mem (l := C.gates) hi
  obtain ⟨u,v, huv⟩ := List.length_eq_two.mp (h.2.2 _ hm)
  have hat : gateAt C i = C.gates[i] := by simp [gateAt, List.getD, hi]
  have hr := h.2.1 i hi
  rw [hat, huv] at hr
  obtain ho | ho := h.1 _ hm
  · exact ⟨true,u,v, by cases hg : C.gates[i] with | mk o l => simp_all [binary],
      hr u (by simp), hr v (by simp)⟩
  · exact ⟨false,u,v, by cases hg : C.gates[i] with | mk o l => simp_all [binary],
      hr u (by simp), hr v (by simp)⟩

lemma layout_ao {n gs} (h : Layout n gs) : IsAO2 n ⟨gs,0⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hg
    obtain ⟨b,u,v,he,-,-⟩ := h i hi
    rw [he]
    cases b <;> simp [binary]
  · intro i hi w hw
    change i < gs.length at hi
    obtain ⟨b,u,v,he,hu,hv⟩ := h i hi
    simp [gateAt, List.getD, hi, he, binary] at hw
    rcases hw with rfl | rfl <;> assumption
  · intro g hg
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hg
    obtain ⟨b,u,v,he,-,-⟩ := h i hi
    simp [he,binary]

def Dirty {n} (F p : Test n) : Prop := ∃ x, p x ∧ ¬ F x

def Clean {n} (F : Test n) (gs : List Gate) : Prop :=
  ∀ i (hi : i < gs.length), gs[i].op = .and → Dirty F (W n gs (n+i))

def Pool {n} (F : Test n) (R : Set (Test n)) (c : ℕ) : Prop :=
  ∃ gs : List Gate, gs.length ≤ c ∧ Layout n gs ∧ Clean F gs ∧
    ∀ p ∈ R, Dirty F p ∧ ∃ i < n + gs.length, W n gs i = p

lemma pool_append {n} {F : Test n} {R c} (h : Pool F R c) {p q}
    (hp : p ∈ R) (hq : q ∈ R) (b : Bool) (hd : Dirty F (combine b p q)) :
    Pool F (insert (combine b p q) R) (c+1) := by
  classical
  obtain ⟨gs,hc,hl,hcl,hr⟩ := h
  obtain ⟨u,hu,hpu⟩ := (hr p hp).2
  obtain ⟨v,hv,hqv⟩ := (hr q hq).2
  let g := binary b u v
  have hn : W n (gs ++ [g]) (n+gs.length) = combine b p q := by
    rw [new_wire, hpu, hqv]
  refine ⟨gs ++ [g], by simp; omega, ?_, ?_, ?_⟩
  · intro i hi
    by_cases hj : i < gs.length
    · simpa [List.getElem_append_left hj] using hl i hj
    · have : i = gs.length := by simp at hi; omega
      subst i
      exact ⟨b,u,v,by simp [g],hu,hv⟩
  · intro i hi ho
    by_cases hj : i < gs.length
    · rw [old_wire (by omega)]
      exact hcl i hj (by simpa [List.getElem_append_left hj] using ho)
    · have : i = gs.length := by simp at hi; omega
      subst i
      rwa [hn]
  · intro s hs
    rcases Set.mem_insert_iff.mp hs with rfl | hs
    · exact ⟨hd, n+gs.length, by simp, hn⟩
    · obtain ⟨hsd,i,hi,he⟩ := hr s hs
      exact ⟨hsd,i,by simp; omega,(old_wire hi g).trans he⟩

def Hit {n} (T : Finset (Term n)) (x : Fin n → Bool) : Prop :=
  ∃ t ∈ T, t.1 x ∧ t.2 x

def Covers {n} (T : Finset (Term n)) (f p : Test n) : Prop :=
  ∀ x, f x → Hit T x ∨ p x

-- Outside the pairs already in T, each original signal is covered by a
-- physical wire in R or by a pair in P. A physical wire also implies the
-- original signal, so a physical representative of the output is impossible.
def Repr {n} (R : Set (Test n)) (P T : Finset (Term n)) (f : Test n) : Prop :=
  (∃ p ∈ R, (∀ x, p x → f x) ∧ Covers T f p) ∨
  ∃ t ∈ P, Covers T f (fun x => t.1 x ∧ t.2 x)

def Sound {n} (F : Test n) (R : Set (Test n)) (P : Finset (Term n)) : Prop :=
  ∀ t ∈ P, t.1 ∈ R ∧ t.2 ∈ R ∧ ∀ x, t.1 x → t.2 x → F x

-- Each original gate can pay for one physical gate, one new pair in P,
-- or the promotion of one existing pair from P into T.
def Model {n} (F : Test n) (S : Set (Test n)) (k : ℕ) : Prop :=
  ∃ R P T c, Pool F R c ∧ Sound F R P ∧ T ⊆ P ∧
    c + P.card + T.card ≤ k ∧ ∀ f ∈ S, Repr R P T f

lemma hit_mono {n} {T U : Finset (Term n)} (h : T ⊆ U) {x} :
    Hit T x → Hit U x := fun ⟨t,ht,ha⟩ => ⟨t,h ht,ha⟩

lemma repr_mono {n} {R R' : Set (Test n)} {P P' T T' : Finset (Term n)} {f}
    (hr : R ⊆ R') (hp : P ⊆ P') (ht : T ⊆ T') (h : Repr R P T f) :
    Repr R' P' T' f := by
  have liftCov {a : Test n} (hc : Covers T f a) : Covers T' f a :=
    fun x hx => (hc x hx).imp (hit_mono ht) id
  rcases h with ⟨p,hm,hl,hc⟩ | ⟨t,hm,hc⟩
  · exact Or.inl ⟨p,hr hm,hl,liftCov hc⟩
  · exact Or.inr ⟨t,hp hm,liftCov hc⟩

lemma combine_comm {n} (b) (f g : Test n) :
    combine b f g = combine b g f := by
  funext x
  cases b <;> simp [combine, and_comm, or_comm]

lemma cov_combine {n} {T : Finset (Term n)} {f g p q} (b)
    (hp : Covers T f p) (hq : Covers T g q) :
    Covers T (combine b f g) (combine b p q) := by
  intro x hx
  by_cases hh : Hit T x
  · exact Or.inl hh
  · right
    have ha := fun h => (hp x h).resolve_left hh
    have hb := fun h => (hq x h).resolve_left hh
    cases b
    · exact hx.elim (fun h => Or.inl (ha h)) (fun h => Or.inr (hb h))
    · exact ⟨ha hx.1, hb hx.2⟩

lemma model_add {n} {F : Test n} {S k} (h : Model F S k)
    {f g} (hf : f ∈ S) (hg : g ∈ S) (b) :
    Model F (insert (combine b f g) S) (k+1) := by
  classical
  obtain ⟨R,P,T,c,pool,sound,sub,budget,reps⟩ := h
  have finish {s : Test n} {R' P' T' c'}
      (hr : R ⊆ R') (hp : P ⊆ P') (ht : T ⊆ T')
      (pl : Pool F R' c') (so : Sound F R' P') (su : T' ⊆ P')
      (bu : c'+P'.card+T'.card ≤ k+1) (rep : Repr R' P' T' s) :
      Model F (insert s S) (k+1) := by
    refine ⟨R',P',T',c',pl,so,su,bu,?_⟩
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact rep
    · exact repr_mono hr hp ht (reps a ha)
  -- An AND can pass the same pair onward. An OR adds it to T and passes
  -- the other operand onward, since this pair now covers its own inputs.
  have virtual {a d : Test n} {t} (ht : t ∈ P)
      (hc : Covers T a (fun x => t.1 x ∧ t.2 x)) (hd : Repr R P T d) :
      Model F (insert (combine b a d) S) (k+1) := by
    cases b
    · let U := insert t T
      have incl : T ⊆ U := Finset.subset_insert t T
      have cover {s : Test n} (cs : Covers T d s) : Covers U (combine false a d) s := by
        intro x hx
        rcases hx with ha | hd'
        · rcases hc x ha with hh | hh
          · exact Or.inl (hit_mono incl hh)
          · exact Or.inl ⟨t,Finset.mem_insert_self _ _,hh⟩
        · exact (cs x hd').imp (hit_mono incl) id
      apply finish (Set.Subset.rfl) (Finset.Subset.refl _) incl pool sound
        (Finset.insert_subset ht sub) (by have := Finset.card_insert_le t T; dsimp [U]; omega)
      rcases hd with ⟨q,hq,hlo,hcov⟩ | ⟨s,hs,hcov⟩
      · exact Or.inl ⟨q,hq,fun x hx => Or.inr (hlo x hx),cover hcov⟩
      · exact Or.inr ⟨s,hs,cover hcov⟩
    · exact finish (Set.Subset.rfl) (Finset.Subset.refl _) (Finset.Subset.refl _) pool sound sub (by omega)
        (Or.inr ⟨t,ht,fun x hx => hc x hx.1⟩)
  have rf := reps f hf
  have rg := reps g hg
  rcases rf with ⟨p,hp,lp,cp⟩ | ⟨t,ht,ct⟩
  · rcases rg with ⟨q,hq,lq,cq⟩ | ⟨t,ht,ct⟩
    · have cov := cov_combine b cp cq
      by_cases dirty : Dirty F (combine b p q)
      · have hr : R ⊆ insert (combine b p q) R := Set.subset_insert _ _
        refine finish hr (Finset.Subset.refl _) (Finset.Subset.refl _) (pool_append pool hp hq b dirty) ?_ sub (by omega) ?_
        · intro t ht
          obtain ⟨ha,hb,hf⟩ := sound t ht
          exact ⟨hr ha,hr hb,hf⟩
        · refine Or.inl ⟨combine b p q, Set.mem_insert _ _, ?_,cov⟩
          intro x hx
          cases b
          · exact hx.elim (fun h => Or.inl (lp x h)) (fun h => Or.inr (lq x h))
          · exact ⟨lp x hx.1,lq x hx.2⟩
      · cases b
        · obtain ⟨gs,-,-,-,hr⟩ := pool
          obtain ⟨x,hx,hn⟩ := (hr p hp).1
          exact (dirty ⟨x, Or.inl hx,hn⟩).elim
        · let t : Term n := (p,q)
          have incl := Finset.subset_insert t P
          refine finish (Set.Subset.rfl) incl (Finset.Subset.refl _) pool ?_ (sub.trans incl)
            (by have := Finset.card_insert_le t P; omega) ?_
          · intro s hs
            rcases Finset.mem_insert.mp hs with rfl | hs
            · refine ⟨hp,hq,?_⟩
              intro x hx hy
              by_contra hn
              exact dirty ⟨x,⟨hx,hy⟩,hn⟩
            · exact sound s hs
          · exact Or.inr ⟨t,Finset.mem_insert_self _ _,cov⟩
    · rw [combine_comm b f g]
      exact virtual ht ct (Or.inl ⟨p,hp,lp,cp⟩)
  · exact virtual ht ct rg

def Signals (n : ℕ) (gs : List Gate) : Set (Test n) :=
  {p | ∃ i < n + gs.length, W n gs i = p}

lemma simulate {n} (F : Test n) (inputs : ∀ i < n, Dirty F (W n [] i))
    (gs : List Gate) (hl : Layout n gs) : Model F (Signals n gs) gs.length := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨Signals n [], ∅, ∅, 0, ?_, by simp [Sound], by simp, by simp, ?_⟩
    · refine ⟨[],by simp,by simp [Layout],by simp [Clean],?_⟩
      intro p hp
      obtain ⟨i,hi,rfl⟩ := hp
      exact ⟨inputs i (by simpa using hi), i,hi,rfl⟩
    · intro p hp
      exact Or.inl ⟨p,hp,fun _ => id, fun _ hx => Or.inr hx⟩
  | append_singleton gs last ih =>
    have layout : Layout n gs := by
      intro i hi
      obtain ⟨b,u,v,he,hu,hv⟩ := hl i (by simp; omega)
      exact ⟨b,u,v, (List.getElem_append_left hi).symm.trans he,hu,hv⟩
    obtain ⟨b,u,v,he,hu,hv⟩ := hl gs.length (by simp)
    simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,
      List.getElem_cons_zero] at he
    subst last
    have h := model_add (ih layout) (f := W n gs u) (g := W n gs v)
      ⟨u,hu,rfl⟩ ⟨v,hv,rfl⟩ b
    obtain ⟨R,P,T,c,hp,hs,ht,hb,hr⟩ := h
    refine ⟨R,P,T,c,hp,hs,ht,by simpa using hb,?_⟩
    intro p hm
    obtain ⟨i,hi,rfl⟩ := hm
    by_cases hj : i < n + gs.length
    · rw [old_wire hj]
      exact hr _ (Set.mem_insert_of_mem _ ⟨i,hj,rfl⟩)
    · have : i = n+gs.length := by simp at hi; omega
      subst i
      rw [new_wire]
      exact hr _ (Set.mem_insert _ _)

lemma extract {n} (F : Test n) (inputs : ∀ i < n, Dirty F (W n [] i))
    (C : Circuit) (hl : IsAO2 n C) (hne : ∃ x, F x)
    (ho : W n C.gates C.output = F) :
    ∃ (gs : List Gate) (U : Finset (ℕ × ℕ)), Layout n gs ∧ Clean F gs ∧
      (∀ t ∈ U, ∀ x, W n gs t.1 x → W n gs t.2 x → F x) ∧
      (∀ x, F x → ∃ t ∈ U, W n gs t.1 x ∧ W n gs t.2 x) ∧
      gs.length + 2 * U.card ≤ C.size + 1 := by
  classical
  obtain ⟨R,P,T,c,pool,sound,sub,budget,reps⟩ :=
    simulate F inputs C.gates (layout_of hl)
  have hout : C.output < n+C.gates.length := by
    by_contra! h
    obtain ⟨x,hx⟩ := hne
    rw [← ho] at hx
    have hlen := length_fold C.gates (List.ofFn x)
    simp only [List.length_ofFn] at hlen
    simp [W, List.getD, List.getElem?_eq_none (hlen ▸ h :
        (C.gates.foldl step (List.ofFn x)).length ≤ C.output)] at hx
  obtain ⟨gs,hc,hg,hclean,real⟩ := pool
  have rep := reps F ⟨C.output,hout,ho⟩
  rcases rep with ⟨p,hp,hlo,-⟩ | ⟨t,ht,hcov⟩
  · obtain ⟨x,hx,hn⟩ := (real p hp).1
    exact (hn (hlo x hx)).elim
  -- Only the pair representing the output can need a final promotion.
  · let U := insert t T
    have hu : U ⊆ P := Finset.insert_subset ht sub
    have cu := Finset.card_le_card hu
    have ct : U.card ≤ T.card + 1 := Finset.card_insert_le t T
    let index (p : Test n) : ℕ := if hp : p ∈ R then ((real p hp).2).choose else 0
    have idx {p : Test n} (hp : p ∈ R) : W n gs (index p) = p := by
      simpa [index,hp] using ((real p hp).2).choose_spec.2
    let enc (s : Term n) := (index s.1, index s.2)
    refine ⟨gs,U.image enc,hg,hclean,?_,?_,?_⟩
    · intro v hv
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨ha,hb,hsafe⟩ := sound s (hu hs)
      simpa only [enc, idx ha, idx hb] using hsafe
    · intro x hx
      have hit : Hit U x := by
        rcases hcov x hx with hh | hh
        · exact hit_mono (Finset.subset_insert t T) hh
        · exact ⟨t, Finset.mem_insert_self _ _, hh⟩
      obtain ⟨s,hs,ha,hb⟩ := hit
      obtain ⟨hm,hn,-⟩ := sound s (hu hs)
      exact ⟨enc s,Finset.mem_image_of_mem enc hs, by simpa only [enc,idx hm] using ha,
        by simpa only [enc,idx hn] using hb⟩
    · have h := Finset.card_image_le (s := U) (f := enc)
      unfold Circuit.size
      omega

def Edge {n m} (E : Finset (Fin n × Fin m)) : Test (n+m) :=
  fun x => ∃ p l, (p,l) ∈ E ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true

lemma input_dirty {n m} (E : Finset (Fin n × Fin m)) (i : ℕ) (hi : i < n+m) :
    Dirty (Edge E) (W (n+m) [] i) := by
  let x (j : Fin (n+m)) := decide (j.val = i)
  refine ⟨x,by simp [W, List.getD, hi, x],?_⟩
  rintro ⟨p,l,-,hp,hh⟩
  simp [x] at hp hh
  have := p.isLt
  omega

end PEqualNP.Outside.L_meta_5322

open PEqualNP.Outside.L_meta_5322

theorem PEqualNP.Outside.L_meta_5322 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3.Nonempty → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : Finset (ℕ × ℕ)), PEqualNP.TopForm.IsAO2 (x1 + x2) x8 ∧ (∀ x10 < x8.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x8 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : Fin (x1 + x2) → Bool), (x8.wires (List.ofFn x13)).getD (x1 + x2 + x10) Bool.false = Bool.true ∧ ¬∃ (x14 : Fin x1) (x15 : Fin x2), (x14, x15) ∈ x3 ∧ x13 (Fin.castAdd x2 x14) = Bool.true ∧ x13 (Fin.natAdd x1 x15) = Bool.true) ∧ (∀ x10 ∈ x9, ∀ (x12 : Fin (x1 + x2) → Bool), (x8.wires (List.ofFn x12)).getD x10.1 Bool.false = Bool.true → (x8.wires (List.ofFn x12)).getD x10.2 Bool.false = Bool.true → ∃ (x15 : Fin x1) (x16 : Fin x2), (x15, x16) ∈ x3 ∧ x12 (Fin.castAdd x2 x15) = Bool.true ∧ x12 (Fin.natAdd x1 x16) = Bool.true) ∧ (∀ x10 ∈ x3, ∃ x12 ∈ x9, (x8.wires (List.ofFn fun (x13 : Fin (x1 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x10.1 ∨ x13 = Fin.natAdd x1 x10.2))).getD x12.1 Bool.false = Bool.true ∧ (x8.wires (List.ofFn fun (x13 : Fin (x1 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x10.1 ∨ x13 = Fin.natAdd x1 x10.2))).getD x12.2 Bool.false = Bool.true) ∧ x8.size + (2 : ℕ) * x9.card ≤ x4.size + (1 : ℕ) := by
  intro n m E C hE hC hfun
  have hn : ∃ x, Edge E x := by
    obtain ⟨⟨p,l⟩,hp⟩ := hE
    exact ⟨fun _ => true,p,l,hp,rfl,rfl⟩
  have ho : W (n+m) C.gates C.output = Edge E := by
    funext x
    change (PEqualNP.MetaComplexity.circuitFun (n+m) C x = true) = _
    rw [hfun]
    simp [Edge]
  obtain ⟨gs,U,hl,hclean,hs,hcov,hb⟩ := extract (Edge E) (input_dirty E) C hC hn ho
  refine ⟨⟨gs,0⟩,U,layout_ao hl,?_,hs,?_,hb⟩
  · intro j hj h
    apply hclean j hj
    simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD, hj] using h
  · intro e he
    apply hcov
    exact ⟨e.1,e.2,he,by simp,by simp⟩
