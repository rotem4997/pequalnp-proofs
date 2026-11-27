import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK
open scoped Classical

-- The wire-update lemma in the proof follows the checked L_meta_2804.
-- The dense-case bound may use any fixed cutoff d >= 63. Peel vertices of degree at most d,
-- then restore each removed edge with a binary AND and an OR.
theorem PEqualNP.Outside.R_meta_4191_640
    (dense : ∃ d b : ℕ, 63 ≤ d ∧ ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      (∀ v, H.degree v = 0 ∨ d < H.degree v) →
      (∀ v (p : H.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ D : Circuit, Monotone2 D → (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        decide (∃ u v, H.Adj u v ∧ x u = true ∧ x v = true)) →
      ∃ R : Circuit, Monotone2 R ∧ IsReadK n R 1 ∧
        R.size + 1 ≤ b * (D.size + 1) ∧
        ∀ x : Fin n → Bool, R.eval (List.ofFn x) = D.eval (List.ofFn x))
    (restore : ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      [DecidableRel H.Adj], H ≤ G → ∀ D : Circuit, Monotone2 D → IsReadK n D 1 →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        decide (∃ u v, H.Adj u v ∧ x u = true ∧ x v = true)) →
      ∃ R : Circuit, Monotone2 R ∧ IsReadK n R 1 ∧
        R.size ≤ D.size + 2 * (G.edgeFinset \ H.edgeFinset).card + 1 ∧
        ∀ x : Fin n → Bool, R.eval (List.ofFn x) =
          decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x2 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.ReadK.IsReadK x2 x10 (1 : ℕ) ∧ x10.size + (1 : ℕ) ≤ x1 * (x7.size + (1 : ℕ)) ∧ ∀ (x11 : Fin x2 → Bool), x10.eval (List.ofFn x11) = x7.eval (List.ofFn x11) := by
  classical
  have pin (n : ℕ) (C : Circuit) (s : Finset (Fin n)) (hm : Monotone2 C) :
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size + 1 ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
          C.eval (List.ofFn (fun i => if i ∈ s then x i else false)) := by
    let f (i : ℕ) : ℕ := if h : i < n then if (⟨i,h⟩ : Fin n) ∈ s then i else n else i+1
    let g (a : Gate) : Gate := ⟨a.op,a.inputs.map f⟩
    let z : Gate := ⟨.or,[]⟩
    let D : Circuit := ⟨z :: C.gates.map g, f C.output⟩
    refine ⟨D, ?_, ?_, ?_⟩
    · intro a ha
      change a ∈ z :: C.gates.map g at ha
      rcases List.mem_cons.mp ha with rfl | h
      · simp [z]
      · obtain ⟨a,hi,rfl⟩ := List.mem_map.mp h
        simpa [g] using hm a hi
    · change (z :: C.gates.map g).length ≤ C.gates.length + 1
      simp
    · intro x
      let step (a : List Bool) (q : Gate) := a ++ [q.op.eval (q.inputs.map fun i => a.getD i false)]
      have liftRun (qs : List Gate) (a b : List Bool) (ha : n ≤ a.length)
          (hl : b.length = a.length + 1) (he : ∀ i, b.getD (f i) false = a.getD i false) :
          ∀ i, ((qs.map g).foldl step b).getD (f i) false =
            (qs.foldl step a).getD i false := by
        induction qs generalizing a b with
        | nil => simpa using he
        | cons q qs ih =>
          change ∀ i, ((qs.map g).foldl step (step b (g q))).getD (f i) false =
            (qs.foldl step (step a q)).getD i false
          apply ih
          · simp [step]; omega
          · simp [step,hl]
          · intro i
            have hval : (g q).op.eval ((g q).inputs.map fun j => b.getD j false) =
                q.op.eval (q.inputs.map fun j => a.getD j false) := by
              simp only [g,List.map_map,Function.comp_def]; rw [show (fun j => b.getD (f j) false) = (fun j => a.getD j false) from funext he]
            by_cases hi : i < a.length
            · have hf : f i < b.length := by
                dsimp [f]; split <;> rename_i h
                · split <;> omega
                · omega
              simpa only [step, List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hf] using he i
            · have hn : ¬i<n := by omega
              have hf : f i = i+1 := by simp [f,hn]
              have hb : b.length ≤ f i := by omega
              unfold step
              rw [List.getD_append_right _ _ _ _ (by omega : a.length ≤ i),
                List.getD_append_right _ _ _ _ hb, hval]
              congr 1
              omega
      let y : Fin n → Bool := fun i => if i ∈ s then x i else false
      have initial (i : ℕ) :
          (List.ofFn x ++ [false]).getD (f i) false = (List.ofFn y).getD i false := by
        by_cases h : i<n
        · let j : Fin n := ⟨i,h⟩
          by_cases hj : j∈s
          · have hfi : f i=i := by simp [f,h,hj,j] at *
            rw [hfi,List.getD_append _ _ _ _ (by simpa using h)]
            simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,h,y,hj,j] at *
          · have hnj : (⟨i,h⟩ : Fin n) ∉ s := hj
            have hfi : f i=n := by simp [f,h,hnj]
            rw [hfi,List.getD_append_right _ _ _ _ (by simp)]
            simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,h,y,hj,j] at *
        · have hfi : f i=i+1 := by simp [f,h]
          rw [hfi]
          simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simp;omega : (List.ofFn x ++ [false]).length ≤ i+1),List.getElem?_eq_none (by simpa using Nat.le_of_not_gt h : (List.ofFn y).length ≤ i)]
      exact liftRun C.gates (List.ofFn y) (List.ofFn x ++ [false])
        (by simp) (by simp) initial C.output
  have graphCore {m : ℕ} (d : ℕ) (G : SimpleGraph (Fin m)) :
      ∃ (s : Finset (Fin m)) (H : SimpleGraph (Fin m)),
        (∀ u v, H.Adj u v ↔ G.Adj u v ∧ u ∈ s ∧ v ∈ s) ∧
        (∀ v, H.degree v = 0 ∨ d < H.degree v) ∧
        G.edgeSet.ncard ≤ H.edgeSet.ncard + d * G.support.ncard := by
    induction G using (measure (fun g : SimpleGraph (Fin m) => g.support.ncard)).wf.induction with
    | h G ih =>
      by_cases done : ∀ v, G.degree v = 0 ∨ d < G.degree v
      · exact ⟨Finset.univ, G, by simp, done, by omega⟩
      push Not at done
      obtain ⟨v, hv, hlow⟩ := done
      let J := G.deleteIncidenceSet v
      have hstrict : J.support.toFinset ⊂ G.support.toFinset := by
        have sub : J.support.toFinset ⊆ G.support.toFinset := by
          intro w hw
          exact Set.mem_toFinset.mpr (SimpleGraph.support_mono (G.deleteIncidenceSet_le v)
            (Set.mem_toFinset.mp hw))
        apply (Finset.ssubset_iff_of_subset sub).2
        have inside : v ∈ G.support := (G.degree_pos_iff_exists_adj v).mp (Nat.pos_of_ne_zero hv)
        refine ⟨v, Set.mem_toFinset.mpr inside, ?_⟩
        intro mem
        obtain ⟨w, hw⟩ := Set.mem_toFinset.mp mem
        exact (SimpleGraph.deleteIncidenceSet_adj.mp hw).2.1 rfl
      have hsmall : J.support.ncard < G.support.ncard := by
        simpa only [← Set.ncard_eq_toFinset_card'] using Finset.card_lt_card hstrict
      obtain ⟨s, H, hsg, hdeg, hcount⟩ := ih J hsmall
      refine ⟨s.erase v, H, ?_, hdeg, ?_⟩
      · intro x y
        rw [hsg]
        simp only [J, SimpleGraph.deleteIncidenceSet_adj, Finset.mem_erase]
        tauto
      · have hcard := Finset.card_lt_card hstrict
        have hn : J.support.ncard < G.support.ncard := by simpa only [← Set.ncard_eq_toFinset_card'] using hcard
        have hmul := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hn)
        have he : J.edgeSet.ncard = G.edgeSet.ncard - G.degree v := by
          simpa only [J, SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card'] using
            G.card_edgeFinset_deleteIncidenceSet v
        have gle : G.degree v ≤ G.edgeSet.ncard := by
          simpa only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card'] using G.degree_le_card_edgeFinset v
        rw [Nat.mul_succ] at hmul
        omega

  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let wf (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w
  have wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
      wf (g :: gs) w = wf gs (step w g) := rfl
  have length_step (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
    simp [step]
  have wf_set (k : ℕ) (b : Bool) (gs : List Gate) (hgs : ∀ g ∈ gs, k ∉ g.inputs) :
      ∀ w : List Bool, k < w.length → wf gs (w.set k b) = (wf gs w).set k b := by
    induction gs with
    | nil => intro w _; rfl
    | cons g gs ih =>
      intro w hk
      have hg : k ∉ g.inputs := hgs g (by simp)
      have hrest : ∀ g' ∈ gs, k ∉ g'.inputs := fun g' hg' => hgs g' (by simp [hg'])
      rw [wf_cons, wf_cons]
      have hmap : (g.inputs.map fun i => (w.set k b).getD i false)
          = (g.inputs.map fun i => w.getD i false) := by
        apply List.map_congr_left
        intro i hi
        have hik : i ≠ k := fun h => hg (h ▸ hi)
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_set_ne (Ne.symm hik)]
      have hs : step (w.set k b) g = (step w g).set k b := by
        unfold step
        rw [hmap, List.set_append_left _ _ (by simpa using hk)]
      rw [hs, ih hrest _ (by rw [length_step]; omega)]
  have essential_vertices {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
      (hC : Monotone2 C)
      (hG : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
          decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) :
      G.support.ncard ≤ 2 * C.size + 1 := by
    classical
    let reads := C.output :: C.gates.flatMap Gate.inputs
    have used (v : Fin n) (hv : v ∈ G.support) : v.val ∈ reads := by
      by_contra absent
      obtain ⟨w, hw⟩ := hv
      have noout : C.output ≠ v.val := by
        intro e
        exact absent (by simp [reads, e])
      have noinputs : ∀ g ∈ C.gates, v.val ∉ g.inputs := by
        intro g hg i
        exact absent (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨g,hg,i⟩))
      let x : Fin n → Bool := fun i => decide (i = w)
      let y : Fin n → Bool := fun i => decide (i = v ∨ i = w)
      have hx : C.eval (List.ofFn x) = false := by
        rw [hG]
        simp [x, G.loopless]
      have hy : C.eval (List.ofFn y) = true := by
        rw [hG, decide_eq_true_eq]
        exact ⟨v,w,hw,by simp [y],by simp [y]⟩
      have hset : (List.ofFn x).set v.val true = List.ofFn y := by
        apply List.ext_getElem
        · simp
        · intro i hi hj
          by_cases eq : i = v.val
          · subst i
            simp [List.getElem_set, y]
          · simp [List.getElem_set, x, y, eq, Fin.ext_iff, Ne.symm eq]
      have hs := wf_set v.val true C.gates noinputs (List.ofFn x) (by simpa using v.isLt)
      have unchanged : C.eval (List.ofFn y) = C.eval (List.ofFn x) := by
        rw [← hset]
        change (wf C.gates ((List.ofFn x).set v.val true)).getD C.output false =
          (wf C.gates (List.ofFn x)).getD C.output false
        rw [hs, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_set_ne (Ne.symm noout)]
      simp [hx,hy] at unchanged
    have subset : G.support.toFinset.image Fin.val ⊆ reads.toFinset := by
      intro i hi
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hi
      exact List.mem_toFinset.mpr (used v (Set.mem_toFinset.mp hv))
    have lengths (gs : List Gate) (hs : ∀g ∈gs, g.inputs.length ≤ 2) :
        (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
      induction gs with
      | nil => simp
      | cons g gs ih =>
        have ig := hs g (by simp)
        have it := ih (fun u hu => hs u (by simp [hu]))
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        omega
    have len := lengths C.gates (fun g hg => (hC g hg).2)
    calc
      G.support.ncard = (G.support.toFinset.image Fin.val).card := by
        rw [Finset.card_image_of_injective _ Fin.val_injective, ← Set.ncard_eq_toFinset_card']
      _ ≤ reads.toFinset.card := Finset.card_le_card subset
      _ ≤ reads.length := List.toFinset_card_le reads
      _ ≤ 2 * C.size + 1 := by
        change (_ :: C.gates.flatMap Gate.inputs).length ≤ 2 * C.gates.length + 1
        simpa only [List.length_cons] using Nat.succ_le_succ len
  obtain ⟨d, b, _, hdense⟩ := dense
  refine ⟨2*b + 4*d + 1, ?_⟩
  intro n G iG hdegree hgirth C hC heval
  obtain ⟨s, H, hadj, hH, hcount⟩ := graphCore d G
  have hHG : H ≤ G := fun _ _ h => ((hadj _ _).mp h).1
  have hused := essential_vertices G C hC (fun x => (heval x).trans (decide_eq_decide.mpr Iff.rfl))
  have hsub : H.edgeFinset ⊆ G.edgeFinset := by
    intro e he
    exact SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.edgeSet_mono hHG (SimpleGraph.mem_edgeFinset.mp he))
  have hedge : (G.edgeFinset \ H.edgeFinset).card ≤ d * (2*(C.size+1)) := by
    rw [Finset.card_sdiff_of_subset hsub]
    have hge : G.edgeFinset.card = G.edgeSet.ncard := by
      exact (Set.ncard_eq_toFinset_card' G.edgeSet).symm
    have hhe : H.edgeFinset.card = H.edgeSet.ncard := by
      exact (Set.ncard_eq_toFinset_card' H.edgeSet).symm
    rw [hge, hhe]
    have hc : G.support.ncard ≤ 2 * (C.size+1) := by omega
    have hm := Nat.mul_le_mul_left d hc
    omega
  obtain ⟨D, hD, hsize, hpinned⟩ := pin n C s hC
  have hgraph (x : Fin n → Bool) : D.eval (List.ofFn x) =
      decide (∃ u v, H.Adj u v ∧ x u = true ∧ x v = true) := by
    rw [hpinned, heval]
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨u,v,ha,hu,hv⟩
      have hus : u ∈ s := by by_contra hn; simp [hn] at hu
      have hvs : v ∈ s := by by_contra hn; simp [hn] at hv
      exact ⟨u,v,(hadj u v).2 ⟨ha,hus,hvs⟩,by simpa [hus] using hu,by simpa [hvs] using hv⟩
    · rintro ⟨u,v,ha,hu,hv⟩
      obtain ⟨ha,hus,hvs⟩ := (hadj u v).mp ha
      exact ⟨u,v,ha,by simp [hus,hu],by simp [hvs,hv]⟩
  have hcycle : ∀ v (p : H.Walk v v), p.IsCycle → 5 ≤ p.length := by
    intro v p hp
    have hc := hgirth v (p.mapLe hHG) ((SimpleGraph.Walk.isCycle_mapLe hHG).2 hp)
    simpa only [SimpleGraph.Walk.length_mapLe] using hc
  obtain ⟨R, hR, hread, hbound, hfun⟩ := hdense n H hH hcycle D hD hgraph
  obtain ⟨T, hT, htread, hts, htf⟩ := restore n G H hHG R hR hread
    (fun x => (hfun x).trans (hgraph x))
  refine ⟨T, hT, htread, ?_, fun x => (htf x).trans (heval x).symm⟩
  have hle : D.size + 1 ≤ 2 * (C.size + 1) := by omega
  have hmul := Nat.mul_le_mul_left b hle
  have ha : 1 ≤ C.size + 1 := by omega
  nlinarith only [hts, hbound, hmul, hedge, ha]
