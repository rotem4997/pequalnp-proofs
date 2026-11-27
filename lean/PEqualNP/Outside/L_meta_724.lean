import PEqualNP.Defs

-- Certificate and lower-bound argument by willzh0 in upstream PR 920.
-- The final inequality below specializes that argument to the L-meta-724 statement.

/-!
# OR complexity of the two pentagons sharing an edge

This file proves that no monotone circuit with at most seven OR gates
computes the stated graph function. AND gates, intermediate fanout, and
the location of the output wire are unrestricted by the lower bound.
-/

namespace PEqualNP.Outside.L_meta_724_aux
namespace OrCost

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Arbitrarily many AND gates and both constants are free. -/
inductive Meet {X : Type} (B : Set (Set X)) : Set X → Prop
  | atom {f} : f ∈ B → Meet B f
  | top : Meet B Set.univ
  | bot : Meet B ∅
  | inter {f g} : Meet B f → Meet B g → Meet B (f ∩ g)

/-- One counted instruction adjoins the union of two already available meets. -/
inductive Run {X : Type} : Set (Set X) → ℕ → Set X → Prop
  | done {B f} : Meet B f → Run B 0 f
  | add {B a b k f} : Meet B a → Meet B b → Run (insert (a∪b) B) k f → Run B (k+1) f

theorem mapMeet {X Y : Type} {B : Set (Set X)} {D : Set (Set Y)} (π : Y → X)
    (atoms : ∀ f∈B, Meet D (π ⁻¹' f)) {f} (h : Meet B f) : Meet D (π ⁻¹' f) := by
  induction h with
  | atom hf => exact atoms _ hf
  | top => exact Meet.top
  | bot => exact Meet.bot
  | inter _ _ hi hj => exact hi.inter hj

theorem weaken {X : Type} {B D : Set (Set X)} (hd : B ⊆ D) {f}
    (h : Meet B f) : Meet D f :=
  mapMeet id (fun _ hf => Meet.atom (hd hf)) h

theorem freeMap {X Y : Type} {B : Set (Set X)} {D : Set (Set Y)} (π : Y → X)
    (atoms : ∀ f∈B, Meet D (π ⁻¹' f)) {k f} (h : Run B k f) : Run D k (π ⁻¹' f) := by
  induction h generalizing D with
  | done hf => exact Run.done (mapMeet π atoms hf)
  | @add B a b k f ha hb _ ih =>
    apply Run.add (mapMeet π atoms ha) (mapMeet π atoms hb)
    apply ih
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl|hg
    · exact Meet.atom (Set.mem_insert _ _)
    · exact weaken (Set.subset_insert _ _) (atoms _ hg)

def Good {X Y : Type} (π : Y → X) (p q : X) (f : Set X) : Prop :=
  (p∈f ↔ q∈f) ∨ π ⁻¹' f = ∅

theorem meetGood {X Y : Type} {B : Set (Set X)} {π : Y → X} {p q : X}
    (atoms : ∀ f∈B, Good π p q f) {f} (h : Meet B f) : Good π p q f := by
  induction h with
  | atom h => exact atoms _ h
  | top => exact Or.inl Iff.rfl
  | bot => exact Or.inr rfl
  | inter _ _ ih jh =>
    rcases ih with h|h
    · rcases jh with j|j
      · exact Or.inl (and_congr h j)
      · exact Or.inr (by rw [Set.preimage_inter,j,Set.inter_empty])
    · exact Or.inr (by rw [Set.preimage_inter,h,Set.empty_inter])

/-- A change visible at p,q but absent from all surviving raw inputs forces
one OR to disappear on restriction. -/
theorem paidMap {X Y : Type} {B : Set (Set X)} {D : Set (Set Y)}
    (π : Y → X) (p q : X) (atoms : ∀ f∈B, Meet D (π ⁻¹' f))
    (good : ∀ f∈B, Good π p q f) {k f} (h : Run B k f) (bad : ¬Good π p q f) :
    ∃ j<k, Run D j (π ⁻¹' f) := by
  classical
  induction h generalizing D with
  | done hf => exact (bad (meetGood good hf)).elim
  | @add B a b k f ha hb tail ih =>
    have aa := mapMeet π atoms ha
    have ab := mapMeet π atoms hb
    by_cases gg : Good π p q (a∪b)
    · let D' := insert ((π ⁻¹' a)∪(π ⁻¹' b)) D
      have m : ∀ g∈insert (a∪b) B, Meet D' (π ⁻¹' g) := by
        intro g hg
        rcases Set.mem_insert_iff.mp hg with rfl|hg
        · exact Meet.atom (Set.mem_insert _ _)
        · exact weaken (Set.subset_insert _ _) (atoms _ hg)
      obtain ⟨j,hj,hr⟩ := ih m (fun g hg => (Set.mem_insert_iff.mp hg).elim
        (fun e => e ▸ gg) (good g)) bad
      exact ⟨j+1,by omega,Run.add aa ab hr⟩
    · have bypass : Meet D (π ⁻¹' (a∪b)) := by
        rcases meetGood good ha with h|h
        · rcases meetGood good hb with z|z
          · exact (gg (Or.inl (or_congr h z))).elim
          · simpa [Set.preimage_union,z] using aa
        · simpa [Set.preimage_union,h] using ab
      exact ⟨k,by omega,freeMap π (fun g hg => (Set.mem_insert_iff.mp hg).elim
        (fun e => e ▸ bypass) (atoms g)) tail⟩

abbrev V (n : ℕ) := Fin n
abbrev Sig (n : ℕ) := Set (Finset (V n))
def var {n} (v : V n) : Sig n := {s | v∈s}
def inputs (n : ℕ) : Set (Sig n) := Set.range var
def edge {n} (G : SimpleGraph (V n)) : Sig n :=
  {s | ∃ u v, G.Adj u v ∧ u∈s ∧ v∈s}
def P {n} (G : SimpleGraph (V n)) (t : ℕ) : Prop :=
  ∃ k≤t, Run (inputs n) k (edge G)

def erase {n} (v : V n) (s : Finset (V n)) := s.erase v

theorem prVar {n} (v u : V n) : (erase v) ⁻¹' var u =
    if u=v then ∅ else var u := by
  ext s; by_cases h : u=v <;> simp [h,erase,var]

theorem inputMap {n} (v : V n) (f : Sig n) (hf : f∈inputs n) :
    Meet (inputs n) (erase v ⁻¹' f) := by
  obtain ⟨u,rfl⟩ := hf
  rw [prVar]; split
  · exact Meet.bot
  · exact Meet.atom ⟨u,rfl⟩

theorem inputGood {n} (v : V n) (s : Finset (V n)) (f : Sig n) (hf : f∈inputs n) :
    Good (erase v) (insert v s) s f := by
  obtain ⟨u,rfl⟩ := hf
  by_cases h : u=v
  · exact Or.inr (by simp [prVar,h])
  · exact Or.inl (by simp [var,h])

theorem prEdge {n} (G : SimpleGraph (V n)) (v : V n) :
    erase v ⁻¹' edge G = edge (G.deleteIncidenceSet v) := by
  ext s
  change (∃ i j, G.Adj i j ∧ i∈s.erase v ∧ j∈s.erase v) ↔
    (∃ i j, (G.deleteIncidenceSet v).Adj i j ∧ i∈s ∧ j∈s)
  simp only [SimpleGraph.deleteIncidenceSet_adj,Finset.mem_erase]
  tauto

theorem singleton_no {n} (G : SimpleGraph (V n)) (w : V n) : {w} ∉ edge G := by
  rintro ⟨u,v,ha,hu,hv⟩
  simp only [Finset.mem_singleton] at hu hv
  exact ha.ne (hu.trans hv.symm)

theorem two_yes {n} {G : SimpleGraph (V n)} {v w : V n} (h : G.Adj v w) :
    insert v {w} ∈ edge G :=
  ⟨v,w,h,by simp,by simp⟩

theorem hasSurvivor {n} {G : SimpleGraph (V n)} {v i j : V n}
    (h : G.Adj i j) (hi : i≠v) (hj : j≠v) : erase v ⁻¹' edge G ≠ ∅ := by
  intro he
  have hh : ({i,j} : Finset (V n)) ∈ erase v ⁻¹' edge G :=
    ⟨i,j,h,by simp [erase,hi],by simp [erase,hj]⟩
  rw [he] at hh; exact hh

theorem paidVertex {n} {G : SimpleGraph (V n)} {t} {v w i j : V n}
    (run : P G t) (hw : G.Adj v w) (h : G.Adj i j) (hi : i≠v) (hj : j≠v) :
    ∃ b, P (G.deleteIncidenceSet v) b ∧ b+1≤t := by
  obtain ⟨k,hk,r⟩ := run
  have bad : ¬ Good (erase v) (insert v {w}) {w} (edge G) :=
    fun hbad => hbad.elim (fun z => singleton_no G _ (z.mp (two_yes hw))) (hasSurvivor h hi hj)
  obtain ⟨j,hj,rt⟩ := paidMap (erase v) (insert v {w}) {w} (inputMap v) (inputGood v _) r bad
  rw [prEdge] at rt
  exact ⟨j,⟨j,le_rfl,rt⟩,by omega⟩

noncomputable def bit {n} (s : Finset (V n)) (f : Sig n) : Bool := by
  classical exact decide (s∈f)

theorem bit_read {n} (s : Finset (V n)) (ws : List (Sig n)) (j : ℕ) :
    (ws.map (bit s)).getD j false = bit s (ws.getD j ∅) := by
  classical
  by_cases hj : j<ws.length
  · simp [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hj]
  · simp [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_none (Nat.le_of_not_gt hj),bit]

def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w++[g.op.eval (g.inputs.map fun j => w.getD j false)]

def isOr (g : Gate) : Bool := match g.op with | .or => true | _ => false
def countOr (gs : List Gate) := (gs.filter isOr).length

theorem compileSig {n} (gs : List Gate) (out : ℕ) (B : Set (Sig n)) (w : List (Sig n))
    (f : Sig n) (legal : ∀g∈gs, g.op∈({GateOp.and,GateOp.or}:Set GateOp) ∧ g.inputs.length≤2)
    (hw : ∀z∈w, Meet B z)
    (val : ∀s, (gs.foldl gateStep (w.map (bit s))).getD out false = bit s f) :
    ∃ k≤countOr gs, Run B k f := by
  classical
  induction gs generalizing B w with
  | nil =>
    obtain h : w.getD out ∅ = f := by
      ext s
      have hh := val s
      rw [List.foldl_nil,bit_read] at hh
      simpa [bit] using (Bool.eq_iff_iff.mp hh)
    refine ⟨0,by simp [countOr],Run.done ?_⟩
    rw [←h]
    by_cases j : out<w.length
    · rw [List.getD_eq_getElem _ _ j]; exact hw _ (List.getElem_mem _)
    · rw [List.getD_eq_default _ _ (by omega)]; exact Meet.bot
  | cons g gs ih =>
    have ok := legal g (by simp)
    have ht : ∀ a∈gs, a.op∈({GateOp.and,GateOp.or}:Set GateOp) ∧ a.inputs.length≤2 :=
      fun a h => legal _ (by simp [h])
    have rd (j : ℕ) : Meet B (w.getD j ∅) := by
      by_cases hj : j<w.length
      · rw [List.getD_eq_getElem _ _ hj]; exact hw _ (List.getElem_mem _)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Meet.bot
    have handle (z : Sig n) (hz : Meet B z ∨ ∃ a b, Meet B a ∧ Meet B b ∧ z=a∪b ∧ g.op=.or)
        (step : ∀ s, gateStep (w.map (bit s)) g = (w++[z]).map (bit s)) :
        ∃ k≤countOr (g::gs), Run B k f := by
      have val' s : (gs.foldl gateStep ((w++[z]).map (bit s))).getD out false = bit s f := by
        simpa only [List.foldl_cons,step] using val s
      rcases hz with free|⟨a,b,ha,hb,rfl,hop⟩
      · obtain ⟨k,hk,h⟩ := ih B _ ht (fun u hu => by
          rcases List.mem_append.mp hu with hu|hu
          · exact hw _ hu
          · simpa [List.mem_singleton.mp hu] using free) val'
        exact ⟨k,hk.trans (by simp [countOr,List.filter_cons]; split <;> simp),h⟩
      · obtain ⟨k,hk,h⟩ := ih (insert (a∪b) B) _ ht (fun u hu => by
          rcases List.mem_append.mp hu with hu|hu
          · exact weaken (Set.subset_insert _ _) (hw _ hu)
          · exact Meet.atom (List.mem_singleton.mp hu ▸ Set.mem_insert _ _)) val'
        refine ⟨k+1,?_,Run.add ha hb h⟩
        have go : isOr g = true := by simp [isOr,hop]
        simpa [countOr,go] using Nat.succ_le_succ hk
    obtain ⟨op,l⟩ := g
    change (op=.and ∨ op=.or) ∧ l.length≤2 at ok
    obtain ⟨opok,hlen⟩ := ok
    cases l with
    | nil =>
      rcases opok with rfl|rfl
      · apply handle Set.univ (Or.inl Meet.top); intro s; simp [gateStep,GateOp.eval,bit]
      · apply handle ∅ (Or.inl Meet.bot); intro s; simp [gateStep,GateOp.eval,bit]
    | cons i l =>
      cases l with
      | nil =>
        rcases opok with rfl|rfl <;> apply handle (w.getD i ∅) (Or.inl (rd i)) <;>
          intro s <;> simp [gateStep,GateOp.eval] <;> cases w[i]? <;> simp [bit]
      | cons j l =>
        cases l with
        | cons => simp at hlen
        | nil =>
          rcases opok with rfl|rfl
          · apply handle _ (Or.inl ((rd i).inter (rd j)))
            intro s; simp [gateStep,GateOp.eval,bit]
            cases w[i]? <;> cases w[j]? <;> simp [bit]
          · apply handle _ (Or.inr ⟨_,_,rd i,rd j,rfl,rfl⟩)
            intro s; simp [gateStep,GateOp.eval,bit]
            cases w[i]? <;> cases w[j]? <;> simp [bit]

theorem count_le (gs : List Gate) (A : Finset ℕ)
    (h : ∀ j g, gs[j]?=some g → g.op=.or → j∈A) : countOr gs ≤ A.card := by
  induction gs generalizing A with
  | nil => simp [countOr]
  | cons g gs ih =>
    let D := (A.erase 0).image Nat.pred
    have tail : countOr gs ≤ D.card := ih D (fun j k hk hko => by
      have hj := h (j+1) k (by simpa using hk) hko
      exact Finset.mem_image.mpr ⟨j+1,by simp [hj],by simp⟩)
    have hd : D.card ≤ (A.erase 0).card := Finset.card_image_le
    cases hg : g.op with
    | or =>
      have zero := h 0 g (by simp) hg
      have hn := Finset.card_erase_add_one zero
      simp [countOr,isOr,hg] at tail ⊢
      omega
    | _ =>
      have hle := Finset.card_le_card (Finset.erase_subset (s:=A) (a:=0))
      simpa [countOr,isOr,hg] using tail.trans (hd.trans hle)

theorem ofCircuit {n} (G : SimpleGraph (V n)) (C : Circuit) (A : Finset ℕ)
    (hc : Monotone2 C) (he : ∀ x : V n → Bool, C.eval (List.ofFn x)=true ↔
      ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true)
    (ha : ∀ j g, C.gates[j]?=some g → g.op=.or → j∈A) : P G A.card := by
  classical
  let w := List.ofFn (fun v : V n => var v)
  have hw : ∀z∈w, Meet (inputs n) z := by
    intro z hz
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hz
    exact Meet.atom ⟨v,rfl⟩
  have hval (s : Finset (V n)) :
      (C.gates.foldl gateStep (w.map (bit s))).getD C.output false = bit s (edge G) := by
    let x := fun v : V n => decide (v∈s)
    have hin : w.map (bit s)=List.ofFn x := by
      rw [show w=List.ofFn (fun v : V n => var v) from rfl,List.map_ofFn]
      apply congrArg List.ofFn
      funext v
      by_cases h : v∈s <;> simp [x,bit,var,h]
    rw [hin]
    change C.eval (List.ofFn x) = _
    apply Bool.eq_iff_iff.mpr
    change C.eval (List.ofFn x)=true ↔ decide (s∈edge G)=true
    rw [decide_eq_true_eq]
    simpa only [x,edge,Set.mem_ofPred_eq,decide_eq_true_eq] using he x
  obtain ⟨k,hk,r⟩ := compileSig C.gates C.output _ w _ hc hw hval
  exact ⟨k,hk.trans (count_le C.gates A ha),r⟩

def need {n} (a : Finset (V n)) : Sig n := {s | a⊆s}

theorem raw_meets {n} {f : Sig n} (hf : Meet (inputs n) f) :
    f=∅ ∨ ∃ a : Finset (V n), f=need a := by
  induction hf with
  | atom h =>
    obtain ⟨v,rfl⟩ := h
    exact Or.inr ⟨{v},by ext s; simp [need,var]⟩
  | top => exact Or.inr ⟨∅,by ext s; simp [need]⟩
  | bot => exact Or.inl rfl
  | inter _ _ ih jh =>
    rcases ih with rfl|⟨a,rfl⟩
    · exact Or.inl (Set.empty_inter _)
    rcases jh with rfl|⟨b,rfl⟩
    · exact Or.inl (Set.inter_empty _)
    · exact Or.inr ⟨a∪b,by ext s; simp [need]⟩

theorem need_dead {n} {a : Finset (V n)} {v : V n} (h : v∈a) :
    erase v ⁻¹' need a = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro s hinc
  exact Finset.notMem_erase _ _ (hinc h)

theorem accept_around {n} {G : SimpleGraph (V n)} {v w : V n} {s : Finset (V n)}
    (hw : G.Adj v w) (hs : w∈s) : insert v s ∈ edge G :=
  ⟨v,w,hw,by simp,Finset.mem_insert_of_mem hs⟩

theorem reject_pair {n} {G : SimpleGraph (V n)} {u w : V n} (h : ¬G.Adj u w) :
    ({u,w} : Finset (V n)) ∉ edge G := by
  rintro ⟨a,b,hab,ha,hb⟩
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
  · exact hab.ne rfl
  · exact h hab
  · exact h hab.symm
  · exact hab.ne rfl

theorem substituteFirst {n} {f g : Sig n} {k} (hg : Meet (inputs n) g)
    (tail : Run (insert g (inputs n)) k f) : Run (inputs n) k f :=
  freeMap id (fun _ hz => (Set.mem_insert_iff.mp hz).elim (fun e => e ▸ hg) (fun h => Meet.atom h)) tail

/-- A first OR that disappears upon restriction can be bypassed before charging
a second OR, provided a pair of tests witnesses a surviving distinction. -/
theorem twoPaymentOfProbe {n} {G : SimpleGraph (V n)} {v : V n} {g : Sig n} {k}
    (tail : Run (insert g (inputs n)) k (edge G)) (s : Finset (V n))
    (free : Meet (inputs n) (erase v ⁻¹' g))
    (agree : insert v s ∈ g ↔ s∈g) (yes : insert v s ∈ edge G) (no : s∉edge G)
    (survive : ∃ i j, G.Adj i j ∧ i≠v ∧ j≠v) :
    ∃ b, P (G.deleteIncidenceSet v) b ∧ b+2≤k+1 := by
  obtain ⟨i,j,ij,iv,jv⟩ := survive
  have bad : ¬ Good (erase v) (insert v s) s (edge G) :=
    fun h => h.elim (fun e => no (e.mp yes)) (hasSurvivor ij iv jv)
  have map (z) (hz : z∈insert g (inputs n)) : Meet (inputs n) (erase v ⁻¹' z) :=
    (Set.mem_insert_iff.mp hz).elim (fun e => e ▸ free) (inputMap v z)
  have good (z) (hz : z∈insert g (inputs n)) : Good (erase v) (insert v s) s z :=
    (Set.mem_insert_iff.mp hz).elim (fun e => e ▸ Or.inl agree) (inputGood v s z)
  obtain ⟨b,hb,r⟩ := paidMap (erase v) (insert v s) s map good tail bad
  rw [prEdge] at r
  exact ⟨b,⟨b,le_rfl,r⟩,by omega⟩

theorem hit_other {n} {G : SimpleGraph (V n)} {v : V n}
    (deg : (G.neighborSet v).ncard=2) (avoid : V n) : ∃ w, G.Adj v w ∧ w≠avoid := by
  obtain ⟨p,hp,q,hq,hpq⟩ := (Set.one_lt_ncard (s:=G.neighborSet v)).mp (by omega)
  by_cases h : p=avoid
  · exact ⟨q,hq,by simpa only [←h] using hpq.symm⟩
  · exact ⟨p,hp,h⟩

theorem other_member {n} {a : Finset (V n)} {v} (hv : v∈a) (hne : a≠{v}) :
    ∃ u∈a, u≠v := by
  by_contra! hs
  apply hne
  ext z
  simp only [Finset.mem_singleton]
  exact ⟨hs z,fun e => e ▸ hv⟩

/-- Find a second payment in a degree-two core. The combinatorial hypotheses
state exactly which neighboring vertices the test assignments need. -/
theorem corePayments {n} {G : SimpleGraph (V n)} {t} (cost : P G t)
    (someEdge : ∃ i j, G.Adj i j)
    (degrees : ∀ v : V n, (∃ w,G.Adj v w) → (G.neighborSet v).ncard=2)
    (noTwins : ∀ {v u : V n}, v≠u → (G.neighborSet v).ncard=2 →
      ∃ w, G.Adj v w ∧ ¬G.Adj u w) :
    ∃ v b, (G.neighborSet v).ncard=2 ∧ P (G.deleteIncidenceSet v) b ∧ b+2≤t := by
  classical
  obtain ⟨v₀,w₀,h₀⟩ := someEdge
  have surv (v : V n) (act : ∃w,G.Adj v w) : ∃i j, G.Adj i j ∧ i≠v ∧ j≠v := by
    obtain ⟨w,hw⟩ := act
    obtain ⟨u,hu,huv⟩ := hit_other (degrees w ⟨v,hw.symm⟩) v
    exact ⟨w,u,hu,hw.ne.symm,huv⟩
  obtain ⟨k,kt,program⟩ := cost
  have improve {b} (r : Run (inputs n) b (edge G)) (hb : b<k) :
      ∃ v c, (G.neighborSet v).ncard=2 ∧ P (G.deleteIncidenceSet v) c ∧ c+2≤t := by
    obtain ⟨i,j,ij,iv,jv⟩ := surv v₀ ⟨w₀,h₀⟩
    obtain ⟨c,hc,hcb⟩ := paidVertex (t:=b) ⟨b,le_rfl,r⟩ h₀ ij iv jv
    exact ⟨v₀,c,degrees _ ⟨_,h₀⟩,hc,by omega⟩
  cases program with
  | done hf =>
    obtain ⟨i,j,ij,iv,jv⟩ := surv v₀ ⟨w₀,h₀⟩
    obtain ⟨c,_,hc⟩ := paidVertex (t:=0) ⟨0,le_rfl,Run.done hf⟩ h₀ ij iv jv
    omega
  | @add _ a b k _ ha hb tail =>
    have redundant (h : Meet (inputs n) (a∪b)) := improve (substituteFirst h tail) (by omega)
    rcases raw_meets ha with rfl|⟨A,rfl⟩
    · apply redundant; simpa using hb
    rcases raw_meets hb with rfl|⟨B,rfl⟩
    · apply redundant; simpa using ha
    by_cases ab : A⊆B
    · apply redundant
      have h : need B ⊆ need A := fun s hs => ab.trans hs
      simpa [Set.union_eq_left.mpr h] using ha
    by_cases ba : B⊆A
    · apply redundant
      have h : need A ⊆ need B := fun s hs => ba.trans hs
      simpa [Set.union_eq_right.mpr h] using hb
    obtain ⟨v,hvA,hvB⟩ := Finset.not_subset.mp ab
    obtain ⟨u,huB,huA⟩ := Finset.not_subset.mp ba
    let g := need A ∪ need B
    have fv : Meet (inputs n) (erase v ⁻¹' g) := by
      simpa only [g,Set.preimage_union,need_dead hvA,Set.empty_union] using mapMeet (erase v) (inputMap v) hb
    have fu : Meet (inputs n) (erase u ⁻¹' g) := by
      simpa only [g,Set.preimage_union,need_dead huB,Set.union_empty] using mapMeet (erase u) (inputMap u) ha
    have isolated (l : V n) (no : ¬∃w,G.Adj l w) (free : Meet (inputs n) (erase l ⁻¹' g)) :
        ∃ v c, (G.neighborSet v).ncard=2 ∧ P (G.deleteIncidenceSet v) c ∧ c+2≤t := by
      have eq : erase l ⁻¹' edge G = edge G := by
        ext s
        constructor
        · rintro ⟨i,j,ij,hi,hj⟩
          exact ⟨i,j,ij,Finset.mem_of_mem_erase hi,Finset.mem_of_mem_erase hj⟩
        · rintro ⟨i,j,ij,hi,hj⟩
          have il : i≠l := fun e => no ⟨j,e ▸ ij⟩
          have jl : j≠l := fun e => no ⟨i,e ▸ ij.symm⟩
          exact ⟨i,j,ij,Finset.mem_erase.mpr ⟨il,hi⟩,Finset.mem_erase.mpr ⟨jl,hj⟩⟩
      apply improve (b:=k) _ (by omega)
      rw [←eq]
      exact freeMap (erase l) (fun z hz => (Set.mem_insert_iff.mp hz).elim
        (fun e => e ▸ free) (inputMap l z)) tail
    by_cases av : ∃ w,G.Adj v w
    swap
    · exact isolated v av fv
    by_cases au : ∃ w,G.Adj u w
    swap
    · exact isolated u au fu
    have pay (l : V n) (act : ∃ w,G.Adj l w) (free : Meet (inputs n) (erase l ⁻¹' g))
        (s : Finset (V n)) (agree : insert l s∈g ↔ s∈g) (yes : insert l s∈edge G)
        (no : s∉edge G) : ∃ v c, (G.neighborSet v).ncard=2 ∧ P (G.deleteIncidenceSet v) c ∧ c+2≤t := by
      obtain ⟨c,hc,ht⟩ := twoPaymentOfProbe tail s free agree yes no (surv l act)
      exact ⟨l,c,degrees l act,hc,by omega⟩
    have unchanged (D : Finset (V n)) (l : V n) (hl : l∉D) (s : Finset (V n)) :
        insert l s∈need D ↔ s∈need D := by
      change D⊆insert l s ↔ D⊆s
      exact ⟨fun h r hr => (Finset.mem_insert.mp (h hr)).resolve_left (fun e => hl (e ▸ hr)),
        fun h => h.trans (Finset.subset_insert _ _)⟩
    have gone (D : Finset (V n)) (l r w : V n) (hr : r∈D) (hrl : r≠l) (hrw : w≠r) :
        insert l {w}∉need D ∧ ({w} : Finset (V n))∉need D := by
      exact ⟨fun h => by simpa [hrl,Ne.symm hrw] using h hr,
        fun h => by simpa [Ne.symm hrw] using h hr⟩
    by_cases hA : A={v}
    swap
    · obtain ⟨r,hr,hrv⟩ := other_member hvA hA
      obtain ⟨w,vw,hwr⟩ := hit_other (degrees _ av) r
      obtain ⟨bad₁,bad₂⟩ := gone A v r w hr hrv hwr
      apply pay v av fv {w} _ (two_yes vw) (singleton_no _ _)
      exact or_congr (iff_of_false bad₁ bad₂) (unchanged B v hvB _)
    by_cases hB : B={u}
    swap
    · obtain ⟨r,hr,hru⟩ := other_member huB hB
      obtain ⟨w,uw,hwr⟩ := hit_other (degrees _ au) r
      obtain ⟨bad₁,bad₂⟩ := gone B u r w hr hru hwr
      apply pay u au fu {w} _ (two_yes uw) (singleton_no _ _)
      exact or_congr (unchanged A u huA _) (iff_of_false bad₁ bad₂)
    have vu : v≠u := fun e => hvB (e ▸ huB)
    obtain ⟨w,vw,nuw⟩ := noTwins vu (degrees _ av)
    apply pay v av fv {u,w} _ (accept_around vw (by simp)) (reject_pair nuw)
    have hasU : ∀ s : Finset (V n), u∈s → s∈g := by
      intro s hs; exact Or.inr (by simpa [need,hB] using hs)
    exact iff_of_true (hasU _ (by simp)) (hasU _ (by simp))

end OrCost
end PEqualNP.Outside.L_meta_724_aux

/-! After deleting any vertex, each induced subgraph has a leaf or consists of isolated vertices and cycles. -/

namespace PEqualNP.Outside.L_meta_724_aux
open OrCost
abbrev V8 := Fin 8
abbrev Vertices := Finset V8
def listed : List (V8 × V8) := [(0,1),(1,2),(2,3),(3,4),(4,0),(1,5),(5,6),(6,7),(7,0)]
def link (u v : V8) : Prop := (u,v)∈listed ∨ (v,u)∈listed
instance (u v : V8) : Decidable (link u v) := inferInstanceAs (Decidable (_∨_))
theorem diag : ∀ u : V8, ¬link u u := by decide +kernel
def induced (S : Vertices) : SimpleGraph V8 where
  Adj u v := u∈S ∧ v∈S ∧ link u v
  symm := ⟨fun _ _ ⟨hu,hv,h⟩ => ⟨hv,hu,h.symm⟩⟩
  loopless := ⟨fun u h => diag u h.2.2⟩
instance (S : Vertices) : DecidableRel (induced S).Adj :=
  fun u v => inferInstanceAs (Decidable (u∈S ∧ v∈S ∧ link u v))

def ec (S : Vertices) := (listed.filter fun z => z.1∈S && z.2∈S).length
def dg (S : Vertices) (v : V8) := (Finset.univ.filter fun w => (induced S).Adj v w).card
theorem dg_eq (S : Vertices) (v : V8) : ((induced S).neighborSet v).ncard = dg S v := by
  have h : (induced S).neighborSet v = ↑(Finset.univ.filter fun w => (induced S).Adj v w) := by
    ext w; simp
  rw [h,Set.ncard_coe_finset]; rfl
theorem delete_eq (S : Vertices) (v : V8) :
    (induced S).deleteIncidenceSet v = induced (S.erase v) := by
  ext a b
  simp only [SimpleGraph.deleteIncidenceSet_adj,induced,Finset.mem_erase]
  tauto
theorem properErase (S : Vertices) (v : V8) : S.erase v ≠ Finset.univ := by
  intro e
  have h : v∈S.erase v := e ▸ Finset.mem_univ v
  exact Finset.notMem_erase v S h

set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem counting : ∀ (S : Vertices) (v : V8), ec (S.erase v)+dg S v=ec S := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem shape : ∀ S : Vertices, S≠Finset.univ →
    (∃v,dg S v=1) ∨ (∀v,dg S v=0 ∨ dg S v=2) := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem edgeExists : ∀ S : Vertices, 0<ec S → ∃i j,(induced S).Adj i j := by decide +kernel
theorem dgPos (S : Vertices) (v : V8) : 0<dg S v ↔ ∃w,(induced S).Adj v w := by
  change 0 < (Finset.univ.filter fun w => (induced S).Adj v w).card ↔ _
  simp [Finset.card_pos,Finset.Nonempty]
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem probeNeighbors : ∀ (S : Vertices) (v u : V8), v≠u → dg S v=2 →
    ∃w,(induced S).Adj v w ∧ ¬(induced S).Adj u w := by decide +kernel

theorem residualLower (S : Vertices) (t : Nat) (hS : S≠Finset.univ) (run : P (induced S) t) :
    ec S≤t+1 := by
  induction h : ec S using Nat.strong_induction_on generalizing S t with
  | ind m ih =>
    by_cases small : m≤1
    · omega
    have step (v : V8) (b : Nat) (hd : 0<dg S v)
        (hr : P ((induced S).deleteIncidenceSet v) b) (pay : b+dg S v≤t) : m≤t+1 := by
      have cnt := counting S v
      rw [delete_eq] at hr
      have lb := ih (ec (S.erase v)) (by omega) (S.erase v) b (properErase S v) hr rfl
      omega
    rcases shape S hS with ⟨v,one⟩ | even
    · obtain ⟨w,hw⟩ := (dgPos S v).mp (by omega)
      have cnt := counting S v
      obtain ⟨i,j,adj⟩ := edgeExists (S.erase v) (by omega)
      rw [←delete_eq] at adj
      obtain ⟨ij,iv,jv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp adj
      obtain ⟨b,rb,hb⟩ := paidVertex run hw ij iv jv
      exact step v b (by omega) rb (by omega)
    · obtain ⟨v,b,deg,rb,pay⟩ := corePayments run (edgeExists S (by omega))
          (fun v active => by
            rw [dg_eq]
            have pos := (dgPos S v).mpr active
            exact (even v).resolve_left (by omega))
          (fun {v u} vu d => probeNeighbors S v u vu (dg_eq S v ▸ d))
      rw [dg_eq] at deg
      exact step v b (by omega) rb (by omega)

end PEqualNP.Outside.L_meta_724_aux

/-! Eight-bit masks describe conjunctions of raw variables. Lists of masks describe their disjunctions. -/

namespace PEqualNP.Outside.L_meta_724_aux.OrCost
abbrev M := BitVec 8
abbrev DNF := List M
abbrev VV := Fin 8
def decM (a : M) : Finset VV := Finset.univ.filter fun v => a.getLsbD v.val
def encM (S : Finset VV) : M := BitVec.ofNat 8 (∑v∈S, 2^v.val)
theorem dec_enc : ∀ S : Finset VV, decM (encM S)=S := by decide +kernel
@[simp] theorem mem_decM (a : M) (v : VV) : v∈decM a ↔ a.getLsbD v.val=true := by simp [decM]
theorem dec_or (a b : M) : decM (a ||| b)=decM a ∪ decM b := by
  ext v
  simp
def incM (a b : M) : Bool := (a &&& b)==a
theorem inc_iff (a b : M) : incM a b = true ↔ decM a⊆decM b := by
  change ((a &&& b)==a)=true ↔ _
  rw [beq_iff_eq,BitVec.eq_of_getLsbD_eq_iff]
  constructor
  · intro h v hv
    have eq := h v.val v.isLt
    simp only [mem_decM] at hv ⊢
    simpa [BitVec.getLsbD_and,hv] using eq
  · intro h i hi
    rw [BitVec.getLsbD_and]
    by_cases hh : a.getLsbD i=true
    · have hb := (mem_decM b ⟨i,hi⟩).mp (h ((mem_decM a ⟨i,hi⟩).mpr hh))
      simp [hh,hb]
    · simp [Bool.eq_false_iff.mpr hh]
def sig (l : DNF) : Sig 8 := {s | ∃a∈l, decM a⊆s}
@[simp] theorem sig_nil : sig []=∅ := by ext s; simp [sig]
@[simp] theorem sig_one (a : M) : sig [a]=need (decM a) := by ext s; simp [sig,need]
@[simp] theorem sig_append (a b : DNF) : sig (a++b)=sig a∪sig b := by
  ext s
  simp only [sig,Set.mem_ofPred_eq,List.mem_append,Set.mem_union]
  aesop
def times (a : M) (l : DNF) : DNF := l.map (fun b => a ||| b)
@[simp] theorem sig_times (a : M) (l : DNF) : sig (times a l)=need (decM a) ∩ sig l := by
  ext s
  simp only [times,sig,Set.mem_ofPred_eq,List.mem_map,Set.mem_inter_iff,need]
  constructor
  · rintro ⟨m,⟨b,hb,e⟩,h⟩
    subst m; rw [dec_or,Finset.union_subset_iff] at h
    exact ⟨h.1,b,hb,h.2⟩
  · rintro ⟨ha,b,hb,hs⟩
    exact ⟨_,⟨b,hb,rfl⟩,by rw [dec_or,Finset.union_subset_iff]; exact ⟨ha,hs⟩⟩

def prD (v : VV) (l : DNF) := l.filter fun a => !(a.getLsbD v.val)
theorem sig_pr (v : VV) (l : DNF) : sig (prD v l) = erase v ⁻¹' sig l := by
  ext s
  simp only [sig,prD,Set.mem_ofPred_eq,List.mem_filter,Bool.not_eq_true',Set.mem_preimage,erase]
  constructor
  · rintro ⟨a,⟨ha,hn⟩,sub⟩
    exact ⟨a,ha,fun u hu => Finset.mem_erase.mpr ⟨fun eq => by
      subst u; exact Bool.noConfusion (hn.symm.trans ((mem_decM a v).mp hu)),sub hu⟩⟩
  · rintro ⟨a,ha,sub⟩
    have hx : v∉decM a := fun hv => Finset.notMem_erase _ _ (sub hv)
    exact ⟨a,⟨ha,by simpa [mem_decM] using hx⟩,sub.trans (Finset.erase_subset _ _)⟩

def leD (a b : DNF) := a.all fun x => b.any fun y => incM y x
def eqD (a b : DNF) := leD a b && leD b a
theorem leD_sound {a b : DNF} (h : leD a b) : sig a⊆sig b := by
  intro s hs
  obtain ⟨x,hx,hxs⟩ := hs
  obtain ⟨y,hy,hxy⟩ := List.any_eq_true.mp ((List.all_eq_true.mp h) x hx)
  exact ⟨y,hy,((inc_iff y x).mp hxy).trans hxs⟩
theorem eqD_sound {a b : DNF} (h : eqD a b) : sig a=sig b := by
  have ⟨h1,h2⟩ : leD a b=true ∧ leD b a=true := by simpa only [eqD,Bool.and_eq_true] using h
  exact Set.Subset.antisymm (leD_sound h1) (leD_sound h2)
def evalD (d : DNF) (x : M) := d.any fun a => incM a x
theorem match_iff (d : DNF) (x : M) : evalD d x ↔ decM x∈sig d := by
  simp only [evalD,List.any_eq_true,inc_iff,sig,Set.mem_ofPred_eq]

theorem meetNeed (A : Finset VV) : Meet (inputs 8) (need A) := by
  induction A using Finset.induction_on with
  | empty => simpa [need] using (Meet.top : Meet (inputs 8) Set.univ)
  | @insert v s hv ih =>
    have eq : need (insert v s) = var v ∩ need s := by
      ext u; exact Finset.insert_subset_iff
    rw [eq]; exact Meet.inter (Meet.atom ⟨v,rfl⟩) ih
def coreM (d : DNF) : M := d.foldl (· &&& ·) (-1)
def freeD (d aux : DNF) := d.isEmpty || eqD d [coreM d] || eqD d (times (coreM d) aux)
theorem freeD_sound {d aux : DNF} {B : Set (Sig 8)} (raw : inputs 8⊆B)
    (extra : Meet B (sig aux)) (h : freeD d aux) : Meet B (sig d) := by
  simp only [freeD,Bool.or_eq_true] at h
  rcases h with (he|he)|he
  · cases d with
    | nil => simpa using (Meet.bot : Meet B ∅)
    | cons a d => simp at he
  · rw [eqD_sound he,sig_one]
    exact weaken raw (meetNeed _)
  · rw [eqD_sound he,sig_times]
    exact Meet.inter (weaken raw (meetNeed _)) extra

def termD (d : DNF) (a : M) (use : Bool) := if use then times a d else [a]
theorem termMeet (d : DNF) (a : M) (use : Bool) :
    Meet (insert (sig d) (inputs 8)) (sig (termD d a use)) := by
  have raw := weaken (Set.subset_insert (sig d) (inputs 8)) (meetNeed (decM a))
  cases use
  · simpa [termD] using raw
  · simpa [termD] using raw.inter (Meet.atom (Set.mem_insert _ _))

theorem termsCover {d : DNF} {g : Sig 8} (h : Meet (insert (sig d) (inputs 8)) g) :
    g=∅ ∨ ∃ (a : M) (use : Bool), g=sig (termD d a use) := by
  have hh : g=∅ ∨ ∃(A : Finset VV) (use : Bool), g=need A ∩ (if use then sig d else Set.univ) := by
    induction h with
    | atom hmem =>
      rcases Set.mem_insert_iff.mp hmem with rfl|⟨v,rfl⟩
      · right; exact ⟨∅,true,by ext s; simp [need]⟩
      · right; exact ⟨{v},false,by ext s; simp [need,var]⟩
    | top => right; exact ⟨∅,false,by ext s; simp [need]⟩
    | bot => exact Or.inl rfl
    | inter _ _ ia ib =>
      rcases ia with rfl|⟨A,i,rfl⟩
      · exact Or.inl (Set.empty_inter _)
      rcases ib with rfl|⟨B,j,rfl⟩
      · exact Or.inl (Set.inter_empty _)
      right; refine ⟨A∪B,i||j,?_⟩
      cases i <;> cases j <;> ext s <;> simp [need,Finset.union_subset_iff] <;> tauto
  rcases hh with h|⟨A,i,h⟩
  · exact Or.inl h
  · right; refine ⟨encM A,i,?_⟩
    cases i <;> simpa [termD,dec_enc] using h
end PEqualNP.Outside.L_meta_724_aux.OrCost

/-! A probe is a rejecting input that becomes accepting when one vertex is turned on. If the gates already built agree on the probe pair, a later OR must disappear. -/

namespace PEqualNP.Outside.L_meta_724_aux
open OrCost
abbrev ALL : Vertices := Finset.univ
abbrev Target : Sig 8 := edge (induced ALL)
abbrev Raw : Set (Sig 8) := inputs 8
def degreeV (v : V8) := if v.val<2 then 3 else 2
theorem degreeV_ok : ∀v, dg ALL v=degreeV v := by decide +kernel
theorem ec_full : ec ALL=9 := by decide +kernel
def bitV (v : V8) : M := (1:M) <<< v.val
theorem dec_bitV : ∀v, decM (bitV v)={v} := by decide +kernel
theorem insMask (v : V8) (s : M) : decM (s ||| bitV v)=insert v (decM s) := by
  rw [dec_or,dec_bitV,Finset.union_comm]; simp

def edgeDs : DNF := [3,6,12,24,17,34,96,192,129]
def validProbe (v : V8) (x : M) :=
  evalD edgeDs (x ||| bitV v) && !evalD edgeDs x
theorem evalTarget : ∀x : M, evalD edgeDs x=true ↔
    ∃a b : V8, (induced ALL).Adj a b ∧ a∈decM x ∧ b∈decM x := by decide +kernel
theorem probeTarget {v : V8} {x : M} (h : validProbe v x) :
    insert v (decM x)∈Target ∧ decM x∉Target := by
  have ⟨hp,hq⟩ : evalD edgeDs (x ||| bitV v)=true ∧ evalD edgeDs x=false := by
    simpa only [validProbe,Bool.and_eq_true,Bool.not_eq_true'] using h
  have hp' := (evalTarget _).mp hp
  rw [insMask] at hp'
  exact ⟨hp',fun hx => Bool.noConfusion (hq.symm.trans ((evalTarget _).mpr hx))⟩

def goodD (d : DNF) (v : V8) (x : M) :=
  (prD v d).isEmpty || (evalD d (x ||| bitV v) == evalD d x)
theorem goodD_ok {d : DNF} {v : V8} {x : M} (h : goodD d v x) :
    Good (erase v) (insert v (decM x)) (decM x) (sig d) := by
  simp only [goodD,Bool.or_eq_true,beq_iff_eq] at h
  rcases h with he|he
  · right; rw [←sig_pr]
    cases hh : prD v d with
    | nil => exact sig_nil
    | cons a t => simp [hh] at he
  · left
    rw [←insMask,←match_iff,←match_iff,he]

theorem projLower (v : V8) {i : Nat} (program : Run Raw i (erase v ⁻¹' Target)) :
    8 ≤ i + degreeV v := by
  rw [prEdge,delete_eq] at program
  have lower := residualLower (ALL.erase v) i (properErase ALL v) ⟨i,le_rfl,program⟩
  have count := counting ALL v
  rw [degreeV_ok,ec_full] at count
  omega
theorem targetBad {v : V8} {x : M} (ok : validProbe v x) :
    ¬Good (erase v) (insert v (decM x)) (decM x) Target := by
  obtain ⟨yes,no⟩ := probeTarget ok
  rcases edgeExists (ALL.erase v) (by
      have count := counting ALL v
      rw [degreeV_ok,ec_full] at count
      unfold degreeV at count; split at count <;> omega) with ⟨i,j,adj⟩
  rw [←delete_eq] at adj
  obtain ⟨hw,hi,hj⟩ := SimpleGraph.deleteIncidenceSet_adj.mp adj
  exact fun bad => bad.elim (fun ih => no (ih.mp yes)) (hasSurvivor hw hi hj)

structure Sim (v : V8) (B D : Set (Sig 8)) (r : Nat) : Prop where
  raw : Raw⊆D
  map : ∀z∈B, Meet D (erase v ⁻¹' z)
  back : ∀{k f}, Run D k f → Run Raw (k+r) f

theorem startSim (v : V8) : Sim v Raw Raw 0 :=
  ⟨fun _ h => h,inputMap v,fun h => h⟩
def priceD (v : V8) (aux d : DNF) : Nat := if freeD (prD v d) aux then 0 else 1
def afterD (v : V8) (aux d : DNF) (D : Set (Sig 8)) : Set (Sig 8) :=
  if freeD (prD v d) aux then D else insert (sig (prD v d)) D
theorem extraAfter {v : V8} {aux d : DNF} {D : Set (Sig 8)}
    (hraw : Raw⊆D) (haux : Meet D (sig aux)) :
    Meet (afterD v aux d D) (sig (prD v d)) := by
  unfold afterD; split
  · exact freeD_sound hraw haux ‹_›
  · exact Meet.atom (Set.mem_insert _ _)
theorem advanceSim {v : V8} {aux d : DNF} {B D : Set (Sig 8)} {r : Nat}
    (s : Sim v B D r) (haux : Meet D (sig aux)) {a b : Sig 8}
    (hA : Meet B a) (hB : Meet B b) (eq : sig d = a∪b) :
    Sim v (insert (sig d) B) (afterD v aux d D) (r+priceD v aux d) := by
  have atom := extraAfter (v:=v) (d:=d) s.raw haux
  unfold afterD priceD at *
  by_cases hf : freeD (prD v d) aux=true
  · simp only [hf,ite_true,Nat.add_zero] at atom ⊢
    refine ⟨s.raw,?_,s.back⟩
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl|hz
    · rwa [←sig_pr]
    · exact s.map z hz
  · simp only [hf] at atom ⊢
    have ha := mapMeet (erase v) s.map hA
    have hb := mapMeet (erase v) s.map hB
    have pr : sig (prD v d) = (erase v ⁻¹' a)∪(erase v ⁻¹' b) := by rw [sig_pr,eq,Set.preimage_union]
    refine ⟨s.raw.trans (Set.subset_insert _ _),?_,?_⟩
    · intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl|hz
      · rwa [←sig_pr]
      · exact weaken (Set.subset_insert _ _) (s.map z hz)
    · intro k f tail
      rw [pr] at tail
      have h := s.back (Run.add ha hb tail)
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem simLower {v : V8} {B D : Set (Sig 8)} {j k : Nat} (h : Sim v B D j)
    (tail : Run B k Target) : 8≤ k+j+degreeV v :=
  projLower v (h.back (freeMap (erase v) h.map tail))
theorem simPaid {v : V8} {B D : Set (Sig 8)} {j k : Nat} {x : M}
    (h : Sim v B D j) (valid : validProbe v x)
    (good : ∀z∈B,Good (erase v) (insert v (decM x)) (decM x) z)
    (tail : Run B k Target) : 9≤k+j+degreeV v := by
  obtain ⟨i,hi,p⟩ := paidMap (erase v) (insert v (decM x)) (decM x) h.map good tail (targetBad valid)
  have := projLower v (h.back p)
  omega

theorem sevenLower {k} (p : Run Raw k Target) : 7≤k := by
  have := simPaid (v:=2) (x:=2) (startSim 2) (by decide +kernel) (inputGood 2 _) p
  have d : degreeV 2=2 := rfl
  omega
end PEqualNP.Outside.L_meta_724_aux

/-! These fixed probes certify a removable OR after one or two instructions. -/

namespace PEqualNP.Outside.L_meta_724_aux
open OrCost
def specials : List DNF := [[1,2],[3,4],[3,8],[3,16],[3,32],[3,64],[3,128]]
def probes0 : List (V8 × M) := [(3,4),(6,40),(2,66),(5,10),(4,40),(7,68),(2,9),(5,65),(4,5),(7,9),(2,40),(3,5),(3,18),(4,10),(4,65),(4,136),(5,130),(6,33),(6,130),(7,66)]
def probes1 : List (V8 × M) := [(3,4),(6,40),(2,72),(4,72),(5,68),(7,68),(2,18),(5,10),(4,33),(7,9),(0,10),(0,66),(3,18),(6,130),(0,18),(0,130),(1,5),(1,33),(2,9),(4,10),(4,136),(5,65),(5,130),(7,66)]
def probes2 : List (V8 × M) := [(5,2),(6,32),(7,64),(1,68),(0,160),(2,2),(4,33),(3,18),(1,48),(3,5),(0,80),(1,5),(1,132),(3,36),(3,68),(3,132),(4,5),(4,65),(4,136),(5,68),(5,130),(6,36),(7,5)]
def probes3 : List (V8 × M) := [(6,32),(5,2),(7,64),(1,68),(0,160),(3,4),(2,40),(4,5),(2,66),(4,10),(0,10),(0,20),(0,80),(1,132),(2,130),(4,33),(4,65),(4,136),(5,10),(5,130),(6,40),(7,9)]
def probes4 : List (V8 × M) := [(7,1),(6,128),(5,64),(0,48),(1,160),(4,1),(2,66),(3,5),(0,132),(3,18),(0,18),(0,80),(1,68),(2,18),(2,40),(2,130),(3,36),(3,68),(3,132),(5,18),(5,130),(6,48),(7,80)]
def probes5 : List (V8 × M) := [(2,2),(3,4),(4,8),(1,40),(0,20),(5,2),(7,5),(6,130),(1,20),(6,33),(0,136),(1,33),(1,132),(2,18),(2,40),(2,66),(3,36),(3,68),(3,132),(4,33),(4,65),(4,136),(7,33)]
def probes6 : List (V8 × M) := [(3,4),(2,2),(4,8),(1,40),(0,20),(6,32),(5,68),(7,5),(5,10),(7,66),(0,48),(0,66),(0,136),(1,20),(2,18),(2,66),(3,68),(3,132),(4,33),(4,65),(4,136),(5,130)]
def probes7 : List (V8 × M) := [(4,1),(3,16),(2,8),(0,132),(1,20),(7,1),(5,10),(6,33),(0,48),(6,130),(0,130),(0,136),(1,40),(2,18),(2,40),(2,66),(2,130),(3,68),(3,132),(4,33),(4,65),(4,136),(5,130)]
def oneCase (d : DNF) (q : V8 × M) : Bool :=
  let v:=q.1
  let r:=priceD v [] d
  decide (r+degreeV v≤1) || (goodD d v q.2 && decide (r+degreeV v≤2))
def twoCase (g d : DNF) (q : V8 × M) : Bool :=
  let v:=q.1
  let r:=priceD v [] g+priceD v (prD v g) d
  decide (r+degreeV v≤2) || (goodD g v q.2 && goodD d v q.2 && decide (r+degreeV v≤3))
def firstCheck (a b : M) : Bool :=
  let d:DNF:=[a,b]
  freeD d [] || specials.any (eqD d) || probes0.any (oneCase d)
def secCheck (g : DNF) (ps : List (V8 × M)) (a b : M) (i j : Bool) : Bool :=
  let d:=termD g a i ++ termD g b j
  freeD d g || ps.any (twoCase g d)
theorem probesValid : ∀q∈probes0++probes1++probes2++probes3++probes4++probes5++probes6++probes7,
    validProbe q.1 q.2=true := by decide +kernel
end PEqualNP.Outside.L_meta_724_aux

/-! Only the empty mask, singleton masks, and graph edges can contribute to any minimal positive input. A monotone program stays exact after replacing a redundant OR by its surviving operand. -/

namespace PEqualNP.Outside.L_meta_724_aux
open OrCost

def Up (f : Sig 8) : Prop := ∀ ⦃s t⦄, s ⊆ t → s ∈ f → t ∈ f
def BasisUp (B : Set (Sig 8)) : Prop := ∀ f∈B, Up f

theorem upMeet {B f} (base : BasisUp B) (m : Meet B f) : Up f := by
  induction m with
  | atom h => exact base _ h
  | top => intro s t st h; exact Set.mem_univ _
  | bot => intro s t st h; exact h.elim
  | inter _ _ l r => intro s t st h; exact ⟨l st h.1,r st h.2⟩

theorem upRun {B f k} (base : BasisUp B) (run : Run B k f) : Up f := by
  induction run with
  | done m => exact upMeet base m
  | @add B a b k f ha hb _ ih =>
    apply ih
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl|hz
    · intro s t st h
      exact h.elim (fun x => Or.inl (upMeet base ha st x)) (fun x => Or.inr (upMeet base hb st x))
    · exact base _ hz

theorem upInputs : BasisUp Raw := by
  rintro _ ⟨v,rfl⟩ s t st h
  exact st h
theorem upDNF (d : DNF) : BasisUp (insert (sig d) Raw) := by
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl|hz
  · rintro s t st ⟨a,ha,h⟩
    exact ⟨a,ha,h.trans st⟩
  · exact upInputs _ hz

/-- Shrinking a wire may discard values away from the minimal positive inputs. -/
def OnEdges (f g : Sig 8) : Prop := f⊆g ∧ ∀u v, (induced ALL).Adj u v →
    ({u,v} : Vertices)∈g → ({u,v} : Vertices)∈f
theorem onRefl (a : Sig 8) : OnEdges a a := ⟨fun _ h => h,fun _ _ _ h => h⟩
theorem onInter {a b c d : Sig 8} (h : OnEdges a b) (k : OnEdges c d) :
    OnEdges (a∩c) (b∩d) :=
  ⟨fun _ h' => ⟨h.1 h'.1,k.1 h'.2⟩,fun u v e h' => ⟨h.2 u v e h'.1,k.2 u v e h'.2⟩⟩
theorem onUnion {a b c d : Sig 8} (h : OnEdges a b) (k : OnEdges c d) :
    OnEdges (a∪c) (b∪d) :=
  ⟨fun _ h' => h'.elim (fun l => Or.inl (h.1 l)) (fun r => Or.inr (k.1 r)),
    fun u v e h' => h'.elim (fun l => Or.inl (h.2 u v e l)) (fun r => Or.inr (k.2 u v e r))⟩
def Refines (D B : Set (Sig 8)) : Prop := ∀g∈B, ∃f, Meet D f ∧ OnEdges f g
theorem refineMeet {B D g} (h : Refines D B) (m : Meet B g) : ∃f, Meet D f ∧ OnEdges f g := by
  induction m with
  | atom hh => exact h _ hh
  | top => exact ⟨_,.top,onRefl _⟩
  | bot => exact ⟨_,.bot,onRefl _⟩
  | inter _ _ l r =>
    obtain ⟨a,aa,ab⟩ := l
    obtain ⟨b,ba,bb⟩ := r
    exact ⟨_,aa.inter ba,onInter ab bb⟩
theorem refineRun {B D g k} (h : Refines D B) (m : Run B k g) : ∃f, Run D k f ∧ OnEdges f g := by
  induction m generalizing D with
  | done m =>
    obtain ⟨f,hh,e⟩ := refineMeet h m
    exact ⟨f,.done hh,e⟩
  | @add B a b k f ha hb _ ih =>
    obtain ⟨a',aa,ab⟩ := refineMeet h ha
    obtain ⟨b',ba,bb⟩ := refineMeet h hb
    have hr : Refines (insert (a'∪b') D) (insert (a∪b) B) := by
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl|hz
      · exact ⟨_,Meet.atom (Set.mem_insert _ _),onUnion ab bb⟩
      · obtain ⟨c,cc,ce⟩ := h _ hz
        exact ⟨c,weaken (Set.subset_insert _ _) cc,ce⟩
    obtain ⟨f',tail,fe⟩ := ih hr
    exact ⟨f',.add aa ba tail,fe⟩

theorem restoreTarget {f} (up : Up f) (h : OnEdges f Target) : f=Target := by
  apply Set.Subset.antisymm h.1
  rintro s ⟨u,v,e,hu,hv⟩
  have sub : ({u,v} : Vertices) ⊆ s := Finset.insert_subset_iff.mpr ⟨hu,Finset.singleton_subset_iff.mpr hv⟩
  exact up sub (h.2 u v e (two_yes e))

theorem pruneGate {B a b k} (up : BasisUp B) (ma : Meet B a) (near : OnEdges a b)
    (tail : Run (insert b B) k Target) : Run B k Target := by
  have h : Refines B (insert b B) := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl|hz
    · exact ⟨a,ma,near⟩
    · exact ⟨z,Meet.atom hz,onRefl _⟩
  obtain ⟨f,run,fe⟩ := refineRun h tail
  rwa [restoreTarget (upRun up run) fe] at run

def Live (f : Sig 8) := ∃u v, (induced ALL).Adj u v ∧ ({u,v} : Vertices)∈f
theorem bothLive {B a b k} (up : BasisUp B) (ma : Meet B a) (mb : Meet B b)
    (no : ¬Run B k Target) (tail : Run (insert (a∪b) B) k Target) : Live a ∧ Live b := by
  constructor
  · by_contra hn
    apply no
    apply pruneGate up mb _ tail
    exact ⟨Set.subset_union_right,fun u v e h => h.elim (fun l => (hn ⟨u,v,e,l⟩).elim) id⟩
  · by_contra hn
    apply no
    apply pruneGate up ma _ tail
    exact ⟨Set.subset_union_left,fun u v e h => h.elim id (fun r => (hn ⟨u,v,e,r⟩).elim)⟩

def masks : List M := [0,1,2,4,8,16,32,64,128,3,6,12,24,17,34,96,192,129]
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem maskEnum : ∀(a : M) (u v : V8), (induced ALL).Adj u v → decM a⊆{u,v} → a∈masks := by
  decide +kernel
theorem maskNeed {a : M} (h : Live (need (decM a))) : a∈masks := by
  obtain ⟨u,v,uv,e⟩ := h
  exact maskEnum a u v uv e
theorem maskTerm {g : DNF} {a : M} {use : Bool} (h : Live (sig (termD g a use))) : a∈masks := by
  obtain ⟨u,v,uv,e⟩ := h
  apply maskEnum a u v uv
  cases use with
  | false => simpa [termD,need] using e
  | true =>
    have h : ({u,v} : Vertices) ∈ need (decM a) ∩ sig g := by simpa [termD] using e
    exact h.1
end PEqualNP.Outside.L_meta_724_aux

/-! Apply the finite certificates to the initial one or two ORs of an otherwise unrestricted program. -/

namespace PEqualNP.Outside.L_meta_724_aux
open OrCost

theorem unpack {X : Type} {B : Set (Set X)} {k : Nat} {f : Set X}
    (p : Run B (k+1) f) :
    ∃a b, Meet B a ∧ Meet B b ∧ Run (insert (a∪b) B) k f := by
  cases p with
  | add ha hb tail => exact ⟨_,_,ha,hb,tail⟩
theorem bypass {X : Type} {B : Set (Set X)} {k : Nat} {g f : Set X}
    (hg : Meet B g) (p : Run (insert g B) k f) : Run B k f :=
  freeMap id (fun _ hz => (Set.mem_insert_iff.mp hz).elim
    (fun e => e ▸ hg) (fun h => Meet.atom h)) p

theorem valid0 {q} (hq : q∈probes0) : validProbe q.1 q.2 = true :=
  probesValid q (by simp only [List.mem_append]; tauto)
def validList (ps : List (V8 × M)) := ∀q∈ps, validProbe q.1 q.2=true

theorem cutOne {a b : Sig 8} {d : DNF} (ha : Meet Raw a) (hb : Meet Raw b)
    (eq : sig d=a∪b) (tail : Run (insert (sig d) Raw) 6 Target) {q : V8 × M}
    (valid : validProbe q.1 q.2) (cut : oneCase d q) : False := by
  have emptyMeet : Meet Raw (sig []) := by simpa using (Meet.bot : Meet Raw ∅)
  have sim := advanceSim (v:=q.1) (startSim q.1) emptyMeet ha hb eq
  simp only [Nat.zero_add] at sim
  simp only [oneCase,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at cut
  rcases cut with short|⟨agree,short⟩
  · have := simLower sim tail
    omega
  · have good : ∀z∈insert (sig d) Raw, Good (erase q.1) (insert q.1 (decM q.2)) (decM q.2) z := by
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl|hz
      · exact goodD_ok agree
      · exact inputGood q.1 _ z hz
    have := simPaid sim valid good tail
    omega

theorem cutTwo {a b c e : Sig 8} {g d : DNF}
    (ha : Meet Raw a) (hb : Meet Raw b) (eqg : sig g=a∪b)
    (hc : Meet (insert (sig g) Raw) c) (he : Meet (insert (sig g) Raw) e)
    (eqd : sig d=c∪e) (tail : Run (insert (sig d) (insert (sig g) Raw)) 5 Target) {q : V8 × M}
    (valid : validProbe q.1 q.2) (cut : twoCase g d q) : False := by
  have emptyMeet : Meet Raw (sig []) := by simpa using (Meet.bot : Meet Raw ∅)
  have s1 := advanceSim (v:=q.1) (startSim q.1) emptyMeet ha hb eqg
  have extra := extraAfter (v:=q.1) (d:=g) (D:=Raw) (fun _ hz => hz) emptyMeet
  have s2 := advanceSim s1 extra hc he eqd
  simp only [Nat.zero_add] at s2
  simp only [twoCase,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at cut
  rcases cut with short|⟨⟨ag,ad⟩,short⟩
  · have := simLower s2 tail
    omega
  · have good : ∀z∈insert (sig d) (insert (sig g) Raw),
        Good (erase q.1) (insert q.1 (decM q.2)) (decM q.2) z := by
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl|hz
      · exact goodD_ok ad
      rcases Set.mem_insert_iff.mp hz with rfl|hz
      · exact goodD_ok ag
      · exact inputGood q.1 _ z hz
    have := simPaid s2 valid good tail
    omega

def GivenSeconds (g : DNF) :=
  ∃ ps : List (V8 × M), validList ps ∧ ∀a∈masks, ∀b∈masks, ∀i j : Bool, secCheck g ps a b i j=true

theorem cannotSeven
    (first : ∀a∈masks, ∀b∈masks, firstCheck a b=true)
    (second : ∀g∈specials, GivenSeconds g) (program : Run Raw 7 Target) : False := by
  obtain ⟨a,b,ha,hb,tail⟩ := unpack (k:=6) program
  have no6 (p : Run Raw 6 Target) : False := by have := sevenLower p; omega
  have ⟨alive,blive⟩ := bothLive upInputs ha hb no6 tail
  have red (h : Meet Raw (a∪b)) := no6 (bypass h tail)
  rcases raw_meets ha with rfl|⟨A,rfl⟩
  · exact red (by simpa using hb)
  rcases raw_meets hb with rfl|⟨B,rfl⟩
  · exact red (by simpa using ha)
  let aM := encM A;let bM := encM B
  let d : DNF := [aM,bM]
  have deq : sig d=need A∪need B := by
    simpa [d,aM,bM,dec_enc] using (sig_append [encM A] [encM B])
  rw [←deq] at tail
  have am : aM∈masks := maskNeed (by simpa [aM,dec_enc] using alive)
  have bm : bM∈masks := maskNeed (by simpa [bM,dec_enc] using blive)
  have yes := first aM am bM bm
  change (freeD d [] || specials.any (eqD d) || probes0.any (oneCase d)) = true at yes
  simp only [Bool.or_eq_true,List.any_eq_true] at yes
  rcases yes with (free|⟨g,hg,hEq⟩)|⟨q,hq,hcut⟩
  · exact no6 (bypass (freeD_sound (fun _ hz => hz)
      (by simpa using (Meet.bot : Meet Raw ∅)) free) tail)
  · have sd := eqD_sound hEq
    have geq : sig g=need A∪need B := sd.symm.trans deq
    rw [sd] at tail
    obtain ⟨ps,valid,checks⟩ := second g hg
    obtain ⟨c,e,hc,he,rest⟩ := unpack (k:=5) tail
    have no5 (p : Run (insert (sig g) Raw) 5 Target) : False := by
      rw [geq] at p
      exact no6 (Run.add ha hb p)
    have red2 (h : Meet (insert (sig g) Raw) (c∪e)) := no5 (bypass h rest)
    have ⟨clive,elive⟩ := bothLive (upDNF g) hc he no5 rest
    rcases termsCover hc with rfl|⟨C,i,rfl⟩
    · exact red2 (by simpa using he)
    rcases termsCover he with rfl|⟨E,j,rfl⟩
    · exact red2 (by simpa using hc)
    let m := termD g C i ++ termD g E j
    have meq : sig m = sig (termD g C i)∪sig (termD g E j) := sig_append _ _
    rw [←meq] at rest
    have yes2 := checks C (maskTerm clive) E (maskTerm elive) i j
    change (freeD m g || ps.any (twoCase g m))=true at yes2
    simp only [Bool.or_eq_true,List.any_eq_true] at yes2
    rcases yes2 with free|⟨q,hq,pay⟩
    · apply no5; apply bypass _ rest
      exact freeD_sound (Set.subset_insert _ _) (Meet.atom (Set.mem_insert _ _)) free
    · exact cutTwo ha hb geq hc he meq rest (valid q hq) pay
  · exact cutOne ha hb deq tail (valid0 hq) hcut
end PEqualNP.Outside.L_meta_724_aux

namespace PEqualNP.Outside.L_meta_724_aux
open OrCost
def natEdges : List (Nat×Nat) := [(0,1),(1,2),(2,3),(3,4),(4,0),(1,5),(5,6),(6,7),(7,0)]
theorem listOK : ∀ u v : V8, (u.val,v.val)∈natEdges ↔ (u,v)∈listed := by decide +kernel
theorem recordedOfChecks (first : ∀a∈masks, ∀b∈masks, firstCheck a b=true)
    (second : ∀g∈specials, GivenSeconds g) :
    ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
    (∃ A : Finset ℕ, A.card ≤ 7 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → j ∈ A) ∧
    (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8,
      (u.val, v.val) ∈ ([(0,1),(1,2),(2,3),(3,4),(4,0),(1,5),(5,6),(6,7),(7,0)] : List (ℕ × ℕ))
      ∧ x u = true ∧ x v = true)) := by
  rintro ⟨C,legal,⟨A,cap,allows⟩,he⟩
  have computes (x : V8 → Bool) : C.eval (List.ofFn x)=true ↔
      ∃u v, (induced ALL).Adj u v ∧ x u=true ∧ x v=true := by
    rw [he x]
    constructor
    · rintro ⟨u,v,edge,hu,hv⟩
      exact ⟨u,v,⟨Finset.mem_univ _,Finset.mem_univ _,Or.inl ((listOK u v).mp edge)⟩,hu,hv⟩
    · rintro ⟨u,v,⟨_,_,h|h⟩,hu,hv⟩
      · exact ⟨u,v,(listOK u v).mpr h,hu,hv⟩
      · exact ⟨v,u,(listOK v u).mpr h,hv,hu⟩
  obtain ⟨k,hk,run⟩ := ofCircuit (induced ALL) C A legal computes allows
  have low := sevenLower run
  have eq : k=7 := by omega
  subst k
  exact cannotSeven first second run
end PEqualNP.Outside.L_meta_724_aux

/-! The kernel checks 18 squared first-operand pairs and four times 18 squared second-operand pairs for each of the seven exceptional first gates. -/

namespace PEqualNP.Outside.L_meta_724_aux
open OrCost

def pairTable (f : M → M → Bool) := masks.all fun a => masks.all fun b => f a b
theorem pairTable_sound {f : M → M → Bool} (h : pairTable f=true) :
    ∀a∈masks, ∀b∈masks, f a b=true := by
  intro a ha b hb
  exact List.all_eq_true.mp (List.all_eq_true.mp h a ha) b hb

def flags (f : Bool → Bool → Bool) := f false false && f false true && f true false && f true true
theorem flags_sound {f : Bool → Bool → Bool} (h : flags f=true) (i j : Bool) : f i j=true := by
  simp only [flags,Bool.and_eq_true] at h
  cases i <;> cases j <;> tauto

def rows : List (DNF × List (V8 × M)) :=
  [([1,2],probes1),([3,4],probes2),([3,8],probes3),([3,16],probes4),
   ([3,32],probes5),([3,64],probes6),([3,128],probes7)]
def byFirst (g : DNF) (ps : List (V8 × M)) (a : M) :=
  masks.all fun b => flags (secCheck g ps a b)
def rowCheck (r : DNF × List (V8 × M)) :=
  (r.2.all fun q => validProbe q.1 q.2) && masks.all (byFirst r.1 r.2)

section CertificateTables
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem firstTable : pairTable firstCheck=true := by decide +kernel

def block0 : List M := [0,1,2]
def block1 : List M := [4,8,16]
def block2 : List M := [32,64,128]
def block3 : List M := [3,6,12]
def block4 : List M := [24,17,34]
def block5 : List M := [96,192,129]

theorem combineRow (g : DNF) (ps : List (V8 × M)) (valid : ps.all (fun q => validProbe q.1 q.2)=true)
    (h0 : block0.all (byFirst g ps)=true)
    (h1 : block1.all (byFirst g ps)=true)
    (h2 : block2.all (byFirst g ps)=true)
    (h3 : block3.all (byFirst g ps)=true)
    (h4 : block4.all (byFirst g ps)=true)
    (h5 : block5.all (byFirst g ps)=true)
    : rowCheck (g,ps)=true := by
  change (ps.all (fun q => validProbe q.1 q.2) && masks.all (byFirst g ps))=true
  rw [valid, Bool.true_and, show masks=block0++block1++block2++block3++block4++block5 from rfl]
  simp only [List.all_append,h0,h1,h2,h3,h4,h5,Bool.true_and]

set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch10 : block0.all (byFirst [1,2] probes1)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch11 : block1.all (byFirst [1,2] probes1)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch12 : block2.all (byFirst [1,2] probes1)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch13 : block3.all (byFirst [1,2] probes1)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch14 : block4.all (byFirst [1,2] probes1)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch15 : block5.all (byFirst [1,2] probes1)=true := by decide +kernel
theorem row1 : rowCheck ([1,2],probes1)=true :=
  combineRow _ _ (by decide +kernel) batch10 batch11 batch12 batch13 batch14 batch15

set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch20 : block0.all (byFirst [3,4] probes2)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch21 : block1.all (byFirst [3,4] probes2)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch22 : block2.all (byFirst [3,4] probes2)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch23 : block3.all (byFirst [3,4] probes2)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch24 : block4.all (byFirst [3,4] probes2)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch25 : block5.all (byFirst [3,4] probes2)=true := by decide +kernel
theorem row2 : rowCheck ([3,4],probes2)=true :=
  combineRow _ _ (by decide +kernel) batch20 batch21 batch22 batch23 batch24 batch25

set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch30 : block0.all (byFirst [3,8] probes3)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch31 : block1.all (byFirst [3,8] probes3)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch32 : block2.all (byFirst [3,8] probes3)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch33 : block3.all (byFirst [3,8] probes3)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch34 : block4.all (byFirst [3,8] probes3)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch35 : block5.all (byFirst [3,8] probes3)=true := by decide +kernel
theorem row3 : rowCheck ([3,8],probes3)=true :=
  combineRow _ _ (by decide +kernel) batch30 batch31 batch32 batch33 batch34 batch35

set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch40 : block0.all (byFirst [3,16] probes4)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch41 : block1.all (byFirst [3,16] probes4)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch42 : block2.all (byFirst [3,16] probes4)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch43 : block3.all (byFirst [3,16] probes4)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch44 : block4.all (byFirst [3,16] probes4)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch45 : block5.all (byFirst [3,16] probes4)=true := by decide +kernel
theorem row4 : rowCheck ([3,16],probes4)=true :=
  combineRow _ _ (by decide +kernel) batch40 batch41 batch42 batch43 batch44 batch45

set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch50 : block0.all (byFirst [3,32] probes5)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch51 : block1.all (byFirst [3,32] probes5)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch52 : block2.all (byFirst [3,32] probes5)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch53 : block3.all (byFirst [3,32] probes5)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch54 : block4.all (byFirst [3,32] probes5)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch55 : block5.all (byFirst [3,32] probes5)=true := by decide +kernel
theorem row5 : rowCheck ([3,32],probes5)=true :=
  combineRow _ _ (by decide +kernel) batch50 batch51 batch52 batch53 batch54 batch55

set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch60 : block0.all (byFirst [3,64] probes6)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch61 : block1.all (byFirst [3,64] probes6)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch62 : block2.all (byFirst [3,64] probes6)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch63 : block3.all (byFirst [3,64] probes6)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch64 : block4.all (byFirst [3,64] probes6)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch65 : block5.all (byFirst [3,64] probes6)=true := by decide +kernel
theorem row6 : rowCheck ([3,64],probes6)=true :=
  combineRow _ _ (by decide +kernel) batch60 batch61 batch62 batch63 batch64 batch65

set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch70 : block0.all (byFirst [3,128] probes7)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch71 : block1.all (byFirst [3,128] probes7)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch72 : block2.all (byFirst [3,128] probes7)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch73 : block3.all (byFirst [3,128] probes7)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch74 : block4.all (byFirst [3,128] probes7)=true := by decide +kernel
set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem batch75 : block5.all (byFirst [3,128] probes7)=true := by decide +kernel
theorem row7 : rowCheck ([3,128],probes7)=true :=
  combineRow _ _ (by decide +kernel) batch70 batch71 batch72 batch73 batch74 batch75

theorem secondTable : rows.all rowCheck=true := by
  simp only [rows,List.all_cons,List.all_nil,row1,row2,row3,row4,row5,row6,row7,Bool.true_and]
end CertificateTables

theorem graphSeconds (g : DNF) (hg : g∈specials) : GivenSeconds g := by
  have h : g∈rows.map Prod.fst := hg
  obtain ⟨⟨g',ps⟩,mem,e⟩ := List.mem_map.mp h
  change g'=g at e
  subst g'
  have eq := List.all_eq_true.mp secondTable _ mem
  simp only [rowCheck,Bool.and_eq_true] at eq
  exact ⟨ps,List.all_eq_true.mp eq.1,fun a ha b hb => flags_sound (pairTable_sound eq.2 a ha b hb)⟩
end PEqualNP.Outside.L_meta_724_aux


open PEqualNP.Outside.L_meta_724_aux in
theorem PEqualNP.Outside.L_meta_724 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (1, 5), (5, 6), (6, 7), (7, 0)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → ∀ A : Finset ℕ, (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → j ∈ A) → 8 ≤ A.card := by
  intro C hmono heval A hA
  by_contra! small
  exact recordedOfChecks (pairTable_sound firstTable) graphSeconds
    ⟨C, hmono, ⟨A, by omega, hA⟩, heval⟩
