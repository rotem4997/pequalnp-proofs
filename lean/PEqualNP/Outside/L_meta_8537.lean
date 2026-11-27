import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8537


open PEqualNP.CircuitLowerBounds

abbrev Pt (n : ℕ) := Fin n
abbrev Wire (n : ℕ) := (Pt n → Bool) → Bool
abbrev Paint (n : ℕ) := Pt n → Pt n → ℕ
def single {n : ℕ} (p : Pt n) : Pt n → Bool := fun i => decide (i=p)
def negRow {n : ℕ} (G : SimpleGraph (Pt n)) [DecidableRel G.Adj] (c : Pt n) : Pt n → Bool :=
  fun i => decide (¬G.Adj c i)
def mono {n : ℕ} (s : Wire n) := ∀ x y : Pt n → Bool,
  (∀ i, x i=true → y i=true) → s x=true → s y=true
def uniform {n : ℕ} (G : SimpleGraph (Pt n)) [DecidableRel G.Adj] (f : Paint n) (s : Wire n) :=
  ∀ c : Pt n, s (negRow G c)=false → ∀ p q : Pt n,
    s (single p)=true → s (single q)=true → f c p=f c q
def mergePaint {n : ℕ} (f : Paint n) (c : Pt n) (a b : ℕ) : Paint n :=
  fun d p => if d=c ∧ f d p=a then b else f d p
def palette {n : ℕ} (U : Finset (Pt n × Pt n)) (f : Paint n) : Finset (Pt n × ℕ) :=
  U.image fun z => (z.1,f z.1 z.2)
def coarser {n : ℕ} (f g : Paint n) := ∀ c p q, f c p=f c q → g c p=g c q
def meetW {n : ℕ} (s t : Wire n) : Wire n := fun x => s x && t x
def joinW {n : ℕ} (s t : Wire n) : Wire n := fun x => s x || t x

lemma valid_neighbor {n} {G : SimpleGraph (Pt n)} [DecidableRel G.Adj] {s : Wire n}
    (m : mono s) {c p} (safe : s (negRow G c)=false) (alive : s (single p)=true) : G.Adj c p := by
  by_contra no
  have up := m (single p) (negRow G c) (by
    intro i yes
    have e : i=p := of_decide_eq_true yes
    simpa only [negRow,e,decide_eq_true_eq] using no) alive
  rw [safe] at up
  contradiction

lemma same_center {n} {G : SimpleGraph (Pt n)} [DecidableRel G.Adj]
    (four : TopForm.NoFourCycle G) {c d p q : Pt n} (two : p≠q)
    (hp : G.Adj c p) (hq : G.Adj c q) (jp : G.Adj d p) (jq : G.Adj d q) : c=d := by
  by_contra ne
  let S := Finset.univ.filter fun i => G.Adj c i ∧ G.Adj d i
  have low : S.card≤1 := four c d ne
  exact two (Finset.card_le_one.mp low p (by simp [S,hp,jp]) q (by simp [S,hq,jq]))

lemma after_merge {n} (f : Paint n) (c : Pt n) (a b : ℕ) :
    coarser f (mergePaint f c a b) := by
  intro d p q eq
  simp [mergePaint,eq]

lemma palette_bound {n} (U : Finset (Pt n × Pt n)) (f : Paint n) (c : Pt n) (a b : ℕ) :
    (palette U f).card ≤ (palette U (mergePaint f c a b)).card+1 := by
  have sub : palette U f ⊆ insert (c,a) (palette U (mergePaint f c a b)) := by
    intro z hz
    obtain ⟨⟨d,p⟩,dp,rfl⟩ := Finset.mem_image.mp hz
    by_cases moved : d=c ∧ f d p=a
    · exact Finset.mem_insert.mpr (Or.inl (Prod.ext moved.1 moved.2))
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨(d,p),dp,by simp [mergePaint,moved]⟩
  exact (Finset.card_le_card sub).trans (Finset.card_insert_le _ _)

lemma and_true {a b : Bool} : (a && b)=true ↔ a=true ∧ b=true := by cases a <;> cases b <;> decide
lemma or_true {a b : Bool} : (a || b)=true ↔ a=true ∨ b=true := by cases a <;> cases b <;> decide

lemma mono_meet {n} {s t : Wire n} (a : mono s) (b : mono t) : mono (meetW s t) := by
  intro x y xy on
  obtain ⟨u,v⟩ : s x=true ∧ t x=true := and_true.mp on
  exact and_true.mpr ⟨a x y xy u,b x y xy v⟩

lemma mono_join {n} {s t : Wire n} (a : mono s) (b : mono t) : mono (joinW s t) := by
  intro x y xy on
  exact or_true.mpr ((or_true.mp on).imp (a x y xy) (b x y xy))

lemma kept {n} {G : SimpleGraph (Pt n)} [DecidableRel G.Adj] {f h : Paint n}
    {s : Wire n} (a : uniform G f s) (larger : coarser f h) : uniform G h s := by
  intro c off p q on other
  exact larger c p q (a c off p q on other)

lemma meet_uniform {n} {G : SimpleGraph (Pt n)} [DecidableRel G.Adj] {f : Paint n}
    {s t : Wire n} (a : uniform G f s) (b : uniform G f t) : uniform G f (meetW s t) := by
  intro c off p q hp hq
  obtain ⟨p1,p2⟩ := and_true.mp hp
  obtain ⟨q1,q2⟩ := and_true.mp hq
  cases left : s (negRow G c) with
  | false => exact a c left p q p1 q1
  | true =>
    have right : t (negRow G c)=false := by simpa [meetW,left] using off
    exact b c right p q p2 q2

lemma two_labels {n} {s t : Wire n} {c : Pt n} {f : Paint n}
    (asame : ∀ p q,s (single p)=true → s (single q)=true → f c p=f c q)
    (bsame : ∀ p q,t (single p)=true → t (single q)=true → f c p=f c q)
    {p q : Pt n} (pon : joinW s t (single p)=true) (qon : joinW s t (single q)=true)
    (ne : f c p≠f c q) : ∀ r, joinW s t (single r)=true → f c r=f c p ∨ f c r=f c q := by
  intro r yes
  rcases or_true.mp pon with p1|p2 <;> rcases or_true.mp qon with q1|q2
  · exact False.elim (ne (asame p q p1 q1))
  · exact (or_true.mp yes).elim (fun h => Or.inl (asame r p h p1)) (fun h => Or.inr (bsame r q h q2))
  · exact (or_true.mp yes).elim (fun h => Or.inr (asame r q h q1)) (fun h => Or.inl (bsame r p h p2))
  · exact False.elim (ne (bsame p q p2 q2))

lemma join_uniform {n} {G : SimpleGraph (Pt n)} [DecidableRel G.Adj] (four : TopForm.NoFourCycle G)
    (U : Finset (Pt n × Pt n)) {f : Paint n} {s t : Wire n} (ms : mono s) (mt : mono t)
    (a : uniform G f s) (b : uniform G f t) : ∃ h : Paint n, coarser f h ∧
    uniform G h (joinW s t) ∧ (palette U f).card≤(palette U h).card+1 := by
  classical
  by_cases good : uniform G f (joinW s t)
  · exact ⟨f,fun c p q e => e,good,by omega⟩
  unfold uniform at good
  push Not at good
  obtain ⟨c,off,p,q,pon,qon,ne⟩ := good
  have both : s (negRow G c)=false ∧ t (negRow G c)=false := by simpa [joinW] using off
  let paint := mergePaint f c (f c p) (f c q)
  refine ⟨paint,after_merge _ _ _ _,?_,palette_bound _ _ _ _ _⟩
  have m := mono_join ms mt
  have apart : p≠q := fun e => ne (congrArg (f c) e)
  have colors := two_labels (a c both.1) (b c both.2) pon qon ne
  have unique (d : Pt n) (d0 : joinW s t (negRow G d)=false) : c=d :=
    same_center four apart (valid_neighbor m off pon) (valid_neighbor m off qon)
      (valid_neighbor m d0 pon) (valid_neighbor m d0 qon)
  have paint_eq (r : Pt n) (hr : joinW s t (single r)=true) : paint c r=f c q := by
    rcases colors r hr with left|right
    · simp [paint,mergePaint,left]
    · simp [paint,mergePaint,right,Ne.symm ne]
  intro d hz r k hr hk
  obtain rfl := unique d hz
  exact (paint_eq r hr).trans (paint_eq k hk).symm




open PEqualNP.CircuitLowerBounds

def zeroS {n} : Wire n := fun _ => false
def nextS {n} (xs : List (Wire n)) (g : Gate) : Wire n := fun x =>
  g.op.eval (g.inputs.map fun i => (xs.getD i zeroS) x)
def snocS {n} (xs : List (Wire n)) (g : Gate) : List (Wire n) := xs ++ [nextS xs g]
def startS (n : ℕ) : List (Wire n) := List.ofFn fun i : Fin n => fun x => x i
def allS (n : ℕ) (C : Circuit) := C.gates.foldl snocS (startS n)
def fee (g : Gate) : ℕ := match g.op with | .or => 1 | _ => 0
def fees : List Gate → ℕ
  | [] => 0
  | g::gs => fee g + fees gs

lemma lookup {n} (xs : List (Wire n)) (x : Pt n → Bool) (i : ℕ) :
    (xs.map fun s => s x).getD i false = (xs.getD i zeroS) x := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases xs[i]? <;> rfl

lemma eval_all {n} (gs : List Gate) (xs : List (Wire n)) (x : Pt n → Bool) :
    (gs.foldl snocS xs).map (fun s => s x) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (xs.map fun s => s x) := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    simp only [snocS,nextS,List.map_append,List.map_singleton,lookup]

lemma final_value {n} (C : Circuit) (k : ℕ) (x : Pt n → Bool) :
    ((allS n C).getD k zeroS) x = CleanedNonEdge.wireVal n C k x := by
  rw [←lookup,allS,eval_all]
  simp [CleanedNonEdge.wireVal,Circuit.wires,startS,List.map_ofFn,Function.comp_def]

lemma good_lookup {n} {G : SimpleGraph (Pt n)} [DecidableRel G.Adj] {f : Paint n}
    {xs : List (Wire n)} (ok : ∀ s∈xs, mono s ∧ uniform G f s) (i : ℕ) :
    mono (xs.getD i zeroS) ∧ uniform G f (xs.getD i zeroS) := by
  rw [List.getD_eq_getElem?_getD]
  cases eq : xs[i]? with
  | some s => exact ok s (List.mem_of_getElem? eq)
  | none => exact ⟨by intro x y le h; contradiction, by intro c neg p q hp; contradiction⟩

lemma one_gate {n} {G : SimpleGraph (Pt n)} [DecidableRel G.Adj] (four : TopForm.NoFourCycle G)
    (U : Finset (Pt n × Pt n)) {f : Paint n} {xs : List (Wire n)}
    (ok : ∀ s∈xs, mono s ∧ uniform G f s) (g : Gate)
    (op : g.op=.and ∨ g.op=.or) (arity : g.inputs.length=2) :
    ∃ h : Paint n, coarser f h ∧ (mono (nextS xs g) ∧ uniform G h (nextS xs g)) ∧
      (palette U f).card ≤ (palette U h).card + fee g := by
  rcases g with ⟨opn,inputs⟩
  change inputs.length=2 at arity
  obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp arity
  obtain ⟨ma,ua⟩ := good_lookup ok a
  obtain ⟨mb,ub⟩ := good_lookup ok b
  change opn=.and ∨ opn=.or at op
  rcases op with rfl|rfl
  · have meaning : nextS xs ⟨.and,[a,b]⟩ = meetW (xs.getD a zeroS) (xs.getD b zeroS) := by
      funext x
      simp [nextS,meetW,GateOp.eval]
    exact ⟨f,fun _ _ _ e => e,meaning ▸ ⟨mono_meet ma mb,meet_uniform ua ub⟩,by simp [fee]⟩
  · have meaning : nextS xs ⟨.or,[a,b]⟩ = joinW (xs.getD a zeroS) (xs.getD b zeroS) := by
      funext x
      simp [nextS,joinW,GateOp.eval]
    obtain ⟨h,joins,good,bound⟩ := join_uniform four U ma mb ua ub
    exact ⟨h,joins,meaning ▸ ⟨mono_join ma mb,good⟩,bound⟩

lemma program {n} {G : SimpleGraph (Pt n)} [DecidableRel G.Adj] (four : TopForm.NoFourCycle G)
    (U : Finset (Pt n × Pt n)) (gs : List Gate) (xs : List (Wire n)) (f : Paint n)
    (law : ∀ g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2)
    (ok : ∀ s∈xs, mono s ∧ uniform G f s) :
    ∃ h : Paint n, (∀ s∈gs.foldl snocS xs, mono s ∧ uniform G h s) ∧
      (palette U f).card ≤ (palette U h).card + fees gs := by
  induction gs generalizing xs f with
  | nil => exact ⟨f,ok,by simp [fees]⟩
  | cons g gs ih =>
    obtain ⟨leg,arity⟩ := law g (by simp)
    obtain ⟨h,wide,good,bill⟩ := one_gate four U ok g leg arity
    have nextOk : ∀ s∈snocS xs g, mono s ∧ uniform G h s := by
      intro s hs
      rcases List.mem_append.mp hs with previous|fresh
      · exact ⟨(ok s previous).1,kept (ok s previous).2 wide⟩
      · have : s=nextS xs g := by simpa using fresh
        exact this ▸ good
    obtain ⟨finalPaint,finalOk,otherBill⟩ := ih (snocS xs g) h
      (fun a ha => law a (List.mem_cons_of_mem _ ha)) nextOk
    exact ⟨finalPaint,finalOk,by simp only [fees]; omega⟩

def initial {n : ℕ} : Paint n := fun _ p => p.val

lemma initial_ok {n} (G : SimpleGraph (Pt n)) [DecidableRel G.Adj] :
    ∀ s∈startS n, mono s ∧ uniform G initial s := by
  intro s hs
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hs
  rw [←hi]
  constructor
  · intro x y xy pos
    exact xy i pos
  · intro c neg p q hp hq
    have ip : i=p := of_decide_eq_true hp
    have iq : i=q := of_decide_eq_true hq
    rw [←ip,←iq]

lemma initial_card {n} (U : Finset (Pt n × Pt n)) : (palette U initial).card=U.card := by
  apply Finset.card_image_of_injective
  intro a b eq
  apply Prod.ext
  · exact congrArg (fun z : Pt n × ℕ => z.1) eq
  · exact Fin.ext (congrArg (fun z : Pt n × ℕ => z.2) eq)

def andFee (g : Gate) : ℕ := match g.op with | .and => 1 | _ => 0

lemma sum_fees (gs : List Gate) : (∑ i : Fin gs.length, fee (gs.get i))=fees gs := by
  induction gs with
  | nil => simp [fees]
  | cons g gs ih =>
    change (∑ i : Fin (gs.length+1), fee ((g::gs).get i)) = _
    rw [Fin.sum_univ_succ]
    simpa [fees] using congrArg (fee g + ·) ih

lemma gate_budget (C : Circuit) (K : Finset (Fin C.size))
    (eligible : ∀ g∈K, (C.gates.get g).op=.and) : K.card + fees C.gates ≤ C.size := by
  have one (j) (hj : j∈K) : andFee (C.gates.get j)=1 := by simp [andFee,eligible j hj]
  have members : K.card = ∑ j∈K, andFee (C.gates.get j) := by
    rw [Finset.sum_congr rfl one]
    simp
  have sub : (∑ j∈K, andFee (C.gates.get j)) ≤ ∑ j : Fin C.size, andFee (C.gates.get j) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ K) (by intros; omega)
  rw [members,←sum_fees]
  calc
    _ ≤ (∑ j : Fin C.size, andFee (C.gates.get j)) + ∑ j : Fin C.size, fee (C.gates.get j) :=
      Nat.add_le_add_right sub _
    _ = ∑ j : Fin C.size, (andFee (C.gates.get j)+fee (C.gates.get j)) := Finset.sum_add_distrib.symm
    _ ≤ ∑ _j : Fin C.size, 1 := by
      apply Finset.sum_le_sum
      intro j hj
      cases h : (C.gates.get j).op <;> simp [andFee,fee,h]
    _ = C.size := by simp




open PEqualNP.CircuitLowerBounds

lemma color_cap {n k} (G : SimpleGraph (Pt n)) [DecidableRel G.Adj] (f : Paint n)
    (center : Fin k → Pt n) (read : Fin k → Wire n) (K : Finset (Fin k))
    (U : Finset (Pt n × Pt n))
    (covers : ∀ c p, (c,p)∈U → ∃ j∈K, center j=c ∧ read j (single p)=true)
    (ok : ∀ j, uniform G f (read j)) (safe : ∀ j∈K, read j (negRow G (center j))=false) :
    (palette U f).card ≤ K.card := by
  classical
  let repr (j : Fin k) : Pt n × ℕ := (center j,
    if ex : ∃ p : Pt n, read j (single p)=true then f (center j) (Classical.choose ex) else 0)
  have sub : palette U f ⊆ K.image repr := by
    intro z hz
    obtain ⟨⟨c,p⟩,hu,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨j,jk,rfl,on⟩ := covers c p hu
    have ex : ∃ t : Pt n, read j (single t)=true := ⟨p,on⟩
    apply Finset.mem_image.mpr
    refine ⟨j,jk,?_⟩
    simp only [repr,dite_eq_left ex]
    exact congrArg (Prod.mk (center j))
      (ok j (center j) (safe j jk) _ _ (Classical.choose_spec ex) on)
  exact (Finset.card_le_card sub).trans Finset.card_image_le

lemma pair_single {n} (p : Pt n) : EdgeOwnership.pairInput p p = single p := by
  funext i
  simp [EdgeOwnership.pairInput,single]

theorem result (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (four : TopForm.NoFourCycle G) (ao : TopForm.IsAO2 n C)
    (center : Fin C.size → Fin n) (wire : Fin C.size → ℕ) (K : Finset (Fin C.size))
    (eligible : ∀ j∈K, (C.gates.get j).op=.and ∧ ∀ x : Fin n → Bool,
      x (center j)=true → CleanedNonEdge.wireVal n C (wire j) x=true →
      MetaComplexity.NestedCover.graphFun G ∅ x=true)
    (safe : ∀ j∈K, CleanedNonEdge.wireVal n C (wire j) (fun i => decide (¬G.Adj (center j) i))=false) :
    {e∈G.edgeFinset | ∃ j∈K, ∃ p : Fin n, e=s(center j,p) ∧
      CleanedNonEdge.wireVal n C (wire j) (EdgeOwnership.pairInput p p)=true}.card ≤ C.size := by
  classical
  let read (j : Fin C.size) : Wire n := (allS n C).getD (wire j) zeroS
  let U : Finset (Pt n × Pt n) := Finset.univ.filter fun z =>
    ∃ j∈K, center j=z.1 ∧ read j (single z.2)=true
  have memU (c p : Pt n) : (c,p)∈U ↔ ∃ j∈K, center j=c ∧ read j (single p)=true := by
    simp [U]
  have projected :
      {e∈G.edgeFinset | ∃ j∈K, ∃ p : Fin n, e=s(center j,p) ∧
        CleanedNonEdge.wireVal n C (wire j) (EdgeOwnership.pairInput p p)=true}
      ⊆ U.image (fun z => s(z.1,z.2)) := by
    intro e he
    obtain ⟨j,hj,p,rfl,hp⟩ := (Finset.mem_filter.mp he).2
    apply Finset.mem_image.mpr
    refine ⟨(center j,p),(memU _ _).mpr ⟨j,hj,rfl,?_⟩,rfl⟩
    simpa only [read,final_value,pair_single] using hp
  obtain ⟨f,done,bill⟩ := program four U C.gates (startS n) initial
    (fun g hg => ⟨ao.1 g hg,ao.2.2 g hg⟩) (initial_ok G)
  have cap := color_cap G f center read K U (fun c p => (memU c p).mp) (fun j => (good_lookup done (wire j)).2)
    (by
      intro j hj
      change ((allS n C).getD (wire j) zeroS) (negRow G (center j))=false
      rw [final_value]
      exact safe j hj)
  have edges := (Finset.card_le_card projected).trans Finset.card_image_le
  have count := gate_budget C K (fun j hj => (eligible j hj).1)
  rw [initial_card] at bill
  omega


end PEqualNP.Outside.L_meta_8537

theorem PEqualNP.Outside.L_meta_8537 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsAO2 x1 x4 → ∀ (x7 : Fin x4.size → Fin x1) (x8 : Fin x4.size → ℕ) (x9 : Finset (Fin x4.size)), (∀ x10 ∈ x9, (x4.gates.get x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∀ (x12 : Fin x1 → Bool), x12 (x7 x10) = Bool.true → PEqualNP.CleanedNonEdge.wireVal x1 x4 (x8 x10) x12 = Bool.true → PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ x12 = Bool.true) → (∀ x11 ∈ x9, (PEqualNP.CleanedNonEdge.wireVal x1 x4 (x8 x11) fun (x13 : Fin x1) => Decidable.decide ¬x2.Adj (x7 x11) x13) = Bool.false) → {x12 ∈ x2.edgeFinset | ∃ x13 ∈ x9, ∃ (x14 : Fin x1), x12 = s(x7 x13, x14) ∧ PEqualNP.CleanedNonEdge.wireVal x1 x4 (x8 x13) (PEqualNP.EdgeOwnership.pairInput x14 x14) = Bool.true}.card ≤ x4.size := by
  exact PEqualNP.Outside.L_meta_8537.result
