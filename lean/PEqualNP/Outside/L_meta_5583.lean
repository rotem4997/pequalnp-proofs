import Mathlib
import PEqualNP.Defs

-- Every raw input is needed. Seven binary gates can connect those eight leaves only as a tree.
-- For such a tree the two sides of every gate have disjoint raw supports.
-- The finite checks exclude all monotone splits except the isolated edge at the output.

namespace PEqualNP.Outside.L_meta_5583.Semantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

theorem opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

end PEqualNP.Outside.L_meta_5583.Semantics

namespace PEqualNP.Outside.L_meta_5583

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Represents
open PEqualNP.Outside.L_meta_5583.Semantics (val val_gate val_ofFn val_ge gateAt_mem opMono_imp)

abbrev Wire (C : Circuit) := Fin (8+C.size)

def reads (C : Circuit) (p a : Wire C) : Prop :=
  8 ≤ p.val ∧ a.val < p.val ∧ a.val ∈ (gateAt C (p.val-8)).inputs

abbrev Reach (C : Circuit) := Relation.ReflTransGen (reads C)

abbrev wireVal (C : Circuit) (w : Wire C) (x : Fin 8 → Bool) :=
  val C (List.ofFn x) w.val

def bits (u v : Fin 4) : Fin 8 → Bool :=
  Fin.append (fun i => decide (i=u)) (fun j => decide (j=v))

lemma bits_list (u v : Fin 4) : List.ofFn (bits u v) = oneEach u v := by
  unfold bits oneEach
  rw [List.ofFn_add]
  simp only [Fin.append_left',Fin.append_right]

def A (u v : Fin 4) : Bool := (4813 : ℕ).testBit (4*u.val+v.val)

lemma critical : ∀ i : Fin 8, ∃ u v u' v' : Fin 4,
    A u v = true ∧ A u' v' = false ∧
    ∀ t : Fin 8, t≠i → bits u v t = true → bits u' v' t = true := by
  decide +kernel

theorem order_in_cone (C : Circuit) (mono : Monotone2 C) (root : Wire C)
    (x y : Fin 8 → Bool)
    (order : ∀ t : Fin 8, Reach C root (Fin.castLE (by omega) t) → x t = true → y t = true) :
    wireVal C root x = true → wireVal C root y = true := by
  have go : ∀ w : Wire C, Reach C root w → wireVal C w x = true → wireVal C w y = true := by
    intro w
    induction w using Fin.strong_induction_on with
    | h w ih =>
      intro path on
      by_cases raw : w.val<8
      · let p : Fin 8 := ⟨w.val,raw⟩
        have comp : Fin.castLE (by omega : 8≤8+C.size) p = w := rfl
        change val C (List.ofFn x) p.val = true at on
        rw [val_ofFn] at on
        change val C (List.ofFn y) p.val = true
        rw [val_ofFn]
        exact order p (comp.symm ▸ path) on
      · let j := w.val-8
        have here : 8+j=w.val := by omega
        have hj : j<C.gates.length := by have h := w.isLt; change w.val<8+C.gates.length at h; omega
        have how : (gateAt C j).op = .and ∨ (gateAt C j).op = .or := by
          simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (mono _ (gateAt_mem hj)).1
        change val C (List.ofFn x) w.val = true at on
        change val C (List.ofFn y) w.val = true
        rw [← here,val_gate (by simp) hj] at on ⊢
        apply opMono_imp _ how _ _ _ ?_ on
        intro v mem
        by_cases earlier : v<8+j
        · simp only [earlier,ite_true]
          let child : Wire C := ⟨v,by have h := w.isLt; omega⟩
          have feeds : reads C w child := by
            change 8≤w.val ∧ v<w.val ∧ v ∈ (gateAt C (w.val-8)).inputs
            exact ⟨by omega,by omega,by simpa only [← here,Nat.add_sub_cancel_left] using mem⟩
          exact ih child (by change v<w.val; omega) (path.tail feeds)
        · simp [earlier]
  exact go root Relation.ReflTransGen.refl

theorem every_raw (C : Circuit) (mono : Monotone2 C) (rep : Represents A C)
    (root : Wire C) (output : root.val=C.output) :
    ∀ i : Fin 8, Reach C root (Fin.castLE (by omega) i) := by
  intro i
  by_contra absent
  obtain ⟨u,v,a,b,pos,neg,pattern⟩ := critical i
  have yes : wireVal C root (bits u v) = true := by
    change (⟨C.gates,root.val⟩ : Circuit).eval (List.ofFn (bits u v)) = true
    rw [output,bits_list]
    exact (rep u v).trans pos
  have zero : wireVal C root (bits a b) = false := by
    change (⟨C.gates,root.val⟩ : Circuit).eval (List.ofFn (bits a b)) = false
    rw [output,bits_list]
    exact (rep a b).trans neg
  have bad := order_in_cone C mono root (bits u v) (bits a b)
    (fun t path on => pattern t (fun eq => absent (eq ▸ path)) on) yes
  rw [zero] at bad
  contradiction

def port (C : Circuit) (parent : Wire C) (s : Fin 2) (v : Wire C) : Prop :=
  ((gateAt C (parent.val-8)).inputs)[s.val]? = some v.val ∧ v.val<parent.val

lemma chosen_slot (C : Circuit) (mono : Monotone2 C) {p v : Wire C} (read : reads C p v) :
    ∃ s : Fin 2, port C p s v := by
  obtain ⟨late,earlier,used⟩ := read
  have valid : p.val-8<C.gates.length := by
    have h := p.isLt
    change p.val < 8+C.gates.length at h
    omega
  have length := (mono _ (gateAt_mem valid)).2
  obtain ⟨k,found⟩ := List.mem_iff_getElem?.mp used
  have bound := (List.getElem?_eq_some_iff.mp found).1
  exact ⟨⟨k,by omega⟩,found,earlier⟩

theorem tree_ports (C : Circuit) (mono : Monotone2 C) (small : C.size ≤ 7)
    (root : Wire C) (necessary : ∀ i : Fin 8, Reach C root (Fin.castLE (by omega) i)) :
    (∀ w, Reach C root w → 8≤w.val → ∀ k : Fin 2, ∃ v : Wire C, port C w k v) ∧
    (∀ p q, Reach C root p → Reach C root q → 8≤p.val → 8≤q.val →
      ∀ k l : Fin 2, ∀ v, port C p k v → port C q l v → p=q ∧ k=l) := by
  classical
  let territory : Finset (Wire C) := Finset.univ.filter (fun w => Reach C root w)
  let gates : Finset (Wire C) := territory.filter (fun w => 8≤w.val)
  let others := territory.erase root
  have rootIn : root∈territory := Finset.mem_filter.mpr ⟨Finset.mem_univ _,Relation.ReflTransGen.refl⟩
  have visit (w : Wire C) : w∈territory ↔ Reach C root w := by simp [territory]
  have intoG (w : Wire C) : w∈gates ↔ Reach C root w ∧ 8≤w.val := by simp [gates,visit]
  have select (v : ↥others) : ∃ (g : ↥gates) (k : Fin 2), port C g.val k v.val := by
    obtain ⟨ne,mem⟩ := Finset.mem_erase.mp v.property
    have reach := (visit v.val).mp mem
    obtain ⟨p,prior,step⟩ := reach.cases_tail.resolve_left ne
    obtain ⟨k,hk⟩ := chosen_slot C mono step
    exact ⟨⟨p,(intoG p).mpr ⟨prior,step.1⟩⟩,k,hk⟩
  choose parent slot property using select
  let map (v : ↥others) : ↥gates × Fin 2 := (parent v,slot v)
  have inj : Function.Injective map := by
    intro v w eq
    have p : parent v=parent w := congrArg Prod.fst eq
    have s : slot v=slot w := congrArg Prod.snd eq
    have compare := (property v).1
    rw [p,s,(property w).1] at compare
    exact Subtype.ext (Fin.ext (Option.some.inj compare).symm)
  have count := Fintype.card_le_of_injective map inj
  rw [Fintype.card_prod,Fintype.card_coe,Fintype.card_coe,Fintype.card_fin] at count
  have sub : gates ⊆ territory := Finset.filter_subset _ _
  let raw := (Finset.univ : Finset (Fin 8)).map (Fin.castLEEmb (by omega : 8≤8+C.size))
  have rawEq : territory \ gates = raw := by
    ext w
    constructor
    · intro mem
      obtain ⟨reached,excluded⟩ := Finset.mem_sdiff.mp mem
      have early : w.val<8 := by
        by_contra! late
        exact excluded ((intoG w).mpr ⟨(visit w).mp reached,late⟩)
      exact Finset.mem_map.mpr ⟨⟨w.val,early⟩,Finset.mem_univ _,rfl⟩
    · intro mem
      obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp mem
      exact Finset.mem_sdiff.mpr ⟨(visit _).mpr (necessary i),fun h => (not_le_of_gt i.isLt) ((intoG _).mp h).2⟩
  have rawCard : raw.card = 8 := by simp [raw]
  have partition : territory.card = gates.card+8 := by
    have h := Finset.card_sdiff_add_card_eq_card sub
    rw [rawEq,rawCard] at h
    omega
  have totalOther : others.card+1=territory.card := Finset.card_erase_add_one rootIn
  let gateIndex (g : ↥gates) : Fin C.size :=
    ⟨g.val.val-8,by have v := g.val.isLt; have b := ((intoG _).mp g.property).2; omega⟩
  have gateInj : Function.Injective gateIndex := by
    intro a b eq
    have aGate := ((intoG _).mp a.property).2
    have bGate := ((intoG _).mp b.property).2
    have valEq : a.val.val-8=b.val.val-8 := congrArg Fin.val eq
    exact Subtype.ext (Fin.ext (by omega))
  have bound := Fintype.card_le_of_injective gateIndex gateInj
  rw [Fintype.card_coe,Fintype.card_fin] at bound
  have exactCard : Fintype.card ↥others = Fintype.card (↥gates × Fin 2) := by
    rw [Fintype.card_prod,Fintype.card_coe,Fintype.card_coe,Fintype.card_fin]
    omega
  have surj := ((Fintype.bijective_iff_injective_and_card map).mpr ⟨inj,exactCard⟩).2
  have allSlots (p : ↥gates) (k : Fin 2) :
      ∃ v : ↥others, map v=(p,k) ∧ port C p.val k v.val := by
    obtain ⟨v,eq⟩ := surj (p,k)
    have pp : parent v=p := congrArg Prod.fst eq
    have sk : slot v=k := congrArg Prod.snd eq
    exact ⟨v,eq,pp ▸ sk ▸ property v⟩
  constructor
  · intro w reach late slot
    obtain ⟨u,_,hu⟩ := allSlots ⟨w,(intoG w).mpr ⟨reach,late⟩⟩ slot
    exact ⟨u.val,hu⟩
  · intro p q rp rq ep eq k l v pv qv
    obtain ⟨a,pa,ha⟩ := allSlots ⟨p,(intoG p).mpr ⟨rp,ep⟩⟩ k
    obtain ⟨b,qb,hb⟩ := allSlots ⟨q,(intoG q).mpr ⟨rq,eq⟩⟩ l
    have av : a.val.val=v.val := Option.some.inj (ha.1.symm.trans pv.1)
    have bv : b.val.val=v.val := Option.some.inj (hb.1.symm.trans qv.1)
    have eqAB : a=b := Subtype.ext (Fin.ext (av.trans bv.symm))
    rw [eqAB,qb] at pa
    exact ⟨congrArg (fun w => w.1.val) pa.symm,congrArg Prod.snd pa.symm⟩

end PEqualNP.Outside.L_meta_5583

namespace PEqualNP.Outside.L_meta_5583

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_5583.Semantics (gateAt_mem)

def rawWire {C : Circuit} (i : Fin 8) : Wire C := Fin.castLE (by omega) i

noncomputable def rawLeaves (C : Circuit) (w : Wire C) : Finset (Fin 8) := by
  classical
  exact Finset.univ.filter (fun i => Reach C w (rawWire i))

lemma mem_rawLeaves {C : Circuit} {w : Wire C} {i : Fin 8} :
    i∈rawLeaves C w ↔ Reach C w (rawWire i) := by
  classical
  simp [rawLeaves]

def AllPorts (C : Circuit) (root : Wire C) : Prop :=
  ∀ w, Reach C root w → 8≤w.val → ∀ k : Fin 2, ∃ v : Wire C, port C w k v

def UniquePorts (C : Circuit) (root : Wire C) : Prop :=
  ∀ p q, Reach C root p → Reach C root q → 8≤p.val → 8≤q.val →
     ∀ k l : Fin 2, ∀ v, port C p k v → port C q l v → p=q ∧ k=l

lemma port_read {C : Circuit} {u v : Wire C} {s : Fin 2}
    (late : 8≤u.val) (edge : port C u s v) : reads C u v :=
  ⟨late,edge.2,List.mem_iff_getElem?.mpr ⟨s.val,edge.1⟩⟩

lemma reach_descends {C : Circuit} {a b : Wire C} (run : Reach C a b) : b.val≤a.val := by
  induction run with
  | refl => exact le_rfl
  | tail _ h ih => exact (Nat.le_of_lt h.2.1).trans ih

lemma same_parent {C : Circuit} {root a b v : Wire C} (mono : Monotone2 C)
    (unique : UniquePorts C root) (ha : Reach C root a) (hb : Reach C root b)
    (av : reads C a v) (bv : reads C b v) : a=b := by
  obtain ⟨k,hk⟩ := chosen_slot C mono av
  obtain ⟨l,hl⟩ := chosen_slot C mono bv
  exact (unique a b ha hb av.1 bv.1 k l v hk hl).1

lemma compare_before {C : Circuit} {root : Wire C} (mono : Monotone2 C)
    (unique : UniquePorts C root) (a b t : Wire C)
    (ra : Reach C root a) (rb : Reach C root b)
    (atT : Reach C a t) (btT : Reach C b t) : Reach C a b ∨ Reach C b a := by
  induction atT generalizing b with
  | refl => exact Or.inr btT
  | @tail v t prefixA edgeA ih =>
    rcases btT.cases_tail with same | ⟨u,prefixB,edgeB⟩
    · subst b
      exact Or.inl (prefixA.tail edgeA)
    · have eq := same_parent mono unique (ra.trans prefixA) (rb.trans prefixB) edgeA edgeB
      subst u
      exact ih b rb prefixB

lemma siblings_disjoint {C : Circuit} {root w a b : Wire C}
    (mono : Monotone2 C) (unique : UniquePorts C root) (rootW : Reach C root w)
    (wa : reads C w a) (wb : reads C w b) (distinct : a≠b) :
    Disjoint (rawLeaves C a) (rawLeaves C b) := by
  rw [Finset.disjoint_left]
  intro p ap bp
  have pathA := mem_rawLeaves.mp ap
  have pathB := mem_rawLeaves.mp bp
  have A := rootW.tail wa
  have B := rootW.tail wb
  have noPath (x y : Wire C) (rx : Reach C root x)
      (dest : reads C w y) (src : reads C w x) (ne : x≠y) (run : Reach C x y) : False := by
    obtain ⟨g,trace,step⟩ := run.cases_tail.resolve_left (fun eq => ne eq.symm)
    have eq := same_parent mono unique (rx.trans trace) rootW step dest
    have contradiction := reach_descends trace
    rw [eq] at contradiction
    exact (not_le_of_gt src.2.1) contradiction
  rcases compare_before mono unique a b (rawWire p) A B pathA pathB with ab | ba
  · exact noPath a b A wb wa distinct ab
  · exact noPath b a B wa wb (Ne.symm distinct) ba

lemma raw_is_leaf {C : Circuit} (a : Fin 8) : rawLeaves C (rawWire a) = {a} := by
  ext i
  rw [mem_rawLeaves,Finset.mem_singleton]
  constructor
  · intro h
    rcases h.cases_head with here | ⟨next,bad,_⟩
    · exact Fin.ext (congrArg Fin.val here).symm
    · exact (not_le_of_gt a.isLt bad.1).elim
  · intro e
    subst i
    exact Relation.ReflTransGen.refl

lemma split_gate {C : Circuit} {root w : Wire C}
    (mono : Monotone2 C) (all : AllPorts C root) (unique : UniquePorts C root)
    (rw : Reach C root w) (late : 8≤w.val) :
    ∃ (a b : Wire C), reads C w a ∧ reads C w b ∧
      (gateAt C (w.val-8)).inputs=[a.val,b.val] ∧
      Disjoint (rawLeaves C a) (rawLeaves C b) ∧
      rawLeaves C w = rawLeaves C a ∪ rawLeaves C b := by
  obtain ⟨a,ha⟩ := all w rw late 0
  obtain ⟨b,hb⟩ := all w rw late 1
  have jValid : w.val-8<C.gates.length := by
    have bound := w.isLt
    change w.val<8+C.gates.length at bound
    omega
  have length := (mono _ (gateAt_mem jValid)).2
  have second := (List.getElem?_eq_some_iff.mp hb.1).1
  change 1 < (gateAt C (w.val-8)).inputs.length at second
  have two : (gateAt C (w.val-8)).inputs.length=2 := by omega
  obtain ⟨u,v,ins⟩ := List.length_eq_two.mp two
  have aEq := ha.1
  have bEq := hb.1
  rw [ins] at aEq bEq
  have model : (gateAt C (w.val-8)).inputs=[a.val,b.val] := by
    rw [ins]
    exact congrArg₂ (fun x y : ℕ => [x,y]) (Option.some.inj aEq) (Option.some.inj bEq)
  have ra : reads C w a := port_read late ha
  have rb : reads C w b := port_read late hb
  have distinct : a≠b := by
    intro h
    have bad := (unique w w rw rw late late 0 1 a ha (h.symm ▸ hb)).2
    exact (show (0 : Fin 2) ≠ 1 by decide) bad
  refine ⟨a,b,ra,rb,model,siblings_disjoint mono unique rw ra rb distinct,?_⟩
  ext i
  simp only [Finset.mem_union,mem_rawLeaves]
  constructor
  · intro yes
    rcases yes.cases_head with same | ⟨z,step,after⟩
    · have eq := congrArg Fin.val same
      have low := i.isLt
      change w.val=i.val at eq
      omega
    · have picked := step.2.2
      rw [model] at picked
      simp only [List.mem_cons,List.not_mem_nil,or_false] at picked
      rcases picked with left | right
      · exact Or.inl (Fin.ext left ▸ after)
      · exact Or.inr (Fin.ext right ▸ after)
  · intro h
    exact h.elim (fun run => Relation.ReflTransGen.head ra run) (fun run => Relation.ReflTransGen.head rb run)

end PEqualNP.Outside.L_meta_5583

namespace PEqualNP.Outside.L_meta_5583

def iso : Finset (Fin 8) := {2,5}
def core : Finset (Fin 8) := Finset.univ \ iso
def coreA (u v : Fin 4) : Bool := if u=2 ∧ v=1 then false else A u v

def leOn (S : Finset (Fin 8)) (x y : Fin 8 → Bool) : Prop :=
  ∀ i∈S, x i=true → y i=true

def forced (T : Fin 4→Fin 4→Bool) (S : Finset (Fin 8)) (mode : Bool) (u v : Fin 4) : Prop :=
  ∃ a b : Fin 4, T a b=mode ∧
    (if mode then leOn S (bits a b) (bits u v) else leOn S (bits u v) (bits a b))

def obstruction (T : Fin 4→Fin 4→Bool) (all S : Finset (Fin 8)) (mode : Bool) : Prop :=
  ∃ u v : Fin 4, T u v = !mode ∧ forced T S mode u v ∧ forced T (all \ S) mode u v

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3500000 in
theorem whole_and_blocked : ∀ S : Finset (Fin 8), S.Nonempty →
    (Finset.univ \ S).Nonempty → obstruction A Finset.univ S true := by
  unfold obstruction forced leOn
  simp only [Finset.nonempty_iff_ne_empty,ite_true,Bool.false_eq_true,ite_false]
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3500000 in
theorem whole_or_blocked : ∀ S : Finset (Fin 8), S.Nonempty →
    (Finset.univ \ S).Nonempty → S≠iso → S≠core → obstruction A Finset.univ S false := by
  unfold obstruction forced leOn
  simp only [Finset.nonempty_iff_ne_empty,ite_true,Bool.false_eq_true,ite_false]
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3500000 in
theorem core_blocked : ∀ (S : Finset (Fin 8)) (mode : Bool),
    S ⊆ core → S.Nonempty → (core \ S).Nonempty → obstruction coreA core S mode := by
  unfold obstruction forced leOn
  decide +kernel

theorem core_off_at_isolated : ∀ p∈core, bits 2 1 p = false := by
  decide +kernel

theorem isolated_off_at_core_positive : ∀ u v : Fin 4,
    coreA u v = true → ∀ p∈iso, bits u v p = false := by
  decide +kernel

theorem benchmark_negative : A 1 0 = false := by decide +kernel

end PEqualNP.Outside.L_meta_5583

namespace PEqualNP.Outside.L_meta_5583

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Represents
open PEqualNP.Outside.L_meta_5583.Semantics (val val_gate val_ge gateAt_mem)

lemma cone_mono (C : Circuit) (mono : Monotone2 C) (w : Wire C)
    {x y : Fin 8 → Bool} (ordered : leOn (rawLeaves C w) x y) :
    wireVal C w x = true → wireVal C w y = true :=
  order_in_cone C mono w x y (fun t h => ordered t (mem_rawLeaves.mpr h))

lemma no_split_and (C : Circuit) (mono : Monotone2 C) (T : Fin 4 → Fin 4 → Bool)
    (a b : Wire C) (S : Finset (Fin 8)) (partition : rawLeaves C b = S \ rawLeaves C a)
    (compute : ∀ u v, (wireVal C a (bits u v) && wireVal C b (bits u v)) = T u v)
    (no : obstruction T S (rawLeaves C a) true) : False := by
  obtain ⟨u,v,negative,left,right⟩ := no
  obtain ⟨p,q,h1,orderA⟩ := left
  obtain ⟨p',q',h2,orderB⟩ := right
  simp only [ite_true] at orderA orderB
  have posA := (compute p q).trans h1
  have posB := (compute p' q').trans h2
  simp only [Bool.and_eq_true] at posA posB
  have aOn := cone_mono C mono a orderA posA.1
  have bOn := cone_mono C mono b (partition.symm ▸ orderB) posB.2
  have atUV := compute u v
  rw [aOn,bOn,negative] at atUV
  contradiction

lemma no_split_or (C : Circuit) (mono : Monotone2 C) (T : Fin 4 → Fin 4 → Bool)
    (a b : Wire C) (S : Finset (Fin 8)) (partition : rawLeaves C b = S \ rawLeaves C a)
    (compute : ∀ u v, (wireVal C a (bits u v) || wireVal C b (bits u v)) = T u v)
    (no : obstruction T S (rawLeaves C a) false) : False := by
  obtain ⟨u,v,positive,left,right⟩ := no
  obtain ⟨p,q,h1,orderA⟩ := left
  obtain ⟨p',q',h2,orderB⟩ := right
  simp only [Bool.false_eq_true,ite_false] at orderA orderB
  have offA := (compute p q).trans h1
  have offB := (compute p' q').trans h2
  have aOff : wireVal C a (bits u v) = false := by
    cases e : wireVal C a (bits u v)
    · rfl
    · have h := cone_mono C mono a orderA e
      rw [h] at offA
      contradiction
  have bOff : wireVal C b (bits u v) = false := by
    cases e : wireVal C b (bits u v)
    · rfl
    · have h := cone_mono C mono b (partition.symm ▸ orderB) e
      rw [h,Bool.or_true] at offB
      contradiction
  have atUV := compute u v
  rw [aOff,bOff,positive] at atUV
  contradiction

lemma partition_right {S T R : Finset (Fin 8)} (union : R = S ∪ T) (apart : Disjoint S T) :
    T = R \ S := by
  ext r
  rw [union,Finset.mem_sdiff,Finset.mem_union]
  constructor
  · intro h
    exact ⟨Or.inr h,fun s => Finset.disjoint_left.mp apart s h⟩
  · rintro ⟨h,k⟩
    exact h.resolve_left k

lemma raw_nonempty (C : Circuit) (_mono : Monotone2 C) (root : Wire C)
    (all : AllPorts C root) :
    ∀ w : Wire C, Reach C root w → (rawLeaves C w).Nonempty := by
  intro w
  induction w using Fin.strong_induction_on with
  | h w ih =>
    intro seen
    by_cases low : w.val < 8
    · let x : Fin 8 := ⟨w.val,low⟩
      exact ⟨x,mem_rawLeaves.mpr (show Reach C w w from Relation.ReflTransGen.refl)⟩
    · have late : 8≤w.val := by omega
      obtain ⟨v,pv⟩ := all w seen late 0
      have read := port_read late pv
      obtain ⟨x,hx⟩ := ih v pv.2 (seen.tail read)
      exact ⟨x,mem_rawLeaves.mpr (Relation.ReflTransGen.head read (mem_rawLeaves.mp hx))⟩

lemma gate_truth (C : Circuit) (w a b : Wire C) (wa : reads C w a) (wb : reads C w b)
    (args : (gateAt C (w.val-8)).inputs=[a.val,b.val]) (x : Fin 8 → Bool) :
    wireVal C w x = (gateAt C (w.val-8)).op.eval [wireVal C a x,wireVal C b x] := by
  have late := wa.1
  have valid : w.val-8<C.gates.length := by
    have h := w.isLt
    change w.val<8+C.gates.length at h
    omega
  have addr : 8+(w.val-8)=w.val := by omega
  have values := val_gate (C:=C) (n:=8) (x:=List.ofFn x) (by simp) valid
  rw [addr,args] at values
  simpa only [List.map_cons,List.map_nil,wa.2.1,wb.2.1,ite_true] using values

lemma core_impossible (C : Circuit) (mono : Monotone2 C) (root w : Wire C)
    (all : AllPorts C root) (unique : UniquePorts C root) (reach : Reach C root w)
    (raw : rawLeaves C w = core) (compute : ∀ u v, wireVal C w (bits u v) = coreA u v) :
    False := by
  have late : 8≤w.val := by
    by_contra! early
    let i : Fin 8 := ⟨w.val,early⟩
    have eq : w=rawWire i := rfl
    rw [eq,raw_is_leaf] at raw
    have num := congrArg Finset.card raw
    simp only [Finset.card_singleton] at num
    have six : core.card=6 := by decide +kernel
    omega
  obtain ⟨a,b,wa,wb,args,apart,join⟩ := split_gate mono all unique reach late
  have sub : rawLeaves C a ⊆ core := by rw [← raw,join]; exact Finset.subset_union_left
  have right := partition_right (raw.symm.trans join) apart
  have sa := raw_nonempty C mono root all a (reach.tail wa)
  have sb : (core \ rawLeaves C a).Nonempty := right ▸ raw_nonempty C mono root all b (reach.tail wb)
  have valid : w.val-8<C.gates.length := by
    have h := w.isLt
    change w.val<8+C.gates.length at h
    omega
  have op : (gateAt C (w.val-8)).op = .and ∨ (gateAt C (w.val-8)).op = .or := by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (mono _ (gateAt_mem valid)).1
  rcases op with andG | orG
  · apply no_split_and C mono coreA a b core right ?_ (core_blocked _ true sub sa sb)
    intro u v
    have h := (gate_truth C w a b wa wb args (bits u v)).symm.trans (compute u v)
    simpa [andG,GateOp.eval] using h
  · apply no_split_or C mono coreA a b core right ?_ (core_blocked _ false sub sa sb)
    intro u v
    have h := (gate_truth C w a b wa wb args (bits u v)).symm.trans (compute u v)
    simpa [orG,GateOp.eval] using h

lemma core_operand (C : Circuit) (mono : Monotone2 C) (a b : Wire C)
    (isoA : rawLeaves C a=iso) (coreB : rawLeaves C b=core)
    (compute : ∀ u v, (wireVal C a (bits u v) || wireVal C b (bits u v)) = A u v) :
    ∀ u v, wireVal C b (bits u v) = coreA u v := by
  have ref := (compute 1 0).trans benchmark_negative
  have aNeg : wireVal C a (bits 1 0) = false := by
    cases h : wireVal C a (bits 1 0)
    · rfl
    · rw [h,Bool.true_or] at ref
      contradiction
  have bNeg : wireVal C b (bits 1 0) = false := by
    cases h : wireVal C b (bits 1 0)
    · rfl
    · rw [h,Bool.or_true] at ref
      contradiction
  have absent (w : Wire C) (x : Fin 8→Bool) (zero : ∀ t ∈ rawLeaves C w, x t = false)
      (flag : wireVal C w (bits 1 0) = false) :
      wireVal C w x = false := by
    cases e : wireVal C w x
    · rfl
    · have impossible := cone_mono C mono w
        (show leOn (rawLeaves C w) x (bits 1 0) from
          fun t ht on => by rw [zero t ht] at on; contradiction) e
      rw [flag] at impossible
      contradiction
  intro u v
  by_cases isolated : u=2 ∧ v=1
  · obtain ⟨rfl,rfl⟩ := isolated
    have result := absent b (bits 2 1)
      (fun i mem => core_off_at_isolated i (coreB ▸ mem)) bNeg
    exact result
  · have same : coreA u v = A u v := by simp [coreA,isolated]
    cases result : A u v
    · have h := (compute u v).trans result
      rw [same,result]
      cases bOn : wireVal C b (bits u v)
      · rfl
      · rw [bOn,Bool.or_true] at h
        contradiction
    · have trueCore : coreA u v = true := same.trans result
      have aOff := absent a (bits u v)
        (fun i mem => isolated_off_at_core_positive u v trueCore i (isoA ▸ mem)) aNeg
      have h := compute u v
      rw [aOff,Bool.false_or] at h
      exact h.trans same.symm

theorem lower : ¬ RepSizeAtMost A 7 := by
  intro witness
  obtain ⟨C,mono,small,rep⟩ := witness
  have inRange : C.output<8+C.size := by
    by_contra! out
    have off : C.eval (oneEach (0 : Fin 4) (0 : Fin 4)) = false :=
      val_ge (by simp [oneEach]) out
    rw [rep] at off
    contradiction
  let root : Wire C := ⟨C.output,inRange⟩
  have essential := every_raw C mono rep root rfl
  obtain ⟨full,unique⟩ := tree_ports C mono small root essential
  have all : rawLeaves C root = Finset.univ := Finset.eq_univ_of_forall (fun i => mem_rawLeaves.mpr (essential i))
  have late : 8≤root.val := by
    by_contra! low
    let t : Fin 8 := ⟨root.val,low⟩
    have eq : root=rawWire t := rfl
    rw [eq,raw_is_leaf] at all
    have h := congrArg Finset.card all
    simp at h
  obtain ⟨a,b,wa,wb,args,noShare,union⟩ :=
    split_gate mono full unique Relation.ReflTransGen.refl late
  have comp := partition_right (all.symm.trans union) noShare
  have na := raw_nonempty C mono root full a (Relation.ReflTransGen.single wa)
  have nb := comp ▸ raw_nonempty C mono root full b (Relation.ReflTransGen.single wb)
  have valid : root.val-8<C.gates.length := by
    have h := root.isLt
    change root.val<8+C.gates.length at h
    omega
  have op : (gateAt C (root.val-8)).op = .and ∨ (gateAt C (root.val-8)).op = .or := by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (mono _ (gateAt_mem valid)).1
  have values (u v : Fin 4) :
      (gateAt C (root.val-8)).op.eval [wireVal C a (bits u v),wireVal C b (bits u v)] = A u v := by
    rw [← gate_truth C root a b wa wb args]
    change C.eval (List.ofFn (bits u v)) = A u v
    rw [bits_list]
    exact rep u v
  rcases op with andG | orG
  · apply no_split_and C mono A a b Finset.univ comp ?_ (whole_and_blocked _ na nb)
    intro u v
    simpa [andG,GateOp.eval] using values u v
  · have evaluate (u v : Fin 4) :
        (wireVal C a (bits u v) || wireVal C b (bits u v)) = A u v := by
      simpa [orG,GateOp.eval] using values u v
    have division : rawLeaves C a = iso ∨ rawLeaves C a = core := by
      by_contra! neither
      exact no_split_or C mono A a b Finset.univ comp evaluate
        (whole_or_blocked _ na nb neither.1 neither.2)
    rcases division with isoA | coreA'
    · have coreB : rawLeaves C b=core := by rw [comp,isoA]; rfl
      exact core_impossible C mono root b full unique (Relation.ReflTransGen.single wb) coreB
        (core_operand C mono a b isoA coreB evaluate)
    · have isoB : rawLeaves C b=iso := by rw [comp,coreA']; decide +kernel
      exact core_impossible C mono root a full unique (Relation.ReflTransGen.single wa) coreA'
        (core_operand C mono b a isoB coreA' (fun u v => by rw [Bool.or_comm]; exact evaluate u v))

theorem upper : RepSizeAtMost A 8 := by
  refine ⟨⟨[⟨.or,[6,7]⟩,⟨.or,[0,1]⟩,⟨.and,[8,9]⟩,⟨.or,[0,3]⟩,
    ⟨.and,[4,11]⟩,⟨.and,[2,5]⟩,⟨.or,[10,12]⟩,⟨.or,[13,14]⟩],15⟩,?_ ,by decide,by decide +kernel⟩
  intro g used
  simp only [List.mem_cons,List.not_mem_nil,or_false] at used
  rcases used with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_5583

theorem PEqualNP.Outside.L_meta_5583 :
  PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4813 : ℕ).testBit (4 * u.val + v.val)) 8 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4813 : ℕ).testBit (4 * u.val + v.val)) 7 := by
  exact ⟨PEqualNP.Outside.L_meta_5583.upper,PEqualNP.Outside.L_meta_5583.lower⟩
