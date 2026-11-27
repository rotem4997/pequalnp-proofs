import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8017_aux

namespace Relabel
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def permWire (n : ℕ) (π : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then ↑(π ⟨w, h⟩) else w

def permGate (n : ℕ) (π : Equiv.Perm (Fin n)) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map (permWire n π) }

def permCircuit (n : ℕ) (π : Equiv.Perm (Fin n)) (C : Circuit) : Circuit :=
  { gates := C.gates.map (permGate n π), output := permWire n π C.output }

lemma permWire_lt (n : ℕ) (π : Equiv.Perm (Fin n)) {w : ℕ} (h : w < n) :
    permWire n π w < n := by
  simp only [permWire, h, ↓reduceDIte]
  exact (π ⟨w, h⟩).isLt

lemma permWire_ge (n : ℕ) (π : Equiv.Perm (Fin n)) {w : ℕ} (h : n ≤ w) :
    permWire n π w = w := by
  have hlt : ¬ w < n := Nat.not_lt.mpr h
  simp only [permWire, hlt, ↓reduceDIte]

lemma getD_append_singleton_lt {α : Type*} (l : List α) (v dflt : α) {i : ℕ} (h : i < l.length) :
    (l ++ [v]).getD i dflt = l.getD i dflt := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_append_singleton_eq {α : Type*} (l : List α) (v dflt : α) :
    (l ++ [v]).getD l.length dflt = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
  simp

lemma getD_append_singleton_gt {α : Type*} (l : List α) (v dflt : α) {i : ℕ} (h : l.length < i) :
    (l ++ [v]).getD i dflt = dflt := by
  rw [List.getD_eq_getElem?_getD]
  have hge : (l ++ [v]).length ≤ i := by
    simp only [List.length_append, List.length_singleton]
    omega
  rw [List.getElem?_eq_none hge]
  rfl

lemma getD_ge_length {α : Type*} (l : List α) (dflt : α) {i : ℕ} (h : l.length ≤ i) :
    l.getD i dflt = dflt := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

lemma map_permGate_getD {α : Type*} (n : ℕ) (π : Equiv.Perm (Fin n)) (dflt : α)
    (g : Gate) (acc5 acc1 : List α)
    (hacc : ∀ w, acc5.getD (permWire n π w) dflt = acc1.getD w dflt) :
    ((permGate n π g).inputs.map fun i => acc5.getD i dflt) =
      g.inputs.map fun i => acc1.getD i dflt := by
  simp only [permGate, List.map_map, Function.comp_def, hacc]

lemma foldl_perm_eq {α : Type*} (n : ℕ) (π : Equiv.Perm (Fin n)) (dflt : α)
    (val : Gate → List α → α)
    (hval : ∀ g (acc5 acc1 : List α),
      (∀ w, acc5.getD (permWire n π w) dflt = acc1.getD w dflt) →
      val (permGate n π g) acc5 = val g acc1)
    (gs : List Gate) :
    ∀ (acc5 acc1 : List α),
      acc5.length = acc1.length →
      n ≤ acc1.length →
      (∀ w, acc5.getD (permWire n π w) dflt = acc1.getD w dflt) →
      ((gs.map (permGate n π)).foldl (fun acc g => acc ++ [val g acc]) acc5).length =
        (gs.foldl (fun acc g => acc ++ [val g acc]) acc1).length ∧
      ∀ w, ((gs.map (permGate n π)).foldl (fun acc g => acc ++ [val g acc]) acc5).getD
        (permWire n π w) dflt =
        (gs.foldl (fun acc g => acc ++ [val g acc]) acc1).getD w dflt := by
  induction gs with
  | nil =>
    intro acc5 acc1 hlen _ hacc
    exact ⟨hlen, hacc⟩
  | cons g t ih =>
    intro acc5 acc1 hlen hn hacc
    simp only [List.map_cons, List.foldl_cons]
    have hv : val (permGate n π g) acc5 = val g acc1 := hval g acc5 acc1 hacc
    rw [hv]
    apply ih
    · simp only [List.length_append, List.length_singleton, hlen]
    · simp only [List.length_append, List.length_singleton]
      omega
    · intro w
      rcases Nat.lt_trichotomy w acc1.length with hwlt | rfl | hwgt
      · have hpwlt : permWire n π w < acc5.length := by
          by_cases hwn : w < n
          · have h1 := permWire_lt n π hwn
            omega
          · rw [permWire_ge n π (Nat.le_of_not_lt hwn)]
            omega
        rw [getD_append_singleton_lt acc5 _ dflt hpwlt,
            getD_append_singleton_lt acc1 _ dflt hwlt, hacc w]
      · have hpweq : permWire n π acc1.length = acc1.length := permWire_ge n π hn
        rw [hpweq, ← hlen, getD_append_singleton_eq, hlen, getD_append_singleton_eq]
      · have hpwgt : acc5.length < permWire n π w := by
          have hnw : n ≤ w := by omega
          rw [permWire_ge n π hnw]
          omega
        rw [getD_append_singleton_gt acc5 _ dflt hpwgt,
            getD_append_singleton_gt acc1 _ dflt hwgt]

lemma wires_permCircuit (C : Circuit) (n : ℕ) (π : Equiv.Perm (Fin n)) (x : Fin n → Bool) :
    ∀ w, ((permCircuit n π C).wires (List.ofFn x)).getD (permWire n π w) false = (C.wires (List.ofFn (x ∘ ⇑π))).getD w false := by
  unfold Circuit.wires
  intro w
  change ((C.gates.map (permGate n π)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn x)).getD (permWire n π w) false =
    (C.gates.foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn (x ∘ ⇑π))).getD w false
  have h := foldl_perm_eq n π false
    (fun g w => g.op.eval (g.inputs.map fun i => w.getD i false))
    (fun g acc5 acc1 hacc => by
      rw [map_permGate_getD n π false g acc5 acc1 hacc]
      rfl)
    C.gates
    (List.ofFn x)
    (List.ofFn (x ∘ ⇑π))
    (by simp)
    (by simp)
    (by
      intro w
      by_cases hw : w < n
      · have hpw : permWire n π w = (π ⟨w, hw⟩).val := by simp [permWire, hw]
        have hpwlt : (π ⟨w, hw⟩).val < n := (π ⟨w, hw⟩).isLt
        rw [hpw, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        simp [hpwlt, hw]
      · have hnw : n ≤ w := Nat.le_of_not_lt hw
        rw [permWire_ge n π hnw, getD_ge_length _ false (by simp; exact hnw),
            getD_ge_length _ false (by simp; exact hnw)])
  exact h.2 w

lemma permCircuit_mono (n : ℕ) (π : Equiv.Perm (Fin n)) (C : Circuit)
    (h : Monotone2 C) : Monotone2 (permCircuit n π C) := by
  intro g hg
  change g ∈ C.gates.map (permGate n π) at hg
  obtain ⟨oldGate, holdGate, rfl⟩ := List.mem_map.mp hg
  simpa [permGate] using h oldGate holdGate

end Relabel
end PEqualNP.Outside.L_meta_8017_aux

namespace PEqualNP.Outside.L_meta_8017_aux.Relabel
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

variable {n : ℕ} (π : Equiv.Perm (Fin n)) (C : Circuit)

lemma permWire_inj : Function.Injective (permWire n π) := by
  intro a b hab
  by_cases ha : a < n <;> by_cases hb : b < n
  · simp only [permWire,ha,hb,↓reduceDIte] at hab
    exact congrArg Fin.val (π.injective (Fin.ext hab))
  · have := permWire_lt n π ha
    rw [permWire_ge n π (by omega : n ≤ b)] at hab
    omega
  · have := permWire_lt n π hb
    rw [permWire_ge n π (by omega : n ≤ a)] at hab
    omega
  · simpa [permWire,ha,hb] using hab

lemma perm_gateAt (j : ℕ) :
    gateAt (permCircuit n π C) j = permGate n π (gateAt C j) := by
  unfold gateAt permCircuit
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases C.gates[j]? <;> rfl

lemma perm_ao (h : IsAO2 n C) : IsAO2 n (permCircuit n π C) := by
  refine ⟨?_,?_,?_⟩
  · intro g hg
    obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
    exact h.1 g' hg'
  · intro j hj v hv
    rw [perm_gateAt] at hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    have hj' : j < C.gates.length := by simpa [permCircuit] using hj
    have hlt := h.2.1 j hj' w hw
    by_cases hbase : w < n
    · have := permWire_lt n π hbase
      omega
    · simpa [permWire,hbase] using hlt
  · intro g hg
    obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
    simpa [permGate] using h.2.2 g' hg'

lemma perm_nodup (h : ∀ g ∈ C.gates, g.inputs.Nodup) :
    ∀ g ∈ (permCircuit n π C).gates, g.inputs.Nodup := by
  intro g hg
  obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
  exact (h g' hg').map (permWire_inj π)

lemma gate_lt_of_and {j : ℕ} (h : (gateAt C j).op = GateOp.and) : j < C.gates.length := by
  by_contra! hj
  simp [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_none hj] at h

lemma perm_opnd (h : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) (i : Fin 2) :
    opnd (permCircuit n π C) j i = permWire n π (opnd C j i) := by
  have hm : gateAt C j ∈ C.gates := by
    unfold gateAt
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  have hi : i.val < (gateAt C j).inputs.length := by rw [h.2.2 _ hm]; exact i.isLt
  simp [opnd,perm_gateAt,permGate,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]

private lemma filter_core (cs : List (List ℕ)) (xs : List ℕ) :
    ((xs.map (permWire n π)).filter (fun w => decide (n ≤ w ∧ w < n + cs.length))) =
      xs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases ha : a < n
    · have hl := permWire_lt n π ha
      have h1 : ¬ n ≤ permWire n π a := by omega
      have h2 : ¬ n ≤ a := by omega
      simp only [List.map_cons,List.filter_cons,ih]
      simp [h1,h2]
    · simp only [List.map_cons,permWire_ge n π (Nat.le_of_not_lt ha),List.filter_cons,ih]

lemma perm_cones : cones n (permCircuit n π C) = cones n C := by
  have general (gs : List Gate) (cs : List (List ℕ)) :
      (gs.map (permGate n π)).foldl (coneStep n) cs = gs.foldl (coneStep n) cs := by
    induction gs generalizing cs with
    | nil => rfl
    | cons g t ih =>
      simp only [List.map_cons,List.foldl_cons,ih]
      congr 1
      simp only [coneStep,permGate,filter_core]
  exact general _ _

lemma perm_inCone (i j : ℕ) : InCone n (permCircuit n π C) i j ↔ InCone n C i j := by
  simp [InCone,perm_cones]

lemma perm_first_lt (h : IsAO2 n C) (hn : 0 < C.gates.length) (i : Fin 2) : opnd C 0 i < n := by
  have hm : gateAt C 0 ∈ C.gates := by
    unfold gateAt
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
  have hi : i.val < (gateAt C 0).inputs.length := by rw [h.2.2 _ hm]; exact i.isLt
  apply Nat.lt_of_lt_of_le (h.2.1 0 hn _ ?_) (by omega)
  simp [opnd,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]

lemma perm_output_sub : (permCircuit n π C).output - n = C.output - n := by
  change permWire n π C.output - n = C.output - n
  by_cases h : C.output < n
  · have := permWire_lt n π h
    omega
  · rw [permWire_ge n π (Nat.le_of_not_lt h)]

lemma perm_output_eq (j : ℕ) :
    n + j = (permCircuit n π C).output ↔ n + j = C.output := by
  change n + j = permWire n π C.output ↔ n + j = C.output
  by_cases h : C.output < n
  · have := permWire_lt n π h
    omega
  · rw [permWire_ge n π (Nat.le_of_not_lt h)]

end PEqualNP.Outside.L_meta_8017_aux.Relabel

namespace PEqualNP.Outside.L_meta_8017_aux
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership

def points : Fin 8 → Fin 7 → Fin 7 := ![![0,1,2,3,4,5,6],![0,1,4,3,2,6,5],![0,1,5,3,6,2,4],![0,1,6,3,5,4,2],![0,3,2,1,5,4,6],![0,3,4,1,6,2,5],![0,3,5,1,2,6,4],![0,3,6,1,4,5,2]]
def lines : Fin 8 → Fin 7 → Fin 7 := ![![0,1,2,3,4,5,6],![0,1,3,2,6,5,4],![0,5,2,3,6,1,4],![0,5,3,2,4,1,6],![0,2,1,5,4,3,6],![0,3,1,5,6,2,4],![0,2,5,1,6,3,4],![0,3,5,1,4,2,6]]
def action : Fin 8 → Fin 14 → Fin 14 := ![![0,1,2,3,4,5,6,7,8,9,10,11,12,13],![0,1,4,3,2,6,5,7,8,10,9,13,12,11],![0,1,5,3,6,2,4,7,12,9,10,13,8,11],![0,1,6,3,5,4,2,7,12,10,9,11,8,13],![0,3,2,1,5,4,6,7,9,8,12,11,10,13],![0,3,4,1,6,2,5,7,10,8,12,13,9,11],![0,3,5,1,2,6,4,7,9,12,8,13,10,11],![0,3,6,1,4,5,2,7,10,12,8,11,9,13]]
def invKey : Fin 8 → Fin 8 := ![0,1,2,3,4,6,5,7]

def perm (k : Fin 8) : Equiv.Perm (Fin 14) where
  toFun := action k
  invFun := action (invKey k)
  left_inv := (by decide +kernel : ∀ k v, action (invKey k) (action k v) = v) k
  right_inv := (by decide +kernel : ∀ k v, action k (action (invKey k) v) = v) k

def F (x : Fin 14 → Bool) : Bool := decide (∃ p l : Fin 7, p ∈ fanoLines l ∧
  x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)

theorem forward (k : Fin 8) (x : Fin 14 → Bool) (h : F (x ∘ perm k) = true) : F x = true := by
  obtain ⟨p,l,hE,hp,hl⟩ := of_decide_eq_true h
  apply decide_eq_true
  refine ⟨points k p,lines k l,?_,?_,?_⟩
  · exact (by decide +kernel : ∀ k p l, p ∈ fanoLines l → points k p ∈ fanoLines (lines k l)) k p l hE
  · have eq := (by decide +kernel : ∀ k p, perm k (Fin.castAdd 7 p) = Fin.castAdd 7 (points k p)) k p
    simpa only [Function.comp_apply, eq] using hp
  · have eq := (by decide +kernel : ∀ k l, perm k (Fin.natAdd 7 l) = Fin.natAdd 7 (lines k l)) k l
    simpa only [Function.comp_apply, eq] using hl

theorem invariant (k : Fin 8) (x : Fin 14 → Bool) : F (x ∘ perm k) = F x := by
  apply Bool.eq_iff_iff.mpr
  refine ⟨forward k x,fun h => forward (invKey k) (x ∘ perm k) ?_⟩
  convert h using 2
  funext i
  exact congrArg x ((perm k).right_inv i)

def canonical (i j : ℕ) : Bool :=
  (([2438,2956,11728,0,0,0,0,2304,6656,0,0,8192] : List ℕ).getD (min i j) 0).testBit (max i j)

theorem orbit : ∀ i j : Fin 14, i ≠ j → ∃ k : Fin 8, canonical (perm k i).val (perm k j).val = true := by
  decide +kernel

theorem fixes (k : Fin 8) : perm k 0 = 0 ∧ perm k 7 = 7 :=
  (by decide +kernel : ∀ k, perm k 0 = 0 ∧ perm k 7 = 7) k

theorem fixedPair (k : Fin 8) (u v : Fin 14) (hu : perm k u = u) (hv : perm k v = v) :
    pairInput u v ∘ perm k = pairInput u v := by
  funext i
  change decide (perm k i=u ∨ perm k i=v) = decide (i=u ∨ i=v)
  have one : perm k i = u ↔ i=u := by simpa only [hu] using (show perm k i=perm k u ↔ i=u from (perm k).apply_eq_iff_eq)
  have two : perm k i = v ↔ i=v := by simpa only [hv] using (show perm k i=perm k v ↔ i=v from (perm k).apply_eq_iff_eq)
  simp only [one,two]

end PEqualNP.Outside.L_meta_8017_aux

namespace PEqualNP.Outside.L_meta_8017_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm Relabel

def W (C : Circuit) (j : ℕ) (p : Fin 14) : Prop :=
  (gateAt C j).op = .and ∧ (14+j=C.output ∨ InCone 14 C j (C.output-14)) ∧
  wireVal 14 C (14+j) (pairInput 0 7) = true ∧
  ∀ b, wireVal 14 C (opnd C j b) (pairInput p p) = false

def Bad (C : Circuit) : Prop := C.size ≤ 27 ∧ IsAO2 14 C ∧ (∀ g∈C.gates, g.inputs.Nodup) ∧
  circuitFun 14 C = F ∧ ∃ a b, a≠b ∧ ¬InCone 14 C a b ∧ ¬InCone 14 C b a ∧ W C a 0 ∧ W C b 7

theorem value_pair (C : Circuit) (k : Fin 8) (u v : Fin 14)
    (hu : perm k u = u) (hv : perm k v = v) (w : ℕ) :
    wireVal 14 (permCircuit 14 (perm k) C) (permWire 14 (perm k) w) (pairInput u v) =
      wireVal 14 C w (pairInput u v) := by
  change _ = (C.wires (List.ofFn (pairInput u v))).getD w false
  simpa only [wireVal,fixedPair k u v hu hv] using wires_permCircuit C 14 (perm k) (pairInput u v) w

theorem mark_perm {C : Circuit} (ao : IsAO2 14 C) (k : Fin 8) {j : ℕ} {p : Fin 14}
    (hp : perm k p=p) (h : W C j p) : W (permCircuit 14 (perm k) C) j p := by
  obtain ⟨hop,hold,val,child⟩ := h
  have hj := gate_lt_of_and C hop
  refine ⟨by simpa [perm_gateAt,permGate] using hop,?_,?_,?_⟩
  · rcases hold with e|cone
    · exact Or.inl ((perm_output_eq (perm k) C j).2 e)
    · exact Or.inr (by rw [perm_output_sub,perm_inCone]; exact cone)
  · have eq := value_pair C k 0 7 (fixes k).1 (fixes k).2 (14+j)
    rw [permWire_ge _ _ (by omega : 14 ≤ 14+j)] at eq
    exact eq.trans val
  · intro b
    rw [perm_opnd (perm k) C ao j hj b, value_pair C k p p hp hp]
    exact child b

theorem normalize : (∃ C, Bad C) → ∃ C, Bad C ∧ canonical (opnd C 0 0) (opnd C 0 1) = true := by
  rintro ⟨C,size,ao,ndup,sem,a,b,ne,ab,ba,ha,hb⟩
  have pos : 0 < C.gates.length := by have := gate_lt_of_and C ha.1; omega
  have mem : gateAt C 0 ∈ C.gates := by
    simp [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem pos]
  obtain ⟨i,j,hij⟩ := List.length_eq_two.mp (ao.2.2 _ mem)
  let u : Fin 14 := ⟨opnd C 0 0,perm_first_lt C ao pos 0⟩
  let v : Fin 14 := ⟨opnd C 0 1,perm_first_lt C ao pos 1⟩
  have uv : u ≠ v := by
    intro eq
    have pi := congrArg Fin.val eq
    have nod := ndup _ mem
    simp [u,v,opnd,hij] at pi
    simp [hij,pi] at nod
  obtain ⟨k,can⟩ := orbit u v uv
  refine ⟨permCircuit 14 (perm k) C,⟨by simpa [permCircuit,Circuit.size] using size,
    perm_ao (perm k) C ao,perm_nodup (perm k) C ndup,?_,a,b,ne,?_,?_,
    mark_perm ao k (fixes k).1 ha,mark_perm ao k (fixes k).2 hb⟩,?_⟩
  · funext x
    have h := wires_permCircuit C 14 (perm k) x C.output
    calc circuitFun 14 (permCircuit 14 (perm k) C) x = circuitFun 14 C (x ∘ perm k) := h
         _ = F (x ∘ perm k) := congrFun sem _
         _ = F x := invariant k x
  · exact fun h => ab ((perm_inCone (perm k) C a b).1 h)
  · exact fun h => ba ((perm_inCone (perm k) C b a).1 h)
  · rw [perm_opnd (perm k) C ao 0 pos 0,perm_opnd (perm k) C ao 0 pos 1]
    simpa only [permWire,dif_pos (perm_first_lt C ao pos 0),dif_pos (perm_first_lt C ao pos 1),u,v] using can

end PEqualNP.Outside.L_meta_8017_aux

theorem PEqualNP.Outside.L_meta_8017 : have x1 : (Fin (14 : ℕ) → Bool) → Bool := fun (x1 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x2 : Fin (7 : ℕ)) (x3 : Fin (7 : ℕ)), x2 ∈ PEqualNP.CircuitLowerBounds.fanoLines x3 ∧ x1 (Fin.castAdd (7 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (7 : ℕ) x3) = Bool.true); have x2 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Fin (14 : ℕ) → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Fin (14 : ℕ)) =>   have x5 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x2;   have x6 : Fin (14 : ℕ) → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput;   (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x3 = x2.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x2 x3 (x2.output - (14 : ℕ))) ∧ x5 ((14 : ℕ) + x3) (x6 (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x7 : Fin (2 : ℕ)), x5 (PEqualNP.TopForm.opnd x2 x3 x7) (x6 x4 x4) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => x3.size ≤ (27 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x3 ∧ (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧ PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x3 = x1 ∧ ∃ (x4 : ℕ) (x5 : ℕ), x4 ≠ x5 ∧ ¬PEqualNP.EdgeOwnership.InCone (14 : ℕ) x3 x4 x5 ∧ ¬PEqualNP.EdgeOwnership.InCone (14 : ℕ) x3 x5 x4 ∧ x2 x3 x4 (0 : Fin (14 : ℕ)) ∧ x2 x3 x5 (7 : Fin (14 : ℕ)); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) =>   have x5 : ℕ := PEqualNP.TopForm.opnd x4 (0 : ℕ) (0 : Fin (2 : ℕ));   have x6 : ℕ := PEqualNP.TopForm.opnd x4 (0 : ℕ) (1 : Fin (2 : ℕ));   ([(2438 : ℕ), (2956 : ℕ), (11728 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (2304 : ℕ), (6656 : ℕ), (0 : ℕ), (0 : ℕ), (8192 : ℕ)].getD (Min.min x5 x6) (0 : ℕ)).testBit (Max.max x5 x6) = Bool.true; (∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x3 x5) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x3 x6 ∧ x4 x6 := PEqualNP.Outside.L_meta_8017_aux.normalize
