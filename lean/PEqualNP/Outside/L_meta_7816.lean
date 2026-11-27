import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7816_aux

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
end PEqualNP.Outside.L_meta_7816_aux

namespace PEqualNP.Outside.L_meta_7816_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 10 → Bool) : Bool :=
  [1,12,23,34,40,5,16,27,38,49,57,79,96,68,85].any fun i : ℕ =>
    x (Fin.ofNat 10 (i / 10)) && x (Fin.ofNat 10 (i % 10))

def effective (v : ℕ) (g : Gate) : Prop :=
  v ∈ g.inputs ∧ (g.op = GateOp.not → g.inputs.head? = some v)

def cap (k : ℕ) (C : Circuit) : Prop :=
  ∀ (i : Fin 10) (S : Finset ℕ),
    (∀ j ∈ S, ∃ g : Gate, C.gates[j]? = some g ∧ effective i g) → S.card ≤ k

def exact (C : Circuit) (neg : Bool) : Prop :=
  ∀ x : Fin 10 → Bool, (if neg = true then !circuitFun 10 C x else circuitFun 10 C x) = target x

def single (C : Circuit) (a : Fin 10) (p : ℕ) : Prop :=
  ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → effective a g → j = p

def isolated (C : Circuit) (a : Fin 10) (p : ℕ) : Prop :=
  ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → effective a g →
    j = p ∧ (g.op = GateOp.not ∨ ∀ w ∈ g.inputs, w < 10 → w = a.val)

end PEqualNP.Outside.L_meta_7816_aux

namespace PEqualNP.Outside.L_meta_7816_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PinBudget

def blank : Gate := ⟨.or, []⟩

def need (n : Nat) : List Gate → List Nat → List Nat
  | [], q => q
  | g::gs, q =>
    let w := need (n+1) gs q
    if n ∈ w then (w.filter (· != n)) ++ g.inputs else w

def mask (n : Nat) : List Gate → List Nat → List Gate
  | [], _ => []
  | g::gs, q =>
    (if n ∈ need (n+1) gs q then g else blank) :: mask (n+1) gs q

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem mask_length (n : Nat) (gs : List Gate) (q : List Nat) :
    (mask n gs q).length = gs.length := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => simp [mask, ih]

theorem need_length (n : Nat) (gs : List Gate) (q : List Nat)
    (fan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (need n gs q).length ≤ q.length + gs.length := by
  induction gs generalizing n with
  | nil => simp [need]
  | cons g gs ih =>
    have tail := ih (n+1) (fun h hh => fan h (by simp [hh]))
    have ar := fan g (by simp)
    simp only [need, List.length_cons]
    split
    · rename_i hit
      have lt : ((need (n+1) gs q).filter (· != n)).length < (need (n+1) gs q).length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨n,hit,by simp⟩
      rw [List.length_append]
      omega
    · omega

theorem mask_slot (n : Nat) (gs : List Gate) (q : List Nat) (j : Nat) (h : Gate)
    (hit : (mask n gs q)[j]? = some h) : h = blank ∨ gs[j]? = some h := by
  induction gs generalizing n j with
  | nil => simp [mask] at hit
  | cons a gs ih =>
    cases j with
    | zero =>
      simp only [mask, List.getElem?_cons_zero, Option.some.injEq] at hit
      by_cases live : n ∈ need (n+1) gs q
      · simp [live] at hit
        exact Or.inr (by simp [hit])
      · simp [live] at hit
        exact Or.inl hit.symm
    | succ j => exact ih (n+1) j (by simpa [mask] using hit)

theorem get_snoc_other (w : List Bool) (b : Bool) (i : Nat) (h : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases hi : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append, hi]
  · have far : [b].length ≤ i - w.length := by simp; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_append, hi,
      List.getElem?_eq_none far]

theorem mask_eval (n : Nat) (gs : List Gate) (q : List Nat) (u v : List Bool)
    (lu : u.length = n) (lv : v.length = n)
    (agree : ∀ i ∈ need n gs q, u.getD i false = v.getD i false) :
    ∀ i ∈ q, ((mask n gs q).foldl step u).getD i false = (gs.foldl step v).getD i false := by
  induction gs generalizing n u v with
  | nil => exact agree
  | cons g gs ih =>
    simp only [mask, List.foldl_cons]
    apply ih (n+1) _ _ (by simp [step,lu]) (by simp [step,lv])
    intro i hi
    by_cases live : n ∈ need (n+1) gs q
    · simp only [ite_eq_left live]
      by_cases same : i=n
      · subst i
        have ar : g.inputs.map (fun i => u.getD i false) = g.inputs.map (fun i => v.getD i false) :=
          List.map_congr_left (fun i hm => agree i (by simp [need,live,hm]))
        simp only [List.getD_eq_getElem?_getD] at ar
        simp [step, List.getD_eq_getElem?_getD, lu,lv,ar]
      · rw [step,step,get_snoc_other _ _ _ (by simpa [lu] using same),
          get_snoc_other _ _ _ (by simpa [lv] using same)]
        apply agree
        simp [need,live,hi,same]
    · have ne : i ≠ n := fun h => live (h ▸ hi)
      simp only [ite_eq_right live]
      rw [step,step,get_snoc_other _ _ _ (by simpa [lu] using ne),
          get_snoc_other _ _ _ (by simpa [lv] using ne)]
      exact agree i (by simpa [need,live] using hi)

theorem mask_count (n : Nat) (gs : List Gate) (q : List Nat) (a : Nat) (ha : a<n) :
    ((mask n gs q).flatMap Gate.inputs).count a ≤ (need n gs q).count a := by
  induction gs generalizing n with
  | nil => simp [mask]
  | cons g gs ih =>
    have tail := ih (n+1) (by omega)
    have other : (a != n) = true := by simp; omega
    by_cases live : n ∈ need (n+1) gs q
    · have hfl : ((need (n+1) gs q).filter (fun i => i != n)).count a = (need (n+1) gs q).count a :=
        List.count_filter (p := fun i => i != n) other
      simp [mask,need,live,hfl]
      omega
    · simpa [mask,need,live,blank] using tail

def Reads (gs : List Gate) (p wire : Nat) := ∃ g : Gate, gs[p]? = some g ∧ wire ∈ g.inputs

theorem operands_mem {gs : List Gate} {p wire : Nat} (read : Reads gs p wire) :
    wire ∈ gs.flatMap Gate.inputs := by
  obtain ⟨g,hg,hm⟩ := read
  exact List.mem_flatMap.mpr ⟨g, List.mem_iff_getElem?.mpr ⟨p,hg⟩,hm⟩

theorem two_reads {gs : List Gate} {a p q : Nat}
    (ne : p ≠ q) (hp : Reads gs p a) (hq : Reads gs q a) :
    2 ≤ (gs.flatMap Gate.inputs).count a := by
  induction gs generalizing p q with
  | nil => obtain ⟨g,hg,_⟩ := hp; simp at hg
  | cons g gs ih =>
    simp only [List.flatMap_cons,List.count_append]
    cases p <;> cases q
    · exact (ne rfl).elim
    · have x := List.count_pos_iff.mpr (show a ∈ g.inputs by simpa [Reads] using hp)
      have y := List.count_pos_iff.mpr (operands_mem (by simpa [Reads] using hq))
      omega
    · have x := List.count_pos_iff.mpr (show a ∈ g.inputs by simpa [Reads] using hq)
      have y := List.count_pos_iff.mpr (operands_mem (by simpa [Reads] using hp))
      omega
    · rename_i p q
      have h := ih (show p ≠ q from fun h => ne (congrArg Nat.succ h))
        (by simpa [Reads] using hp) (by simpa [Reads] using hq)
      omega

theorem sparse (q : List Nat) (h : q.length ≤ 19) : ∃ a : Fin 10, q.count a.val ≤ 1 := by
  classical
  by_contra! all
  have count : ∀ a ∈ Finset.range 10, 2 ≤ q.count a := fun a ha => all ⟨a,Finset.mem_range.mp ha⟩
  have sub : Finset.range 10 ⊆ q.toFinset := by
    intro a ha
    exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by have := count a ha; omega))
  have total := List.sum_toFinset_count_eq_length q
  have one := Finset.sum_le_sum count
  have two := Finset.sum_le_sum_of_subset_of_nonneg sub (fun a _ _ => Nat.zero_le (q.count a))
  simp at one
  omega

end PinBudget

open PinBudget in
theorem single_raw (C : Circuit) (k : Nat) (fan : FanInTwo C) (size : C.size ≤ 18)
    (hc : cap k C) :
    ∃ D, circuitFun 10 D = circuitFun 10 C ∧ FanInTwo D ∧ D.size ≤ C.size ∧ cap k D ∧
      ∃ a : Fin 10, ∃ j : Nat, single D a j := by
  let D : Circuit := ⟨mask 10 C.gates [C.output], C.output⟩
  have index (j : Nat) (g : Gate) (hj : D.gates[j]? = some g) := mask_slot 10 C.gates [C.output] j g hj
  refine ⟨D,?_,?_,?_,?_,?_⟩
  · funext x
    exact mask_eval 10 C.gates [C.output] (List.ofFn x) (List.ofFn x) (by simp) (by simp)
      (fun _ _ => rfl) C.output (by simp)
  · intro g hg
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
    rcases index j g hj with rfl | h
    · simp [blank]
    · exact fan g (List.mem_iff_getElem?.mpr ⟨j,h⟩)
  · exact (mask_length 10 C.gates [C.output]).le
  · intro i S hS
    apply hc i S
    intro j hj
    obtain ⟨g,hg,eff⟩ := hS j hj
    rcases index j g hg with rfl | hh
    · simp [effective,blank] at eff
    · exact ⟨g,hh,eff⟩
  · have bound := need_length 10 C.gates [C.output] (fun g hg => (fan g hg).2)
    change C.gates.length ≤ 18 at size
    obtain ⟨a,ha⟩ := sparse (need 10 C.gates [C.output]) (by simp at bound; omega)
    have count := (mask_count 10 C.gates [C.output] a.val a.isLt).trans ha
    by_cases existsRead : ∃ j, Reads D.gates j a
    · obtain ⟨j,hj⟩ := existsRead
      refine ⟨a,j,?_⟩
      intro p g hp eff
      by_contra ne
      exact (by have h := two_reads ne (show Reads D.gates p a from ⟨g,hp,eff.1⟩) hj
                change 2 ≤ ((mask 10 C.gates [C.output]).flatMap Gate.inputs).count a.val at h
                omega)
    · exact ⟨a,0,fun j g hg eff => (existsRead ⟨j,g,hg,eff.1⟩).elim⟩

end PEqualNP.Outside.L_meta_7816_aux

namespace PEqualNP.Outside.L_meta_7816_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_7816_aux.Relabel

private def table (a x : Fin 10) : Fin 10 :=
  ([[0,1,2,3,4,5,6,7,8,9], [1,0,4,3,2,6,5,9,8,7], [2,1,0,4,3,7,6,5,9,8],
    [3,2,1,0,4,8,7,6,5,9], [4,3,2,1,0,9,8,7,6,5], [5,7,2,3,8,0,9,1,4,6],
    [6,1,2,3,8,9,0,7,4,5], [7,2,1,6,9,5,3,0,8,4], [8,3,2,1,6,5,4,7,0,9],
    [9,6,8,3,4,7,1,5,2,0]] : List (List (Fin 10))).getD a [] |>.getD x 0

private theorem table_inv : ∀ a x : Fin 10, table a (table a x) = x := by decide +kernel
private theorem table_zero : ∀ a : Fin 10, table a a = 0 := by decide +kernel
def sym (a : Fin 10) : Equiv.Perm (Fin 10) :=
  ⟨table a, table a, table_inv a, table_inv a⟩

private def edges : List Nat := [1,12,23,34,40,5,16,27,38,49,57,79,96,68,85]
private def edge (i j : Fin 10) : Prop :=
  i.val*10+j.val ∈ edges ∨ j.val*10+i.val ∈ edges
private instance (i j : Fin 10) : Decidable (edge i j) := by unfold edge;infer_instance
private theorem edges_ok : ∀ z ∈ edges, z / 10 < 10 := by decide +kernel
private theorem edge_map : ∀ (a i j : Fin 10), edge i j → edge (sym a i) (sym a j) := by decide +kernel

private theorem holds (x : Fin 10 → Bool) :
    target x = true ↔ ∃ i j, edge i j ∧ x i = true ∧ x j = true := by
  change (edges.any fun z => x (Fin.ofNat 10 (z / 10)) && x (Fin.ofNat 10 (z % 10))) = true ↔ _
  rw [List.any_eq_true]
  constructor
  · rintro ⟨z,hz,h⟩
    have hs := edges_ok z hz
    have hv : (Fin.ofNat 10 (z / 10)).val * 10 + (Fin.ofNat 10 (z % 10)).val = z := by
      change z / 10 % 10 * 10 + z % 10 % 10 = z
      rw [Nat.mod_eq_of_lt hs,Nat.mod_mod]; omega
    refine ⟨_,_,Or.inl (hv ▸ hz),?_⟩
    simpa only [Bool.and_eq_true] using h
  · rintro ⟨i,j,(h|h),hi,hj⟩
    · refine ⟨_,h,?_⟩
      have he₁ : Fin.ofNat 10 ((i.val*10+j.val)/10) = i := by apply Fin.ext; change (i.val*10+j.val)/10%10=i.val;omega
      have he₂ : Fin.ofNat 10 ((i.val*10+j.val)%10) = j := by apply Fin.ext; change (i.val*10+j.val)%10%10=j.val;omega
      simp only [he₁,he₂,hi,hj]; rfl
    · refine ⟨_,h,?_⟩
      have he₁ : Fin.ofNat 10 ((j.val*10+i.val)/10) = j := by apply Fin.ext; change (j.val*10+i.val)/10%10=j.val;omega
      have he₂ : Fin.ofNat 10 ((j.val*10+i.val)%10) = i := by apply Fin.ext; change (j.val*10+i.val)%10%10=i.val;omega
      simp only [he₁,he₂,hi,hj]; rfl

private theorem target_sym (a : Fin 10) (x : Fin 10 → Bool) : target (x ∘ sym a) = target x := by
  apply Bool.eq_iff_iff.mpr
  rw [holds,holds]
  constructor
  · rintro ⟨i,j,h,hi,hj⟩
    exact ⟨_,_,edge_map a i j h,hi,hj⟩
  · rintro ⟨i,j,h,hi,hj⟩
    exact ⟨_,_,edge_map a i j h,by simpa [Function.comp_def,sym,table_inv] using hi,
      by simpa [Function.comp_def,sym,table_inv] using hj⟩

private theorem pw_inv (a : Fin 10) (w : Nat) :
    permWire 10 (sym a) (permWire 10 (sym a) w) = w := by
  by_cases h : w < 10
  · have h' := permWire_lt 10 (sym a) h
    unfold permWire at h' ⊢
    simp only [h,↓reduceDIte] at h' ⊢
    rw [dif_pos h']
    exact congrArg Fin.val (table_inv a ⟨w,h⟩)
  · simp [permWire,h]

private theorem eff (a : Fin 10) (g : Gate) (u : ℕ) :
    effective (permWire 10 (sym a) u) (permGate 10 (sym a) g) ↔ effective u g := by
  have inj : Function.Injective (permWire 10 (sym a)) := fun a' b' h => by
    simpa [pw_inv] using congrArg (permWire 10 (sym a)) h
  unfold effective permGate
  simp only [List.mem_map, List.head?_map]
  constructor
  · rintro ⟨⟨x,hx,he⟩,hn⟩
    refine ⟨inj he ▸ hx,fun hop => ?_⟩
    have ho := hn hop
    cases h : g.inputs.head? with
    | none => simp [h] at ho
    | some w =>
      have hw : permWire 10 (sym a) w = permWire 10 (sym a) u := by simpa [h] using ho
      simp [inj hw]
  · rintro ⟨hg,hn⟩
    exact ⟨⟨_,hg,rfl⟩,fun hop => by simp [hn hop]⟩

private theorem pullGate (a : Fin 10) (C : Circuit) (q : Nat) (g : Gate)
    (h : (permCircuit 10 (sym a) C).gates[q]? = some g) :
    ∃ g', C.gates[q]? = some g' ∧ g = permGate 10 (sym a) g' := by
  change (C.gates.map (permGate 10 (sym a)))[q]? = some g at h
  rw [List.getElem?_map] at h
  cases he : C.gates[q]? with
  | none => simp [he] at h
  | some z => exact ⟨z,rfl,by simpa [he] using h.symm⟩

theorem relocate (C : Circuit) (neg : Bool) (k : ℕ) (a : Fin 10) (j : ℕ)
    (hf : FanInTwo C) (hc : cap k C) (hx : exact C neg) (hi : isolated C a j) :
    ∃ D, FanInTwo D ∧ D.size = C.size ∧ cap k D ∧ circuitFun 10 D = circuitFun 10 C ∧ isolated D 0 j := by
  refine ⟨permCircuit 10 (sym a) C,?_,by simp [Circuit.size,permCircuit],?_,?_,?_⟩
  · intro g hg
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hg
    simpa [permGate] using hf z hz
  · intro i S hs
    apply hc (sym a i) S
    intro q hq
    obtain ⟨g,hg,he⟩ := hs q hq
    obtain ⟨z,hz,rfl⟩ := pullGate a C q g hg
    refine ⟨z,hz,(eff a z _).mp ?_⟩
    have hw : permWire 10 (sym a) (sym a i).val = i.val := by
      simpa [permWire,sym] using congrArg Fin.val (table_inv a i)
    rwa [hw]
  · funext x
    change ((permCircuit 10 (sym a) C).wires (List.ofFn x)).getD (permWire 10 (sym a) C.output) false = _
    rw [wires_permCircuit]
    have h₁ := hx (x ∘ sym a)
    have h₂ := hx x
    rw [target_sym] at h₁
    change circuitFun 10 C (x ∘ sym a) = circuitFun 10 C x
    cases neg <;> simp_all
  · intro q g hg he
    obtain ⟨z,hz,rfl⟩ := pullGate a C q g hg
    have ha : permWire 10 (sym a) a.val = 0 := by
      simpa [permWire,sym] using congrArg Fin.val (table_zero a)
    have he' := (eff a z a.val).mp (by simpa [ha] using he)
    obtain ⟨r,hz'|hz'⟩ := hi q z hz he'
    · exact ⟨r,Or.inl hz'⟩
    · refine ⟨r,Or.inr ?_⟩
      intro w hw h10
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
      by_cases v10 : v < 10
      · rw [hz' v hv v10,ha]; rfl
      · rw [permWire_ge 10 (sym a) (by omega : 10 ≤ v)] at h10
        omega
end PEqualNP.Outside.L_meta_7816_aux

namespace PEqualNP.Outside.L_meta_7816_aux

private def beforePin (b c : Fin 10) (v : Bool) (i : Fin 10) : Bool :=
  decide (i = c) || (decide (i = b) && v)

private def afterPin (a b c : Fin 10) (v : Bool) (i : Fin 10) : Bool :=
  decide (i = a) || beforePin b c v i

private theorem toggles : ∀ a b : Fin 10, a ≠ b → ∀ v : Bool, ∃ c : Fin 10,
    beforePin b c v b = v ∧ afterPin a b c v b = v ∧
    target (beforePin b c v) ≠ target (afterPin a b c v) := by
  decide +kernel

theorem pin_witness (a b : Fin 10) (ne : a ≠ b) (v : Bool) :
    ∃ x y : Fin 10 → Bool, x b = v ∧ y b = v ∧
      (∀ i, i ≠ a → x i = y i) ∧ target x ≠ target y := by
  obtain ⟨c,hb,ha,ht⟩ := toggles a b ne v
  refine ⟨beforePin b c v,afterPin a b c v,hb,ha,?_,ht⟩
  intro i hi
  simp [afterPin,hi]

end PEqualNP.Outside.L_meta_7816_aux

namespace PEqualNP.Outside.L_meta_7816_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Obstruction

def advance (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma raw_preserved (gs : List Gate) (w : List Bool) (i : ℕ) (small : i < w.length) :
    (gs.foldl advance w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (advance w g) (by simp [advance]; omega)]
    exact List.getD_append _ _ _ _ small

lemma rawbit (x : Fin 10 → Bool) (v : Fin 10) : (List.ofFn x).getD v.val false = x v := by
  fin_cases v <;> rfl

lemma not_raw (C : Circuit) (neg : Bool) (hx : exact C neg) (a : Fin 10) : C.output ≠ a.val := by
  intro eq
  let z : Fin 10 → Bool := fun _ => false
  let u : Fin 10 → Bool := fun i => decide (i=a)
  have ev (x : Fin 10 → Bool) : circuitFun 10 C x = x a := by
    change (C.gates.foldl advance (List.ofFn x)).getD C.output false = _
    rw [eq,raw_preserved _ _ _ (by simpa using a.isLt),rawbit]
  have emp : target z = false := by decide
  have sing : ∀ i : Fin 10, target (fun j => decide (j=i)) = false := by decide +kernel
  have f := hx z
  have g := hx u
  rw [ev, emp] at f
  rw [ev, show target u=false from sing a] at g
  cases neg <;> simp_all [u,z]

lemma unaffected {a : ℕ} {g : Gate} {w w' : List Bool}
    (same : ∀ i, i ≠ a → w.getD i false = w'.getD i false)
    (no : ¬ effective a g) :
    g.op.eval (g.inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  by_cases hn : g.op = GateOp.not
  · cases hi : g.inputs with
    | nil => simp [hi]
    | cons i l =>
      have diff : i ≠ a := by
        rintro rfl
        exact no ⟨by simp [hi],fun _ => by simp [hi]⟩
      simp [hn,GateOp.eval]; exact same i diff
  · have miss : a ∉ g.inputs := fun mem => no ⟨mem,fun h => (hn h).elim⟩
    congr 1
    apply List.map_congr_left
    intro i hi
    exact same i (fun e => miss (e ▸ hi))

lemma absorb {g : Gate} {b : ℕ} (hb : b ∈ g.inputs) {w w' : List Bool} {v : Bool}
    (h : (v=false ∧ g.op=.and) ∨ (v=true ∧ g.op=.or))
    (bw : w.getD b false = v) (bw' : w'.getD b false = v) :
    g.op.eval (g.inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  rcases h with ⟨rfl,ha⟩ | ⟨rfl,ha⟩
  · have eq (s : List Bool) (hs : s.getD b false = false) :
        (g.inputs.map fun i => s.getD i false).all id = false := by
      simp only [List.all_eq_false]
      exact ⟨false, List.mem_map.mpr ⟨b,hb,hs⟩,by decide⟩
    rw [ha]; exact (eq w bw).trans (eq w' bw').symm
  · have eq (s : List Bool) (hs : s.getD b false = true) :
        (g.inputs.map fun i => s.getD i false).any id = true := by
      exact List.any_eq_true.mpr ⟨true,List.mem_map.mpr ⟨b,hb,hs⟩,by decide⟩
    rw [ha]; exact (eq w bw).trans (eq w' bw').symm

lemma fold_mask {a b : ℕ} {v : Bool} {g₀ : Gate} (hb : b ∈ g₀.inputs)
    (op : (v=false ∧ g₀.op=.and) ∨ (v=true ∧ g₀.op=.or))
    (gs : List Gate) (read : ∀ g ∈ gs, effective a g → g = g₀)
    (w w' : List Bool) (len : w.length = w'.length) (start : b < w.length)
    (bv : w.getD b false = v) (bv' : w'.getD b false = v)
    (equal : ∀ i, i ≠ a → w.getD i false = w'.getD i false) :
    ∀ i, i ≠ a → (gs.foldl advance w).getD i false = (gs.foldl advance w').getD i false := by
  induction gs generalizing w w' with
  | nil => exact equal
  | cons g gs ih =>
    have step : g.op.eval (g.inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      by_cases e : effective a g
      · have h := read g (by simp) e
        subst g
        exact absorb hb op bv bv'
      · exact unaffected equal e
    apply ih (fun h hh => read h (List.mem_cons_of_mem _ hh)) (advance w g) (advance w' g)
    · simp [advance,len]
    · simp [advance]; omega
    · exact (List.getD_append _ _ _ _ start).trans bv
    · exact (List.getD_append _ _ _ _ (len ▸ start)).trans bv'
    · intro i ia
      by_cases hi : i < w.length
      · exact (List.getD_append _ _ _ _ hi).trans ((equal i ia).trans (List.getD_append _ _ _ _ (len ▸ hi)).symm)
      · simp only [advance, List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hi),
          List.getD_append_right _ _ _ _ (show w'.length ≤ i by omega),step,len]

theorem isolate_of_witness
    (witness : ∀ (a b : Fin 10), a ≠ b → ∀ v : Bool,
      ∃ x y : Fin 10 → Bool, x b = v ∧ y b = v ∧ (∀ i, i ≠ a → x i = y i) ∧ target x ≠ target y)
    (C : Circuit) (neg : Bool) (a : Fin 10) (p : ℕ)
    (fan : FanInTwo C) (hx : exact C neg) (one : single C a p) : isolated C a p := by
  classical
  intro j g gj ea
  have jp := one j g gj ea
  refine ⟨jp,?_⟩
  by_cases hn : g.op = .not
  · exact Or.inl hn
  right
  intro k hk hlt
  by_contra neq
  let b : Fin 10 := ⟨k,hlt⟩
  have diff : a ≠ b := fun z => neq (congrArg Fin.val z).symm
  have gf := (fan g (List.mem_of_getElem? gj)).1
  have gr : g.op = .and ∨ g.op = .or := by
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at gf
    exact gf.elim Or.inl (fun h => Or.inr (h.resolve_right hn))
  let v := decide (g.op = .or)
  have oh : (v=false ∧ g.op=.and) ∨ (v=true ∧ g.op=.or) := by
    rcases gr with e|e <;> simp [v,e]
  obtain ⟨x,y,xb,yb,same,td⟩ := witness a b diff v
  have rr : ∀ t ∈ C.gates, effective a t → t=g := by
    intro t ht eff
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp ht
    have ij : i=j := (one i t hi eff).trans jp.symm
    subst i
    exact Option.some.inj (hi.symm.trans gj)
  have agree : ∀ i, i ≠ a.val → (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
    intro i ne
    by_cases il : i < 10
    · exact (rawbit x ⟨i,il⟩).trans ((same ⟨i,il⟩ (fun h => ne (congrArg Fin.val h))).trans (rawbit y ⟨i,il⟩).symm)
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none
        (show (List.ofFn x).length ≤ i by simpa using Nat.le_of_not_gt il),List.getElem?_eq_none
        (show (List.ofFn y).length ≤ i by simpa using Nat.le_of_not_gt il)]
  have ev : circuitFun 10 C x = circuitFun 10 C y :=
    fold_mask (b:=k) hk oh C.gates rr (List.ofFn x) (List.ofFn y) (by simp) (by simpa using hlt)
      ((rawbit x b).trans xb) ((rawbit y b).trans yb) agree C.output (not_raw C neg hx a)
  apply td
  rw [← hx x, ← hx y, ev]
end Obstruction
theorem isolate (C : Circuit) (neg : Bool) (a : Fin 10) (p : ℕ)
    (fan : FanInTwo C) (hx : exact C neg) (one : single C a p) : isolated C a p :=
  Obstruction.isolate_of_witness pin_witness C neg a p fan hx one
end PEqualNP.Outside.L_meta_7816_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_7816_aux

theorem PEqualNP.Outside.L_meta_7816 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool) (x3 : ℕ),   have x4 : (Fin (10 : ℕ) → Bool) → Bool := fun (x4 : Fin (10 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x5 : ℕ) => x4 (Fin.ofNat (10 : ℕ) (x5 / (10 : ℕ))) && x4 (Fin.ofNat (10 : ℕ) (x5 % (10 : ℕ)));   have x5 : ℕ → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) => x5 ∈ x6.inputs ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.not → x6.inputs.head? = Option.some x5);   have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x7 : Fin (10 : ℕ)) (x8 : Finset ℕ), (∀ x9 ∈ x8, ∃ (x11 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x9]? = Option.some x11 ∧ x5 (↑x7) x11) → x8.card ≤ x3;   have x7 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : ℕ) => ∀ (x9 : ℕ) (x10 : PEqualNP.CircuitLowerBounds.Gate), x7.gates[x9]? = Option.some x10 → x5 (0 : ℕ) x10 → x9 = x8 ∧ (x10.op = PEqualNP.CircuitLowerBounds.GateOp.not ∨ ∀ x13 ∈ x10.inputs, x13 < (10 : ℕ) → x13 = (0 : ℕ));   PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → x6 x1 → (∀ (x11 : Fin (10 : ℕ) → Bool), (if x2 = Bool.true then !PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 x11 else PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 x11) = x4 x11) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit) (x13 : ℕ), PEqualNP.MetaComplexity.FanInTwo x12 ∧ x12.size ≤ x1.size ∧ x6 x12 ∧ PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x12 = PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 ∧ x7 x12 x13 := by
  intro C neg k
  change FanInTwo C → C.size ≤ 18 → cap k C → PEqualNP.Outside.L_meta_7816_aux.exact C neg →
    ∃ (D : Circuit) (j : ℕ), FanInTwo D ∧ D.size ≤ C.size ∧ cap k D ∧
      circuitFun 10 D = circuitFun 10 C ∧ isolated D 0 j
  intro fan size hcap computes
  obtain ⟨D,heq,dfan,dsize,dcap,a,j,one⟩ := single_raw C k fan size hcap
  have dx : PEqualNP.Outside.L_meta_7816_aux.exact D neg := by
    intro x
    simpa only [heq] using computes x
  have iso : isolated D a j := isolate D neg a j dfan dx one
  obtain ⟨F,ffan,fsize,fcap,feq,fiso⟩ := relocate D neg k a j dfan dcap dx iso
  exact ⟨F,j,ffan,fsize.trans_le dsize,fcap,feq.trans heq,fiso⟩
