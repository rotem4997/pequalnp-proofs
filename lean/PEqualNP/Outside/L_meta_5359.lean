import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_5359
def edge (a b : Fin 42) := a.val < 21 ∧ 21 ≤ b.val ∧
  (b.val+21-a.val)%21 ∈ ([0,5,7,17,20] : List Nat)
def near (a b : Fin 42) := edge a b ∨ edge b a
def accepts (x : Fin 42 → Bool) := ∃ a b, edge a b ∧ x a=true ∧ x b=true
theorem separated : ∀ v p : Fin 42, v≠p → ∃ w : Fin 42, near v w ∧ ¬near p w := by
  letI (a b : Fin 42) : Decidable (near a b) := by unfold near edge; infer_instance
  decide
theorem no_loop (a : Fin 42) : ¬edge a a := fun h => (Nat.not_lt.mpr h.2.1) h.1
theorem rows (v p : Fin 42) (ne : p≠v) : ∃ x y : Fin 42 → Bool,
    x p=true ∧ y p=true ∧ (∀ i, i≠v → x i=y i) ∧ ¬accepts x ∧ accepts y := by
  obtain ⟨w,on,off⟩ := separated v p ne.symm
  let x (i : Fin 42) := decide (i=p ∨ i=w)
  let y (i : Fin 42) := decide (i=p ∨ i=w ∨ i=v)
  refine ⟨x,y,by simp [x],by simp [y],?_,?_,?_⟩
  · intro i hi
    simp [x,y,hi]
  · rintro ⟨a,b,e,pa,pb⟩
    simp only [x,decide_eq_true_eq] at pa pb
    rcases pa with rfl|rfl <;> rcases pb with rfl|rfl
    · exact no_loop _ e
    · exact off (Or.inl e)
    · exact off (Or.inr e)
    · exact no_loop _ e
  · have hv : y v=true := by simp [y]
    have hw : y w=true := by simp [y]
    rcases on with e|e
    · exact ⟨v,w,e,hv,hw⟩
    · exact ⟨w,v,e,hw,hv⟩
theorem singleton_off (v : Fin 42) : ¬accepts (fun k => decide (k=v)) := by
  rintro ⟨a,b,e,pa,pb⟩
  have aa : a=v := of_decide_eq_true pa
  have bb : b=v := of_decide_eq_true pb
  rw [aa,bb] at e
  exact no_loop v e

def onceCases (v a b c d : Nat) := (v=a ∧ v≠b ∧ v≠c ∧ v≠d) ∨
  (v≠a ∧ v=b ∧ v≠c ∧ v≠d) ∨ (v≠a ∧ v≠b ∧ v=c ∧ v≠d) ∨ (v≠a ∧ v≠b ∧ v≠c ∧ v=d)
theorem once_of_count {v a b c d : Nat} (h : [a,b,c,d].count v = 1) : onceCases v a b c d := by
  simp only [List.count_cons,List.count_nil,beq_iff_eq] at h
  unfold onceCases
  split_ifs at h <;> omega
def first (s : Fin 42) (x : Fin 42 → Bool) : Fin 43 → Bool := Fin.lastCases (x 0 || x s) x
def aug (s : Fin 42) (a b : Fin 43) (x : Fin 42 → Bool) : Fin 44 → Bool :=
  Fin.lastCases (first s x a || first s x b) (first s x)
theorem mask_exists (s v : Fin 42) (a b : Fin 43) (ab : a<b)
    (once : [0,s.val,a.val,b.val].count v.val=1) :
    ∃ p : Fin 42, p≠v ∧ ∀ x y : Fin 42 → Bool, x p=true → y p=true →
    (∀ i, i≠v → x i=y i) →
    (x 0 || x s)=(y 0 || y s) ∧ (first s x a || first s x b)=(first s y a || first s y b) := by
  have ha : a.val<42 := by have := b.isLt; change a.val<b.val at ab; omega
  let A : Fin 42 := ⟨a.val,ha⟩
  have ae : a=A.castSucc := Fin.ext rfl
  have cs := once_of_count once
  rcases cs with h|h|h|h
  · obtain ⟨z,ns,na,nb⟩ := h
    have vs : s≠v := fun eq => ns (congrArg Fin.val eq.symm)
    have va : A≠v := fun eq => na (congrArg Fin.val eq.symm)
    refine ⟨s,vs,?_⟩
    intro x y hx hy same
    have top : (x 0 || x s)=(y 0 || y s) := by simp [hx,hy]
    refine ⟨top,?_⟩
    rw [ae]; simp only [first,Fin.lastCases_castSucc]
    rw [same A va]
    by_cases hb : b.val<42
    · let B : Fin 42 := ⟨b.val,hb⟩
      rw [show b=B.castSucc from Fin.ext rfl,Fin.lastCases_castSucc,Fin.lastCases_castSucc,same B (fun eq => nb (congrArg Fin.val eq.symm))]
    · rw [show b=Fin.last 42 from Fin.ext (by have := b.isLt; change b.val=42; omega)]
      simp only [Fin.lastCases_last,top]
  · obtain ⟨nz,z,na,nb⟩ := h
    have v0 : (0 : Fin 42) ≠ v := fun eq => nz (congrArg Fin.val eq.symm)
    have va : A≠v := fun eq => na (congrArg Fin.val eq.symm)
    refine ⟨0,v0,?_⟩
    intro x y hx hy same
    have top : (x 0 || x s)=(y 0 || y s) := by simp [hx,hy]
    refine ⟨top,?_⟩
    rw [ae]; simp only [first,Fin.lastCases_castSucc]
    rw [same A va]
    by_cases hb : b.val<42
    · let B : Fin 42 := ⟨b.val,hb⟩
      rw [show b=B.castSucc from Fin.ext rfl,Fin.lastCases_castSucc,Fin.lastCases_castSucc,same B (fun eq => nb (congrArg Fin.val eq.symm))]
    · rw [show b=Fin.last 42 from Fin.ext (by have := b.isLt; change b.val=42; omega)]
      simp only [Fin.lastCases_last,top]
  · obtain ⟨nz,ns,_,nb⟩ := h
    have v0 : (0 : Fin 42) ≠ v := fun eq => nz (congrArg Fin.val eq.symm)
    have vs : s≠v := fun eq => ns (congrArg Fin.val eq.symm)
    by_cases hb : b.val<42
    · let B : Fin 42 := ⟨b.val,hb⟩
      refine ⟨B,fun eq => nb (congrArg Fin.val eq.symm),?_⟩
      intro x y hx hy same
      constructor
      · rw [same 0 v0,same s vs]
      · rw [show b=B.castSucc from Fin.ext rfl]
        simp [first,hx,hy]
    · refine ⟨0,v0,?_⟩
      intro x y hx hy same
      rw [show b=Fin.last 42 from Fin.ext (by have := b.isLt; change b.val=42; omega)]
      simp only [first,Fin.lastCases_last,hx,hy,Bool.true_or,Bool.or_true,and_self]
  · obtain ⟨nz,ns,na,_⟩ := h
    refine ⟨A,fun eq => na (congrArg Fin.val eq.symm),?_⟩
    intro x y hx hy same
    constructor
    · rw [same 0 (fun eq => nz (congrArg Fin.val eq.symm)),same s (fun eq => ns (congrArg Fin.val eq.symm))]
    · rw [ae]; simp [first,hx,hy]

open PEqualNP.CircuitLowerBounds
def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def run (gs : List Gate) (w : List Bool) := gs.foldl step w
lemma retained (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi
lemma ignoring (gs : List Gate) (v : Nat) (a b : List Bool) (sameLen : a.length=b.length)
    (same : ∀ i, i≠v → a.getD i false=b.getD i false) (unused : ∀ g∈gs,v∉g.inputs) :
    ∀ i, i≠v → (run gs a).getD i false = (run gs b).getD i false := by
  induction gs generalizing a b with
  | nil => exact same
  | cons g gs ih =>
    have reads : g.inputs.map (fun i => a.getD i false) = g.inputs.map (fun i => b.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact same i (fun eq => unused g (by simp) (eq ▸ hi))
    change ∀ i, i≠v → (run gs (step a g)).getD i false = (run gs (step b g)).getD i false
    apply ih _ _ (by simp [step,sameLen]) _ (fun q h => unused q (List.mem_cons_of_mem _ h))
    intro i ne
    by_cases lo : i<a.length
    · exact (List.getD_append _ _ _ _ lo).trans ((same i ne).trans (List.getD_append _ _ _ _ (by omega : i<b.length)).symm)
    · unfold step
      rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),reads,sameLen]

lemma raw (s : Fin 42) (a b : Fin 43) (x : Fin 42 → Bool) (v : Fin 42) :
    (List.ofFn (aug s a b x)).getD v.val false=x v := by
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; have := v.isLt; omega),List.getElem_ofFn]
  change aug s a b x (v.castSucc.castSucc) = _
  simp only [aug,first,Fin.lastCases_castSucc]
lemma or1 (s : Fin 42) (a b : Fin 43) (x : Fin 42 → Bool) :
    (List.ofFn (aug s a b x)).getD 42 false=(x 0 || x s) := by
  rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
  change aug s a b x ((Fin.last 42).castSucc) = _
  simp only [aug,first,Fin.lastCases_castSucc,Fin.lastCases_last]
lemma or2 (s : Fin 42) (a b : Fin 43) (x : Fin 42 → Bool) :
    (List.ofFn (aug s a b x)).getD 43 false=(first s x a || first s x b) := by
  rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
  change aug s a b x (Fin.last 43) = _
  simp only [aug,Fin.lastCases_last]
lemma outside_same (s v : Fin 42) (a b : Fin 43) (x y : Fin 42 → Bool)
    (same : ∀ i, i≠v → x i=y i) (rawOr : (x 0 || x s)=(y 0 || y s))
    (lastOr : (first s x a || first s x b)=(first s y a || first s y b)) :
    ∀ i, i≠v.val → (List.ofFn (aug s a b x)).getD i false=(List.ofFn (aug s a b y)).getD i false := by
  intro i ne
  by_cases lo : i<42
  · let j : Fin 42 := ⟨i,lo⟩
    exact (raw s a b x j).trans ((same j (fun eq => ne (congrArg Fin.val eq))).trans (raw s a b y j).symm)
  by_cases q : i=42
  · subst i; rw [or1,or1,rawOr]
  by_cases t : i=43
  · subst i; rw [or2,or2,lastOr]
  rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
end PEqualNP.Outside.L_meta_5359
open PEqualNP.Outside.L_meta_5359 PEqualNP.CircuitLowerBounds
theorem PEqualNP.Outside.L_meta_5359 : ∀ (x1 : Fin (42 : ℕ)) (x2 x3 : Fin (43 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x1 = (1 : Fin (42 : ℕ)) ∨ x1 = (21 : Fin (42 : ℕ)) ∨ x1 = (22 : Fin (42 : ℕ)) →     x2 < x3 →       (x2, x3) ≠ ((0 : Fin (43 : ℕ)), x1.castSucc) →         (x3 = Fin.last (42 : ℕ) → x2 ≠ (0 : Fin (43 : ℕ)) ∧ x2 ≠ x1.castSucc) →           (∀ (x9 : Fin (42 : ℕ) → Bool),               have x10 : Fin (43 : ℕ) → Bool := fun (x10 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x9 (0 : Fin (42 : ℕ)) || x9 x1) x9 x10;               x4.eval (List.ofFn fun (x11 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x10 x2 || x10 x3) x10 x11) = Bool.true ↔ ∃ (x11 : Fin (42 : ℕ)) (x12 : Fin (42 : ℕ)), (↑x11 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x12 ∧ (↑x12 + (21 : ℕ) - ↑x11) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x9 x11 = Bool.true ∧ x9 x12 = Bool.true) →             ∀ (x10 : Fin (42 : ℕ)), List.count ↑x10 [(0 : ℕ), ↑x1, ↑x2, ↑x3] = (1 : ℕ) → ∃ x12 ∈ x4.gates, ↑x10 ∈ x12.inputs := by
  intro s a b C _ ab _ _ law v count
  have correct (x : Fin 42 → Bool) : C.eval (List.ofFn (aug s a b x))=true ↔ accepts x := law x
  obtain ⟨p,ne,mask⟩ := mask_exists s v a b ab count
  obtain ⟨x,y,hx,hy,same,off,on⟩ := rows v p ne
  obtain ⟨h1,h2⟩ := mask x y hx hy same
  have out : C.output≠v.val := by
    intro eq
    let single (k : Fin 42) := decide (k=v)
    apply singleton_off v
    apply (correct single).mp
    change (run C.gates (List.ofFn (aug s a b single))).getD C.output false = true
    rw [eq,retained _ _ _ (by simp only [List.length_ofFn]; have := v.isLt; omega),raw]
    simp [single]
  by_contra no
  have unused : ∀ g∈C.gates, v.val∉g.inputs := fun g hg h => no ⟨g,hg,h⟩
  have equal := ignoring C.gates v.val _ _ (by simp only [List.length_ofFn]) (outside_same s v a b x y same h1 h2) unused C.output out
  exact off ((correct x).mp (equal.trans ((correct y).mpr on)))
