import PEqualNP.Defs
import Mathlib.Data.List.GetD
namespace PEqualNP.Outside.L_meta_18417
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def index {n m : ℕ} (f : Fin n → Fin m) (s : ℕ) (i : ℕ) : ℕ :=
  if h : i < n then (f ⟨i,h⟩).val else m+s+(i-n)

private def gate (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map f⟩
private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma before {n m : ℕ} (f : Fin n → Fin m) (s len : ℕ) (i : ℕ) (h : i < n+len) :
    index f s i < m+s+len := by
  unfold index
  split
  · have := (f ⟨i,by assumption⟩).isLt; omega
  · omega

private lemma read {n m : ℕ} (x : Fin m → Bool) (f : Fin n → Fin m) (s t : List Bool) (i : ℕ) :
    ((List.ofFn x ++ s) ++ t).getD (index f s.length i) false =
      (List.ofFn (fun j => x (f j)) ++ t).getD i false := by
  by_cases h : i < n
  · simp only [index,dif_pos h]
    rw [List.getD_append _ _ _ _ (by simp; have := (f ⟨i,h⟩).isLt;omega),
      List.getD_append _ _ _ _ (by simp),List.getD_append _ _ _ _ (by simpa using h)]
    simp [List.getD_eq_getElem?_getD,List.getElem?_ofFn,h]
  · simp only [index,dif_neg h]
    rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp;omega)]
    simp

private lemma simulate {n m : ℕ} (x : Fin m → Bool) (f : Fin n → Fin m)
    (s : List Bool) (gs : List Gate) (t : List Bool) :
    ∃ u, u.length = t.length+gs.length ∧
      gs.foldl step (List.ofFn (fun i => x (f i)) ++ t) = List.ofFn (fun i => x (f i)) ++ u ∧
      (gs.map (gate (index f s.length))).foldl step ((List.ofFn x ++ s) ++ t) =
        (List.ofFn x ++ s) ++ u := by
  induction gs generalizing t with
  | nil => exact ⟨t,by simp,rfl,rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => (List.ofFn (fun j => x (f j)) ++ t).getD i false)
    have eh : (gate (index f s.length) g).op.eval
        ((gate (index f s.length) g).inputs.map fun i => ((List.ofFn x ++ s) ++ t).getD i false) = v := by
      simp only [gate,v,List.map_map,Function.comp_apply]
      congr 1
      exact List.map_congr_left fun i _ => read x f s t i
    obtain ⟨u,lu,hu,hu'⟩ := ih (t ++ [v])
    refine ⟨u,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using lu,?_,?_⟩
    · simp only [List.foldl_cons,step,List.append_assoc]
      exact hu
    · simp only [List.map_cons,List.foldl_cons,step]
      rw [eh]
      simp only [List.append_assoc]
      simpa only [List.append_assoc] using hu'

theorem parallelCopies (C : Circuit) (q : ℕ) (hm : Monotone2 C)
    (ho : C.output < 17+C.size) (hq : q < 17+C.size) (f g : Fin 17 → Fin 25) :
    ∃ (B : Circuit) (r : ℕ), Monotone2 B ∧ B.size ≤ 2*C.size+2 ∧
      B.output < 25+B.size ∧ r < 25+B.size ∧ ∀ x : Fin 25 → Bool,
      let a := List.ofFn (fun i => x (f i))
      let b := List.ofFn (fun i => x (g i))
      B.eval (List.ofFn x) = (C.eval a || C.eval b) ∧
      (B.wires (List.ofFn x)).getD r false = ((C.wires a).getD q false || (C.wires b).getD q false) := by
  let l := C.size
  let seqA := C.gates.map (gate (index f 0))
  let seqB := C.gates.map (gate (index g l))
  let top : Gate := ⟨.or,[index f 0 C.output, index g l C.output]⟩
  let aux : Gate := ⟨.or,[index f 0 q, index g l q]⟩
  let o := 25+l+l
  let B : Circuit := ⟨seqA ++ seqB ++ [top,aux],o⟩
  have size : B.size = 2*l+2 := by simp [B,seqA,seqB,Circuit.size,l]; omega
  refine ⟨B,o+1,?_,size.le,by change o < 25+B.size; dsimp [o]; omega,by dsimp [o]; omega,?_⟩
  · intro k hk
    change k ∈ seqA ++ seqB ++ [top,aux] at hk
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hk
    have legal (φ : ℕ → ℕ) (h : k ∈ C.gates.map (gate φ)) : k.op ∈ ({.and,.or} : Set GateOp) ∧ k.inputs.length ≤ 2 := by
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp h
      simpa [gate] using hm u hu
    rcases hk with (h|h) | h | h
    · exact legal _ h
    · exact legal _ h
    · subst k; simp [top]
    · subst k; simp [aux]
  intro x
  obtain ⟨ta,la,ea,pa⟩ := simulate x f [] C.gates []
  simp only [List.length_nil, Nat.zero_add,List.append_nil] at la ea pa
  obtain ⟨tb,lb,eb,pb⟩ := simulate x g ta C.gates []
  simp only [List.length_nil, Nat.zero_add,List.append_nil] at lb eb pb
  let a := List.ofFn (fun i => x (f i))
  let b := List.ofFn (fun i => x (g i))
  let w := (List.ofFn x ++ ta) ++ tb
  have wlen : w.length = o := by simp only [w,o,l, List.length_append,List.length_ofFn,la,lb,Circuit.size]
  have simulation : (seqA ++ seqB).foldl step (List.ofFn x) = w := by
    rw [List.foldl_append]
    change (C.gates.map (gate (index g l))).foldl step
      ((C.gates.map (gate (index f 0))).foldl step (List.ofFn x)) = w
    rw [pa]
    simpa only [w,l,Circuit.size,la] using pb
  have readA (i : ℕ) (hi : i < 17+l) :
      w.getD (index f 0 i) false = (C.wires a).getD i false := by
    change ((List.ofFn x ++ ta) ++ tb).getD _ _ = (C.gates.foldl step a).getD i false
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append,List.length_ofFn,la]; have hh := before f 0 l i hi; simpa only [l,Circuit.size,Nat.add_zero] using hh),ea]
    simpa only [List.append_nil,List.length_nil] using read x f [] ta i
  have readB (i : ℕ) : w.getD (index g l i) false = (C.wires b).getD i false := by
    change _ = (C.gates.foldl step b).getD i false
    rw [eb]
    simpa only [w,l,Circuit.size,la] using read x g ta tb i
  let val1 := C.eval a || C.eval b
  let val2 := (C.wires a).getD q false || (C.wires b).getD q false
  have ht : step w top = w ++ [val1] := by
    simp only [step,top,List.map_cons,List.map_nil,readA C.output ho,readB,GateOp.eval, List.any_cons,
      List.any_nil,id_eq,Bool.or_false]
    rfl
  have ha (i : ℕ) (hi : i < o) : (w ++ [val1]).getD i false = w.getD i false :=
    List.getD_append _ _ _ _ (wlen ▸ hi)
  have hu : step (w ++ [val1]) aux = (w ++ [val1]) ++ [val2] := by
    have l1 : index f 0 q < o := by have := before f 0 l q hq; dsimp [o];omega
    have l2 : index g l q < o := before g l l q hq
    simp only [step,aux,List.map_cons,List.map_nil,ha _ l1,ha _ l2,readA q hq,readB,GateOp.eval,
      List.any_cons,List.any_nil,id_eq,Bool.or_false]
    rfl
  have full : B.wires (List.ofFn x) = (w ++ [val1]) ++ [val2] := by
    change ((seqA ++ seqB) ++ [top,aux]).foldl step _ = _
    rw [List.foldl_append,simulation]
    change step (step w top) aux = _
    rw [ht,hu]
  change (B.wires (List.ofFn x)).getD o false = val1 ∧ (B.wires (List.ofFn x)).getD (o+1) false = val2
  rw [full, ← wlen]
  simp [List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_18417

theorem PEqualNP.Outside.L_meta_18417 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.output < (17 : ℕ) + x1.size →       x2 < (17 : ℕ) + x1.size →         ∀ (x6 x7 : Fin (17 : ℕ) → Fin (25 : ℕ)),           ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : ℕ),             PEqualNP.MetaComplexity.Monotone2 x8 ∧               x8.size ≤ (2 : ℕ) * x1.size + (2 : ℕ) ∧                 x8.output < (25 : ℕ) + x8.size ∧                   x9 < (25 : ℕ) + x8.size ∧                     ∀ (x10 : Fin (25 : ℕ) → Bool),                       have x11 : List Bool := List.ofFn fun (x11 : Fin (17 : ℕ)) => x10 (x6 x11);                       have x12 : List Bool := List.ofFn fun (x12 : Fin (17 : ℕ)) => x10 (x7 x12);                       x8.eval (List.ofFn x10) = (x1.eval x11 || x1.eval x12) ∧ (x8.wires (List.ofFn x10)).getD x9 Bool.false = ((x1.wires x11).getD x2 Bool.false || (x1.wires x12).getD x2 Bool.false) := PEqualNP.Outside.L_meta_18417.parallelCopies
