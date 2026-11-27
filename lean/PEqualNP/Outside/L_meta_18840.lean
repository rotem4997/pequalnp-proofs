import PEqualNP.Defs
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_meta_18840

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def FullRepSizeAtMost {n m : ℕ} (G : Fin n → Fin m → Bool) (s : ℕ) : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ Represents G C

private def value (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private def push (w : List Bool) (g : Gate) : List Bool := w ++ [value w g]

private def ao (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl push w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, push, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem fold_append (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl push w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t,h⟩ := ih (push w g)
    exact ⟨value w g :: t, by simpa [push, List.append_assoc] using h⟩

private theorem fold_read (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl push w).getD i false = w.getD i false := by
  obtain ⟨t, ht⟩ := fold_append gs w
  rw [ht, List.getD_append _ _ _ _ h]

private theorem push_read (w : List Bool) (g : Gate) :
    (push w g).getD w.length false = value w g := by
  rw [push, List.getD_append_right _ _ _ _ (le_refl _)]
  simp

private def shift (k : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (k + ·)⟩

private theorem shifted_fold (headW w : List Bool) (gs : List Gate) :
    (gs.map (shift headW.length)).foldl push (headW ++ w) =
      headW ++ gs.foldl push w := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    have read (j : ℕ) : (headW ++ w).getD (headW.length + j) false = w.getD j false := by
      rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
    have h : value (headW ++ w) (shift headW.length g) = value w g := by
      simp only [value, shift, List.map_map, Function.comp_def, read]
    simp only [List.map_cons, List.foldl_cons, push, h]
    simpa only [List.append_assoc] using ih (w ++ [value w g])

private theorem fixed_fold (gs : List Gate) (w : List Bool)
    (fixed : ∀ g ∈ gs, ∀ i ∈ g.inputs, i < w.length) :
    gs.foldl push w = w ++ gs.map (value w) := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    let a := value w g
    have carry : ∀ h ∈ gs, ∀ i ∈ h.inputs, i < w.length :=
      fun h hh => fixed h (List.mem_cons_of_mem _ hh)
    have same : gs.map (value (w ++ [a])) = gs.map (value w) := by
      apply List.map_congr_left
      intro h hh
      unfold value
      congr 1
      apply List.map_congr_left
      intro i hi
      exact List.getD_append _ _ _ _ (carry h hh i hi)
    have next : ∀ h ∈ gs, ∀ i ∈ h.inputs, i < (w ++ [a]).length := by
      intro h hh i hi
      have := carry h hh i hi
      simp
      omega
    change gs.foldl push (w ++ [a]) = _
    rw [ih (w ++ [a]) next, same]
    simp [a, List.append_assoc]

private theorem decide_eq {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    decide p = decide q := by
  by_cases hp : p
  · have hq := h.mp hp
    simp [hp,hq]
  · have hq := mt h.mpr hp
    simp [hp,hq]

private theorem one_read {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  unfold oneEach
  by_cases h : i < n
  · rw [List.getD_append _ _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h)]
    rw [List.getElem_ofFn]
    apply decide_eq
    simp only [Fin.ext_iff]
    omega
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h), List.length_ofFn]
    by_cases j : i - n < m
    · rw [List.getD_eq_getElem _ _ (by simpa using j), List.getElem_ofFn]
      apply decide_eq
      simp only [Fin.ext_iff]
      omega
    · symm
      rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt j), decide_eq_false_iff_not]
      omega

private def leftMix (n : ℕ) (u v : Fin (2*n)) : List Bool :=
  List.ofFn fun i : Fin n => decide (u.val = i.val ∨ v.val = n + i.val)

private def rightMix (n : ℕ) (u v : Fin (2*n)) : List Bool :=
  List.ofFn fun i : Fin n => decide (v.val = i.val ∨ u.val = n + i.val)

private def mixGates (n : ℕ) : List Gate :=
  List.ofFn (fun i : Fin n => ⟨.or,[i.val,3*n+i.val]⟩) ++
    List.ofFn (fun i : Fin n => ⟨.or,[2*n+i.val,n+i.val]⟩)

private theorem mix_ao (n : ℕ) : ∀ g ∈ mixGates n, ao g := by
  intro g h
  simp only [mixGates, List.mem_append, List.mem_ofFn] at h
  rcases h with ⟨i,rfl⟩ | ⟨i,rfl⟩ <;> simp [ao]

private theorem mix_eval (n : ℕ) (u v : Fin (2*n)) :
    (mixGates n).foldl push (oneEach u v) =
      oneEach u v ++ (leftMix n u v ++ rightMix n u v) := by
  rw [fixed_fold]
  · simp only [mixGates, List.map_append, List.map_ofFn]
    congr 1
    congr 1
    all_goals
      simp only [leftMix, rightMix]
      congr 1
      funext i
      have hi := i.isLt
      simp only [Function.comp_def, value, List.map_cons, List.map_nil, GateOp.eval,
        List.any_cons, List.any_nil, id_eq, Bool.or_false, one_read]
      apply Bool.eq_iff_iff.2
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      have hu := u.isLt
      have hv := v.isLt
      omega
  · intro g hg i hi
    simp only [mixGates, List.mem_append, List.mem_ofFn] at hg
    rcases hg with ⟨j,rfl⟩ | ⟨j,rfl⟩ <;>
      have hj := j.isLt <;>
      simp [oneEach] at hi ⊢ <;> omega

private def last (base a k : ℕ) : ℕ := if k = 0 then a else base+k-1

private def collect (base a k : ℕ) : List Gate :=
  (List.range k).map fun i => ⟨.or, [last base a i, a+i+1]⟩

private theorem collect_ao (base a k : ℕ) :
    ∀ g ∈ collect base a k, ao g := by
  intro g hg
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hg
  simp [ao]

private def reads (w : List Bool) (a k : ℕ) : Bool :=
  ((List.range k).map fun i => w.getD (a+i) false).any id

private theorem collect_eval (w : List Bool) (a k : ℕ) (bound : a+k < w.length) :
    ((collect w.length a k).foldl push w).getD (last w.length a k) false =
      reads w a (k+1) := by
  induction k with
  | zero => simp [last, collect, reads]
  | succ k ih =>
    have prev := ih (by omega)
    let gs := collect w.length a k
    let v := gs.foldl push w
    have vl : v.length = w.length + k := by simp [v, gs, fold_length, collect]
    have out : last w.length a (k+1) = v.length := by simp [last, vl]
    have second : v.getD (a+k+1) false = w.getD (a+k+1) false :=
      fold_read gs w _ (by omega)
    rw [show collect w.length a (k+1) = gs ++ [⟨.or,[last w.length a k,a+k+1]⟩] by
      simp [collect, gs, List.range_succ]]
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, out, push_read]
    simp only [value, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
    change (v.getD (last w.length a k) false || v.getD (a+k+1) false) = _
    rw [show v.getD (last w.length a k) false = reads w a (k+1) from prev, second]
    unfold reads
    rw [show List.range (k+1+1) = List.range (k+1) ++ [k+1] from List.range_succ]
    simp [List.any_append, Nat.add_assoc]

private theorem reads_true (w : List Bool) (a k : ℕ) :
    reads w a k = true ↔ ∃ i < k, w.getD (a+i) false = true := by
  simp [reads, List.any_eq_true]

private theorem mix_lengths (n : ℕ) (u v : Fin (2*n)) :
    (leftMix n u v).length = n ∧ (rightMix n u v).length = n := by
  simp [leftMix, rightMix]

private theorem read_left (n : ℕ) (u v : Fin (2*n)) (t : List Bool) (i : ℕ) (hi : i < n) :
    (oneEach u v ++ (leftMix n u v ++ rightMix n u v) ++ t).getD (4*n+i) false =
      decide (u.val = i ∨ v.val = n+i) := by
  have h : (oneEach u v).length = 4*n := by simp [oneEach]; omega
  rw [List.getD_append _ _ _ _ (by simp [h,leftMix,rightMix]; omega)]
  rw [List.getD_append_right _ _ _ _ (by omega), h, Nat.add_sub_cancel_left]
  rw [List.getD_append _ _ _ _ (by simpa [leftMix] using hi)]
  rw [leftMix, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

private theorem read_right (n : ℕ) (u v : Fin (2*n)) (t : List Bool) (i : ℕ) (hi : i < n) :
    (oneEach u v ++ (leftMix n u v ++ rightMix n u v) ++ t).getD (5*n+i) false =
      decide (v.val = i ∨ u.val = n+i) := by
  have h : (oneEach u v).length = 4*n := by simp [oneEach]; omega
  rw [List.getD_append _ _ _ _ (by simp [h,leftMix,rightMix]; omega)]
  rw [List.getD_append_right _ _ _ _ (by omega), h]
  rw [List.getD_append_right _ _ _ _ (by simp [leftMix]; omega)]
  rw [show 5*n+i-4*n-(leftMix n u v).length = i by simp [leftMix]; omega]
  rw [rightMix, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

private theorem mix_both (n : ℕ) (u v : Fin (2*n)) :
    ((u.val < n) ↔ (v.val < n)) →
      ∃ a b : Fin n, leftMix n u v ++ rightMix n u v = oneEach a b ∧
        ((u.val < n ∧ v.val < n ∧ a.val=u.val ∧ b.val=v.val) ∨
         (n ≤ u.val ∧ n ≤ v.val ∧ a.val=v.val-n ∧ b.val=u.val-n)) := by
  intro same
  have hu := u.isLt
  have hv := v.isLt
  by_cases h : u.val < n
  · have hv' := same.mp h
    refine ⟨⟨u.val,h⟩,⟨v.val,hv'⟩,?_,Or.inl ⟨h,hv',rfl,rfl⟩⟩
    simp only [oneEach, leftMix, rightMix]
    congr 1 <;> congr 1 <;> funext i <;> have hi := i.isLt <;> apply decide_eq <;>
      simp only [Fin.ext_iff] <;> omega
  · have hv' : ¬ v.val < n := fun hv' => h (same.mpr hv')
    refine ⟨⟨v.val-n,by omega⟩,⟨u.val-n,by omega⟩,?_,Or.inr ⟨by omega,by omega,rfl,rfl⟩⟩
    simp only [oneEach, leftMix, rightMix]
    congr 1 <;> congr 1 <;> funext i <;> have hi := i.isLt <;> apply decide_eq <;>
      simp only [Fin.ext_iff] <;> omega

set_option maxHeartbeats 1500000 in
theorem build (n : ℕ) (hn : 1 ≤ n) (G : ℕ → ℕ → Bool) (s : ℕ)
    (small : FullRepSizeAtMost (fun u v : Fin n => G u.val v.val) s) :
    FullRepSizeAtMost
      (fun u v : Fin (2*n) => decide ((u.val < n ∧ v.val < n ∧ G u.val v.val = true) ∨
        (n ≤ u.val ∧ n ≤ v.val ∧ G (v.val-n) (u.val-n) = true))) (s+4*n) := by
  obtain ⟨C, cm, cs, ce⟩ := small
  by_cases co : C.output < 2*n+C.size
  · let B := 6*n+C.size
    let k := n-1
    let g₁ := collect B (4*n) k
    let g₂ := collect (B+k) (5*n) k
    let and₁ : Gate := ⟨.and,[4*n+C.output,last B (4*n) k]⟩
    let and₂ : Gate := ⟨.and,[B+2*k,last (B+k) (5*n) k]⟩
    let D : Circuit :=
      ⟨mixGates n ++ C.gates.map (shift (4*n)) ++ g₁ ++ g₂ ++ [and₁,and₂], B+2*k+1⟩
    refine ⟨D, ?_, ?_, ?_⟩
    · intro g hg
      simp only [D, List.mem_append] at hg
      rcases hg with (((hm | hc) | h₁) | h₂) | hf
      · exact mix_ao n g hm
      · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hc
        simpa [ao, shift] using cm x hx
      · exact collect_ao _ _ _ _ h₁
      · exact collect_ao _ _ _ _ h₂
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl <;> simp [and₁,and₂]
    · simp [D, Circuit.size, mixGates, g₁, g₂, collect, k] at *
      omega
    · intro u v
      let w := oneEach u v
      let mix := leftMix n u v ++ rightMix n u v
      let W := w ++ C.wires mix
      let U := g₁.foldl push W
      let V := g₂.foldl push U
      have wl : w.length = 4*n := by simp [w,oneEach]; omega
      have ml : mix.length = 2*n := by simp [mix,leftMix,rightMix]; omega
      have lens : W.length = B := by
        change (w ++ (C.gates.foldl push mix)).length = _
        simp [B, wl, fold_length, ml, Circuit.size] <;> omega
      have lenU : U.length = B+k := by simp [U,fold_length,lens,g₁,collect]
      have lenV : V.length = B+2*k := by
        simp [V,fold_length,lenU,g₂,collect]
        omega
      have mid : (C.gates.map (shift (4*n))).foldl push ((mixGates n).foldl push w) = W := by
        rw [show (mixGates n).foldl push w = w ++ mix from mix_eval n u v, ← wl, shifted_fold]
        rfl
      have raw : V.getD (4*n+C.output) false = C.eval mix := by
        have hh : 4*n+C.output < W.length := by rw [lens]; dsimp [B]; omega
        have hh' : 4*n+C.output < U.length := by rw [lenU]; rw [lens] at hh; omega
        rw [show V.getD _ false = U.getD _ false from fold_read g₂ U _ hh',
          show U.getD _ false = W.getD _ false from fold_read g₁ W _ hh]
        change (w ++ C.wires mix).getD (4*n+C.output) false = _
        rw [List.getD_append_right _ _ _ _ (by omega), wl, Nat.add_sub_cancel_left]
        rfl
      have lcalc : U.getD (last B (4*n) k) false = reads W (4*n) n := by
        have := collect_eval W (4*n) k (by rw [lens]; dsimp [B,k]; omega)
        simpa [lens, U, g₁, show k+1=n by dsimp [k]; omega] using this
      have rcalc : V.getD (last (B+k) (5*n) k) false = reads U (5*n) n := by
        have := collect_eval U (5*n) k (by rw [lenU]; dsimp [B,k]; omega)
        simpa [lenU, V, g₂, show k+1=n by dsimp [k]; omega] using this
      have readL : (reads W (4*n) n = true) ↔ (u.val < n ∨ n ≤ v.val) := by
        rw [reads_true]
        obtain ⟨t, ht⟩ := fold_append C.gates mix
        have hW : W = w ++ mix ++ t := by
          change w ++ C.wires mix = _
          rw [show C.wires mix = mix ++ t from ht]
          simp [mix, List.append_assoc]
        have hr (i : ℕ) (hi : i<n) := read_left n u v t i hi
        have hv := v.isLt
        constructor
        · rintro ⟨i,hi,he⟩
          rw [hW, show (w ++ mix ++ t).getD (4*n+i) false = _ from hr i hi, decide_eq_true_eq] at he
          omega
        · intro he
          obtain hu | hv' := he
          · exact ⟨u.val,hu,by rw [hW, show (w ++ mix ++ t).getD (4*n+u.val) false = _ from hr u.val hu]; simp⟩
          · have hh : v.val-n<n := by omega
            refine ⟨v.val-n,hh,?_⟩
            rw [hW, show (w ++ mix ++ t).getD (4*n+(v.val-n)) false = _ from hr _ hh, decide_eq_true_eq]
            omega
      have readR : (reads U (5*n) n = true) ↔ (v.val < n ∨ n ≤ u.val) := by
        rw [reads_true]
        obtain ⟨t, ht⟩ := fold_append C.gates mix
        obtain ⟨t', ht'⟩ := fold_append g₁ W
        have hU : U = w ++ mix ++ (t ++ t') := by
          change g₁.foldl push W = _
          rw [ht']
          change (w ++ C.wires mix) ++ t' = _
          rw [show C.wires mix = mix ++ t from ht]
          simp [List.append_assoc]
        have hr (i : ℕ) (hi : i<n) := read_right n u v (t++t') i hi
        have hu := u.isLt
        constructor
        · rintro ⟨i,hi,he⟩
          rw [hU, show (w ++ mix ++ (t++t')).getD (5*n+i) false = _ from hr i hi, decide_eq_true_eq] at he
          omega
        · intro he
          obtain hv | hu' := he
          · exact ⟨v.val,hv,by rw [hU, show (w ++ mix ++ (t++t')).getD (5*n+v.val) false = _ from hr v.val hv]; simp⟩
          · have hh : u.val-n<n := by omega
            refine ⟨u.val-n,hh,?_⟩
            rw [hU, show (w ++ mix ++ (t++t')).getD (5*n+(u.val-n)) false = _ from hr _ hh, decide_eq_true_eq]
            omega
      have lbound : last B (4*n) k < U.length := by
        rw [lenU]
        simp only [last]
        split <;> dsimp [B] <;> omega
      have rbound : last (B+k) (5*n) k < V.length := by
        rw [lenV]
        simp only [last]
        split <;> dsimp [B] <;> omega
      change ((D.gates.foldl push w).getD D.output false) = _
      simp only [D,List.foldl_append,mid]
      change ((push (push V and₁) and₂).getD (B+2*k+1) false) = _
      have lens₁ : (push V and₁).length = B+2*k+1 := by simp [push,lenV]
      have afterR := List.getD_append V [value V and₁] false _ rbound
      rw [← lens₁,push_read]
      change ((push V and₁).getD (B+2*k) false &&
        ((push V and₁).getD (last (B+k) (5*n) k) false && true)) = _
      rw [Bool.and_true, ← lenV, push_read]
      rw [show (push V and₁).getD (last (B+k) (5*n) k) false = _ from afterR, rcalc]
      change ((V.getD (4*n+C.output) false && (V.getD (last B (4*n) k) false && true)) &&
        reads U (5*n) n) = _
      rw [Bool.and_true,raw,show V.getD (last B (4*n) k) false = U.getD (last B (4*n) k) false
        from fold_read g₂ U _ lbound,lcalc]
      by_cases hu : u.val < n <;> by_cases hv : v.val < n
      · obtain ⟨a,b,he,hcase⟩ := mix_both n u v (by omega)
        have hc : a.val=u.val ∧ b.val=v.val := by omega
        rw [show mix=oneEach a b from he, ce a b, readL.mpr (Or.inl hu),readR.mpr (Or.inl hv)]
        simpa [hu,hv,hc.1,hc.2,show ¬ n≤u.val by omega]
      · have hfalse : reads U (5*n) n = false := by
          simpa only [Bool.not_eq_true] using (show ¬ reads U (5*n) n = true by rw [readR]; omega)
        simp [hu,hv,hfalse,show ¬ n≤u.val by omega]
      · have hfalse : reads W (4*n) n = false := by
          simpa only [Bool.not_eq_true] using (show ¬ reads W (4*n) n = true by rw [readL]; omega)
        simp [hu,hv,hfalse,show ¬ n≤v.val by omega,show n≤u.val by omega]
      · obtain ⟨a,b,he,hcase⟩ := mix_both n u v (by omega)
        have hc : a.val=v.val-n ∧ b.val=u.val-n := by omega
        rw [show mix=oneEach a b from he,ce a b,readL.mpr (Or.inr (by omega)),
          readR.mpr (Or.inr (by omega))]
        simpa [hu,hv,hc.1,hc.2,show n≤u.val by omega,show n≤v.val by omega]
  · refine ⟨⟨[],4*n⟩, by simp [FanInTwo], by simp [Circuit.size], ?_⟩
    have empty (a b : Fin n) : G a.val b.val = false := by
      have e := ce a b
      change C.eval (oneEach a b) = G a.val b.val at e
      rw [← e, Circuit.eval, List.getD_eq_default]
      change (C.gates.foldl push (oneEach a b)).length ≤ C.output
      simp [fold_length, oneEach, Circuit.size] at *
      omega
    intro u v
    have hu := u.isLt
    have hv := v.isLt
    have hzero : (⟨[],4*n⟩ : Circuit).eval (oneEach u v) = false := by
      simp only [Circuit.eval,Circuit.wires,List.foldl_nil]
      apply List.getD_eq_default
      simp [oneEach]
      omega
    rw [hzero,eq_comm,decide_eq_false_iff_not]
    rintro (⟨a,b,h⟩ | ⟨a,b,h⟩)
    · simp [empty ⟨u.val,a⟩ ⟨v.val,b⟩] at h
    · simp [empty ⟨v.val-n,by omega⟩ ⟨u.val-n,by omega⟩] at h

theorem blk_congr {a b : ℕ} (F K : ℕ → ℕ → Bool) (s t : ℕ) (hab : a = b) (hst : s ≤ t)
    (hFK : ∀ u v, u < b → v < b → F u v = K u v)
    (h : FullRepSizeAtMost (fun u v : Fin a => F u.val v.val) s) :
    FullRepSizeAtMost (fun u v : Fin b => K u.val v.val) t := by
  subst hab
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, le_trans h2 hst, ?_⟩
  intro u v
  exact (h3 u v).trans (hFK u.val v.val u.isLt v.isLt)

theorem blk_size (s n k : ℕ) :
    s + 4 * n * (2 ^ k - 1) + 4 * (2 ^ k * n) ≤ s + 4 * n * (2 ^ (k + 1) - 1) := by
  obtain ⟨q, hq⟩ : ∃ q, 2 ^ k = q + 1 := ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  rw [pow_succ, hq]
  have e1 : q + 1 - 1 = q := Nat.add_sub_cancel q 1
  have e2 : (q + 1) * 2 - 1 = 2 * q + 1 := by omega
  rw [e1, e2]
  apply le_of_eq
  ring

theorem ds_step (b : ℕ) : (Nat.digits 2 b).sum = b % 2 + (Nat.digits 2 (b / 2)).sum := by
  rcases Nat.eq_zero_or_pos b with h | h
  · subst h
    simp
  · rw [Nat.digits_def' (by norm_num) h, List.sum_cons]

theorem ds_top (k : ℕ) : ∀ b, b < 2 ^ k → (Nat.digits 2 (b + 2 ^ k)).sum = (Nat.digits 2 b).sum + 1 := by
  induction k with
  | zero =>
    intro b hb
    have h0 : b = 0 := by simp at hb; omega
    subst h0
    rw [ds_step]
    simp
  | succ k ih =>
    intro b hb
    have hp : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
    rw [ds_step (b + 2 ^ (k + 1)), ds_step b]
    have e1 : (b + 2 ^ (k + 1)) % 2 = b % 2 := by rw [hp]; omega
    have e2 : (b + 2 ^ (k + 1)) / 2 = b / 2 + 2 ^ k := by rw [hp]; omega
    rw [e1, e2, ih (b / 2) (by rw [hp] at hb; omega)]
    omega

def blkT (n : ℕ) (G : ℕ → ℕ → Bool) (u v : ℕ) : Bool :=
  decide (u / n = v / n ∧
    (((Nat.digits 2 (u / n)).sum % 2 = 0 ∧ G (u % n) (v % n) = true) ∨
     ((Nat.digits 2 (u / n)).sum % 2 = 1 ∧ G (v % n) (u % n) = true)))

theorem tm_pt (n m : ℕ) (hn : 1 ≤ n) (G : ℕ → ℕ → Bool)
    (hd : ∀ c, c < m → (Nat.digits 2 (c + m)).sum = (Nat.digits 2 c).sum + 1) (u v : ℕ)
    (hu2 : u < 2 * (m * n)) (hv2 : v < 2 * (m * n)) :
    decide ((u < m * n ∧ v < m * n ∧ blkT n G u v = true) ∨
      (m * n ≤ u ∧ m * n ≤ v ∧ blkT n G (v - m * n) (u - m * n) = true)) = blkT n G u v := by
  have hn0 : 0 < n := hn
  rw [Bool.eq_iff_iff]
  simp only [blkT, decide_eq_true_eq]
  by_cases hu : u < m * n <;> by_cases hv : v < m * n
  · constructor
    · rintro (⟨_, _, h⟩ | ⟨h, _, _⟩)
      · exact h
      · omega
    · intro h
      exact Or.inl ⟨hu, hv, h⟩
  · have h1 : u / n < m := (Nat.div_lt_iff_lt_mul hn0).2 hu
    have h2 : m ≤ v / n := (Nat.le_div_iff_mul_le hn0).2 (by omega)
    constructor
    · rintro (⟨_, h, _⟩ | ⟨h, _, _⟩) <;> omega
    · rintro ⟨h, _⟩
      omega
  · have h1 : v / n < m := (Nat.div_lt_iff_lt_mul hn0).2 hv
    have h2 : m ≤ u / n := (Nat.le_div_iff_mul_le hn0).2 (by omega)
    constructor
    · rintro (⟨h, _, _⟩ | ⟨_, h, _⟩) <;> omega
    · rintro ⟨h, _⟩
      omega
  · obtain ⟨a, rfl⟩ : ∃ a, u = a + m * n := ⟨u - m * n, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, v = b + m * n := ⟨v - m * n, by omega⟩
    have ha : a / n < m := (Nat.div_lt_iff_lt_mul hn0).2 (by omega)
    have ea : a + m * n - m * n = a := Nat.add_sub_cancel a (m * n)
    have eb : b + m * n - m * n = b := Nat.add_sub_cancel b (m * n)
    rw [ea, eb, Nat.add_mul_div_right a m hn0, Nat.add_mul_div_right b m hn0,
      Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right, hd (a / n) ha]
    by_cases hab : a / n = b / n
    · rw [← hab]
      generalize G (a % n) (b % n) = p
      generalize G (b % n) (a % n) = q
      cases p <;> cases q <;> simp <;> omega
    · constructor
      · rintro (⟨h, _, _⟩ | ⟨_, _, h, _⟩)
        · omega
        · omega
      · rintro ⟨h, _⟩
        omega

theorem tm_gen (n : ℕ) (hn : 1 ≤ n) (G : ℕ → ℕ → Bool) (s : ℕ)
    (hrep : FullRepSizeAtMost (fun u v : Fin n => G u.val v.val) s) (k : ℕ) :
    FullRepSizeAtMost (fun u v : Fin (2 ^ k * n) => blkT n G u.val v.val)
      (s + 4 * n * (2 ^ k - 1)) := by
  induction k with
  | zero =>
    refine blk_congr G (blkT n G) s (s + 4 * n * (2 ^ 0 - 1)) (by simp) (by simp) ?_ hrep
    intro u v hu hv
    simp only [pow_zero, one_mul] at hu hv
    simp only [blkT, Nat.div_eq_of_lt hu, Nat.div_eq_of_lt hv, Nat.mod_eq_of_lt hu,
      Nat.mod_eq_of_lt hv]
    simp
  | succ k ih =>
    have hN : 1 ≤ 2 ^ k * n := by
      have := Nat.one_le_two_pow (n := k)
      nlinarith
    have t := build (2 ^ k * n) hN (blkT n G) (s + 4 * n * (2 ^ k - 1)) ih
    have hb : 2 ^ (k + 1) * n = 2 * (2 ^ k * n) := by ring
    exact blk_congr
      (fun u v => decide ((u < 2 ^ k * n ∧ v < 2 ^ k * n ∧ blkT n G u v = true) ∨
        (2 ^ k * n ≤ u ∧ 2 ^ k * n ≤ v ∧ blkT n G (v - 2 ^ k * n) (u - 2 ^ k * n) = true)))
      (blkT n G) _ _ (by ring) (blk_size s n k)
      (fun u v hu hv => tm_pt n (2 ^ k) hn G (ds_top k) u v (by omega) (by omega)) t

theorem main_aux : ∀ (n j : ℕ), 1 ≤ n → ∀ (G : ℕ → ℕ → Bool) (s : ℕ),
  FullRepSizeAtMost (fun u v : Fin n => G u.val v.val) s →
  FullRepSizeAtMost
    (fun u v : Fin (2 ^ j * n) => decide (u.val / n = v.val / n ∧
      (((Nat.digits 2 (u.val / n)).sum % 2 = 0 ∧ G (u.val % n) (v.val % n) = true) ∨
       ((Nat.digits 2 (u.val / n)).sum % 2 = 1 ∧ G (v.val % n) (u.val % n) = true))))
    (s + 4 * n * (2 ^ j - 1)) := by
  intro n j hn G s hrep
  exact tm_gen n hn G s hrep j

end PEqualNP.Outside.L_meta_18840

theorem PEqualNP.Outside.L_meta_18840 :
    ∀ (n j : ℕ), 1 ≤ n → ∀ (G : ℕ → ℕ → Bool) (s : ℕ),
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧
     PEqualNP.Represents.Represents (fun u v : Fin n => G u.val v.val) C) →
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s + 4 * n * (2 ^ j - 1) ∧
     PEqualNP.Represents.Represents
       (fun u v : Fin (2 ^ j * n) => decide (u.val / n = v.val / n ∧
         (((Nat.digits 2 (u.val / n)).sum % 2 = 0 ∧ G (u.val % n) (v.val % n) = true) ∨
          ((Nat.digits 2 (u.val / n)).sum % 2 = 1 ∧ G (v.val % n) (u.val % n) = true)))) C := PEqualNP.Outside.L_meta_18840.main_aux
