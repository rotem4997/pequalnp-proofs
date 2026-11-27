import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_4861
open PEqualNP.CircuitLowerBounds
-- Effective-read simulation and gate erasure are adapted from L-meta-3580 by chloebrett.
def rd (g : Gate) : List ℕ := List.take (bif g.op.eval [false] then 1 else 2) g.inputs

def F (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl F x := rfl

def OkGate (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem ok_of_fan (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C) (g : Gate) (hg : g ∈ C.gates) :
    OkGate g := by
  obtain ⟨h1, h2⟩ := h g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact ⟨h1, h2⟩

theorem evalRd (g : Gate) (hg : OkGate g) (f f' : ℕ → Bool) (h : ∀ i ∈ rd g, f i = f' i) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  obtain ⟨hop, hl⟩ := hg
  rcases hop with hop | hop | hop
  · have : rd g = g.inputs := by
      simp only [rd, hop, GateOp.eval]
      exact List.take_of_length_le (by simpa using hl)
    rw [this] at h
    rw [List.map_congr_left h]
  · have : rd g = g.inputs := by
      simp only [rd, hop, GateOp.eval]
      exact List.take_of_length_le (by simpa using hl)
    rw [this] at h
    rw [List.map_congr_left h]
  · rw [hop]
    simp only [rd, hop, GateOp.eval] at h
    cases hin : g.inputs with
    | nil => simp
    | cons a t =>
      rw [hin] at h
      simp only [List.map_cons]
      rw [h a (by simp)]
      simp [GateOp.eval]

theorem fold_len (gs : List Gate) (w : List Bool) : (gs.foldl F w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [F, List.length_append, List.length_cons, List.length_nil]
    omega

def dl (w i : ℕ) : ℕ := if i < w then i else i - 1

def rg (w : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (dl w)⟩

theorem F_rg (Q Q' : List Bool) (w : ℕ) (g : Gate) (hg : OkGate g)
    (h : ∀ i ∈ rd g, Q'.getD (dl w i) false = Q.getD i false) :
    (rg w g).op.eval ((rg w g).inputs.map fun i => Q'.getD i false)
      = g.op.eval (g.inputs.map fun i => Q.getD i false) := by
  simp only [rg, List.map_map]
  exact evalRd g hg _ _ h

theorem stageA (w : ℕ) (A : List Gate) (hA : ∀ g ∈ A, OkGate g ∧ w ∉ rd g) :
    ∀ Q : List Bool, Q.length + A.length ≤ w → (A.map (rg w)).foldl F Q = A.foldl F Q := by
  induction A with
  | nil => intro Q _; rfl
  | cons g A ih =>
    intro Q hQ
    simp only [List.map_cons, List.foldl_cons]
    have hg := hA g (by simp)
    have hF : F Q (rg w g) = F Q g := by
      unfold F
      rw [F_rg Q Q w g hg.1]
      intro i hi
      have hne : i ≠ w := fun h => hg.2 (h ▸ hi)
      simp only [List.length_cons] at hQ
      by_cases hiw : i < w
      · simp [dl, hiw]
      · simp only [dl, hiw, ite_false]
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    rw [hF]
    apply ih (fun g' hg' => hA g' (by simp [hg']))
    simp only [F, List.length_append, List.length_cons, List.length_nil, List.length_cons] at hQ ⊢
    omega

theorem key (P M : List Bool) (v : Bool) (w : ℕ) (hP : P.length = w) (i : ℕ) (hi : i ≠ w) :
    (P ++ M).getD (dl w i) false = (P ++ v :: M).getD i false := by
  by_cases hiw : i < w
  · simp only [dl, hiw, ite_true]
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
  · simp only [dl, hiw, ite_false]
    rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hP]
    obtain ⟨k, hk⟩ : ∃ k, i - w = k + 1 := ⟨i - w - 1, by omega⟩
    rw [hk, List.getD_cons_succ]
    congr 1
    omega

theorem stageB (w : ℕ) (P : List Bool) (v : Bool) (hP : P.length = w) (B : List Gate)
    (hB : ∀ g ∈ B, OkGate g ∧ w ∉ rd g) :
    ∀ M : List Bool, ∀ i, i ≠ w →
      ((B.map (rg w)).foldl F (P ++ M)).getD (dl w i) false = (B.foldl F (P ++ v :: M)).getD i false := by
  induction B with
  | nil => intro M i hi; exact key P M v w hP i hi
  | cons g B ih =>
    intro M i hi
    simp only [List.map_cons, List.foldl_cons]
    have hg := hB g (by simp)
    have h1 : F (P ++ M) (rg w g) = P ++ (M ++ [g.op.eval (g.inputs.map fun i => (P ++ v :: M).getD i false)]) := by
      unfold F
      rw [F_rg (P ++ v :: M) (P ++ M) w g hg.1, List.append_assoc]
      intro i hi
      exact key P M v w hP i (fun h => hg.2 (h ▸ hi))
    have h2 : F (P ++ v :: M) g = P ++ v :: (M ++ [g.op.eval (g.inputs.map fun i => (P ++ v :: M).getD i false)]) := by
      unfold F
      simp
    rw [h1, h2]
    exact ih (fun g' hg' => hB g' (by simp [hg'])) _ i hi

theorem del_getD (n j : ℕ) (gs : List Gate) (hj : j < gs.length)
    (hok : ∀ g ∈ gs, OkGate g) (hw : ∀ g ∈ gs, n + j ∉ rd g) (x : List Bool) (hx : x.length = n)
    (i : ℕ) (hi : i ≠ n + j) :
    (((gs.eraseIdx j).map (rg (n + j))).foldl F x).getD (dl (n + j) i) false
      = (gs.foldl F x).getD i false := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j gs]
    rw [List.drop_eq_getElem_cons hj]
  have herase : gs.eraseIdx j = gs.take j ++ gs.drop (j + 1) := List.eraseIdx_eq_take_drop_succ gs j
  have hAll : ∀ g ∈ gs, OkGate g ∧ n + j ∉ rd g := fun g hg => ⟨hok g hg, hw g hg⟩
  rw [herase, List.map_append, List.foldl_append]
  conv_rhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [stageA (n + j) (gs.take j) (fun g hg => hAll g (List.mem_of_mem_take hg)) x
    (by rw [hx, List.length_take]; omega)]
  have hP : (List.foldl F x (gs.take j)).length = n + j := by
    rw [fold_len, hx, List.length_take]; omega
  have := stageB (n + j) (List.foldl F x (gs.take j))
    (gs[j].op.eval (gs[j].inputs.map fun i => (List.foldl F x (gs.take j)).getD i false)) hP
    (gs.drop (j + 1)) (fun g hg => hAll g (List.mem_of_mem_drop hg)) [] i hi
  simpa [F] using this

theorem indep (k : ℕ) (gs : List Gate) (hok : ∀ g ∈ gs, OkGate g) (hk : ∀ g ∈ gs, k ∉ rd g) :
    ∀ Q Q' : List Bool, Q.length = Q'.length → (∀ i, i ≠ k → Q.getD i false = Q'.getD i false) →
      ∀ i, i ≠ k → (gs.foldl F Q).getD i false = (gs.foldl F Q').getD i false := by
  induction gs with
  | nil => intro Q Q' _ h i hi; exact h i hi
  | cons g gs ih =>
    intro Q Q' hl h i hi
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hok g' (by simp [hg'])) (fun g' hg' => hk g' (by simp [hg']))
    · simp [F, hl]
    · intro i' hi'
      have hv : g.op.eval (g.inputs.map fun i => Q.getD i false)
          = g.op.eval (g.inputs.map fun i => Q'.getD i false) := by
        apply evalRd g (hok g (by simp))
        intro j hj
        exact h j (fun e => hk g (by simp) (e ▸ hj))
      unfold F
      rw [hv]
      by_cases hlt : i' < Q.length
      · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
        exact h i' hi'
      · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
    · exact hi

theorem count (gs : List Gate) (hok : ∀ g ∈ gs, OkGate g) :
    (gs.flatMap rd).length + (gs.filter fun g => g.op.eval [false]).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have ih' := ih (fun g' hg' => hok g' (by simp [hg']))
    have hg : (rd g).length + (if g.op.eval [false] = true then 1 else 0) ≤ 2 := by
      rcases (hok g (by simp)).1 with h | h | h <;> simp [rd, h, GateOp.eval]
    rw [List.flatMap_cons, List.filter_cons, List.length_append]
    split_ifs at hg ⊢ with hc
    · simp only [List.length_cons]
      omega
    · simp only [List.length_cons]
      omega

open PEqualNP.MetaComplexity

def accesses (C : Circuit) := C.output :: C.gates.flatMap rd

theorem internal {n : Nat} {C : Circuit} (fan : FanInTwo C)
    (minimal : ∀ s, HasCircuitSize n (circuitFun n C) s → C.size ≤ s)
    (j : Fin C.gates.length) : n+j.val ∈ accesses C := by
  by_contra unread
  have absent : n+j.val ≠ C.output ∧ n+j.val ∉ C.gates.flatMap rd := by
    simpa [accesses] using unread
  have nog (g) (hg : g ∈ C.gates) : n+j.val ∉ rd g :=
    fun h => absent.2 (List.mem_flatMap.mpr ⟨g,hg,h⟩)
  let D : Circuit := ⟨(C.gates.eraseIdx j.val).map (rg (n+j.val)),dl (n+j.val) C.output⟩
  have dFan : FanInTwo D := by
    intro g hg
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
    simpa [rg] using fan v (List.mem_of_mem_eraseIdx hv)
  have dSize : D.size=C.gates.length-1 := by
    simp [D,Circuit.size,List.length_eraseIdx_of_lt j.isLt]
  have same (x : Fin n → Bool) : D.eval (List.ofFn x) = circuitFun n C x := by
    unfold circuitFun Circuit.eval
    rw [wires_eq,wires_eq]
    exact del_getD n j.val _ j.isLt (ok_of_fan C fan) nog _ (by simp) _ absent.1.symm
  have h := minimal _ ⟨D,dFan,le_rfl,same⟩
  change C.gates.length ≤ D.size at h
  have positive := j.isLt
  omega

theorem passenger {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {T : Finset (Fin n)} {C : Circuit} (fan : FanInTwo C)
    (correct : circuitFun n C=NestedCover.graphFun G T) (p : Fin n) (hp : p∈T) :
    p.val ∈ accesses C := by
  by_contra unread
  have absent : p.val≠C.output ∧ p.val∉C.gates.flatMap rd := by simpa [accesses] using unread
  let x : Fin n → Bool := fun _ => false
  let y : Fin n → Bool := fun i => decide (i=p)
  have same : circuitFun n C x = circuitFun n C y := by
    unfold circuitFun Circuit.eval
    rw [wires_eq,wires_eq]
    apply indep p.val C.gates (ok_of_fan C fan)
      (fun g hg h => absent.2 (List.mem_flatMap.mpr ⟨g,hg,h⟩)) _ _ (by simp) _ C.output absent.1.symm
    intro i hi
    by_cases hin : i<n
    · rw [List.getD_eq_getElem _ _ (by simpa using hin),List.getD_eq_getElem _ _ (by simpa using hin),
        List.getElem_ofFn,List.getElem_ofFn]
      have hne : (⟨i,hin⟩ : Fin n) ≠ p := fun h => hi (congrArg Fin.val h)
      simp [x,y,hne]
    · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
  rw [correct] at same
  have pos : ∃ a∈T, y a=true := ⟨p,hp,by simp [y]⟩
  simp [NestedCover.graphFun,x,pos] at same

theorem readers (gs : List Gate) (i : Nat) :
    (gs.filter (fun g => (rd g).contains i)).length ≤ (gs.flatMap rd).count i := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    rw [List.flatMap_cons,List.count_append,List.filter_cons]
    split
    · rename_i h
      have positive : 0 < (rd g).count i := List.count_pos_iff.mpr (by simpa using h)
      simp only [List.length_cons]
      omega
    · omega

theorem mass (S : Finset Nat) (R : List Nat) :
    (∑ i ∈ S, R.count i) ≤ R.length := by
  induction R with
  | nil => simp
  | cons a r ih =>
    simp only [List.count_cons,beq_iff_eq,Finset.sum_add_distrib,List.length_cons]
    by_cases ha : a ∈ S <;> simp [ha] <;> omega

theorem countSlots {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (T : Finset (Fin n)) (C : Circuit) (fan : FanInTwo C)
    (correct : circuitFun n C=NestedCover.graphFun G T)
    (minimal : ∀ s, HasCircuitSize n (NestedCover.graphFun G T) s → C.size ≤ s) :
    T.card + (∑ i ∈ Tᶜ, (C.gates.filter (fun g => (rd g).contains i.val)).length) +
      (C.gates.filter (fun g => g.op.eval [false])).length ≤ C.size + 1 := by
  let R := accesses C
  have one (i : Nat) (h : i∈R) : 1 ≤ R.count i := List.count_pos_iff.mpr h
  have left : T.card ≤ ∑ i∈T, R.count i.val := by
    calc
      T.card = ∑ _i∈T, (1:Nat) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i hi => one _ (passenger fan correct i hi)
  have right : (∑ i∈Tᶜ, (C.gates.filter (fun g => (rd g).contains i.val)).length) ≤
      ∑ i∈Tᶜ, R.count i.val := by
    apply Finset.sum_le_sum
    intro i hi
    have h := readers C.gates i.val
    change _ ≤ (C.output :: C.gates.flatMap rd).count i.val
    rw [List.count_cons]
    omega
  have inner : C.size ≤ ∑ j : Fin C.gates.length, R.count (n+j.val) := by
    calc
      C.size = ∑ _j : Fin C.gates.length, (1:Nat) := by simp [Circuit.size]
      _ ≤ _ := Finset.sum_le_sum fun j _ => one _ (internal fan (by rwa [correct]) j)
  have allRaw : (∑ i ∈ T, R.count i.val)+(∑ i∈Tᶜ, R.count i.val) =
      ∑ i : Fin n, R.count i.val := Finset.sum_add_sum_compl T _
  have combined : (∑ i : Fin n,R.count i.val)+(∑ j : Fin C.gates.length,R.count (n+j.val)) ≤ R.length := by
    have h := mass (Finset.range (n+C.gates.length)) R
    rw [Finset.sum_range_add] at h
    rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range] at h
    exact h
  have total := count C.gates (ok_of_fan C fan)
  have len : R.length=(C.gates.flatMap rd).length+1 := rfl
  change _ ≤ C.gates.length+1
  change C.gates.length ≤ _ at inner
  omega

end PEqualNP.Outside.L_meta_4861

theorem PEqualNP.Outside.L_meta_4861 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 → (∀ (x8 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4) x8 → x5.size ≤ x8) → x4.card + ∑ x9 ∈ x4ᶜ, (List.filter (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x10.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x10.inputs).contains ↑x9) x5.gates).length + (List.filter (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => x9.op.eval [Bool.false]) x5.gates).length ≤ x5.size + (1 : ℕ) := by
  intro n G d T C fan correct minimal
  exact PEqualNP.Outside.L_meta_4861.countSlots T C fan correct minimal
