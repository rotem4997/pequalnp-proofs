import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17201_aux
-- The wire evaluation identities below are adapted from L-meta-4145.
namespace Internal4111
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false
theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

abbrev W {n : ℕ} (C : Circuit) (u v : Fin n) (i : ℕ) (x : Fin n → Bool) :=
  val C.gates i (Function.update (Function.update x u false) v false)

theorem compile {n : ℕ} (C : Circuit) (u v : Fin n) (S : Finset ℕ)
    (fan : FanInTwo C) (bounds : ∀ j∈S, j < C.size)
    (dup : ∀ j∈S, (∀ x, W C u v (n+j) x = false) ∨ ∃ i < n+j, W C u v (n+j) = W C u v i) :
    ∃ s, s + S.card ≤ C.size ∧ HasCircuitSize n (fun x =>
      circuitFun n C (Function.update (Function.update x u false) v false)) s := by
  classical
  let z := n + C.size
  let Rep := fun (gs : List Gate) (i : ℕ) => ∃ a : ℕ,
    (a < n + gs.length ∨ a = z) ∧ ∀ x, val gs a x = W C u v i x
  have go (k : ℕ) (hk : k ≤ C.size) : ∃ gs : List Gate,
      FanInTwo ⟨gs,0⟩ ∧ gs.length + (S.filter (· < k)).card = k ∧
      ∀ i < n+k, Rep gs i := by
    induction k with
    | zero =>
      refine ⟨[], by simp [FanInTwo], by simp, ?_⟩
      intro i hi
      have il : i < n := by omega
      let j : Fin n := ⟨i,il⟩
      by_cases pin : j = u ∨ j = v
      · refine ⟨z, Or.inr rfl, fun x => ?_⟩
        rw [val_big _ _ _ (by simp [z]), W,val_input _ _ _ il]
        rcases pin with h|h <;> simp [← show j.val=i from rfl, show (⟨i,il⟩ : Fin n)=j from rfl,h,Function.update_apply]
      · refine ⟨i, Or.inl (by simpa), fun x => ?_⟩
        rw [val_input _ _ _ il,W,val_input _ _ _ il]
        have h1 : j ≠ u := fun h => pin (.inl h)
        have h2 : j ≠ v := fun h => pin (.inr h)
        simp [show (⟨i,il⟩ : Fin n)=j from rfl,h1,h2,Function.update_apply]
    | succ k ih =>
      obtain ⟨gs,hg,cnt,rep⟩ := ih (by omega)
      have small : gs.length ≤ k := by omega
      have newCount : S.filter (· < k+1) = if k∈S then insert k (S.filter (· < k)) else S.filter (· < k) := by
        ext j
        by_cases eq : j=k
        · subst j; by_cases h : k∈S <;> simp [h]
        · have lt : j ≤ k ↔ j < k := by omega
          by_cases h : k∈S <;> simp [h,eq,lt]
      have outsideFilter : k ∉ S.filter (· < k) := by simp
      by_cases h : k∈S
      · refine ⟨gs,hg,by rw [newCount,if_pos h,Finset.card_insert_of_notMem outsideFilter]; omega,?_⟩
        intro i hi
        by_cases old : i < n+k
        · exact rep i old
        have eq : i=n+k := by omega
        subst i
        rcases dup k h with zero|⟨j,jl,same⟩
        · exact ⟨z,Or.inr rfl,fun x => (val_big gs x z (by dsimp [z];omega)).trans (zero x).symm⟩
        · obtain ⟨a,ha,r⟩ := rep j jl
          exact ⟨a,ha,fun x => (r x).trans (congrFun same x).symm⟩
      · have kl : k < C.gates.length := by change k < C.size; omega
        let g := C.gates[k]
        have source (i : ℕ) : ∃ a : ℕ, (a < n+gs.length ∨ a=z) ∧ ∀ x : Fin n → Bool,
            val gs a x = (wf (C.gates.take k) (List.ofFn (Function.update (Function.update x u false) v false))).getD i false := by
          by_cases hi : i<n+k
          · obtain ⟨a,ha,ra⟩ := rep i hi
            exact ⟨a,ha,fun x => (ra x).trans (wire_take _ _ k i (by simpa using hi) (by omega))⟩
          · exact ⟨z,Or.inr rfl,fun x => (val_big _ _ _ (by dsimp [z];omega)).trans
              (List.getD_eq_default _ _ (by rw [wf_len,List.length_ofFn,List.length_take,Nat.min_eq_left (by omega : k ≤ C.gates.length)]; omega)).symm⟩
        let idx := fun i => (source i).choose
        let newGate : Gate := ⟨g.op,g.inputs.map idx⟩
        let ns := gs ++ [newGate]
        have outputEq (x : Fin n → Bool) : val ns (n+gs.length) x = W C u v (n+k) x := by
          have old := gate_val C.gates (List.ofFn (Function.update (Function.update x u false) v false)) k kl
          rw [List.length_ofFn] at old
          unfold W val
          rw [old]
          change (wf (gs ++ [newGate]) (List.ofFn x)).getD _ false = _
          rw [wf_snoc]
          have leq : (wf gs (List.ofFn x)).length = n+gs.length := by simp [wf_len]
          rw [←leq,getD_snoc_eq]
          apply congrArg g.op.eval
          simp only [newGate,List.map_map]
          exact List.map_congr_left (fun i _ => (source i).choose_spec.2 x)
        refine ⟨ns,?_,by rw [newCount,if_neg h]; simp only [ns,List.length_append,List.length_singleton]; omega,?_⟩
        · intro q hq
          change q ∈ gs ++ [newGate] at hq
          rcases List.mem_append.mp hq with hq|hq
          · exact hg q hq
          · have heq : q=newGate := by simpa using hq
            subst q
            have ok := fan g (List.getElem_mem kl)
            simpa [newGate] using ok
        · intro i hi
          by_cases prior : i < n+k
          · obtain ⟨a,ha,ra⟩ := rep i prior
            refine ⟨a,ha.imp_left (fun lt => by simp [ns];omega),fun x => ?_⟩
            rcases ha with al|rfl
            · exact (wf_prefix gs [newGate] (List.ofFn x) a (by simpa using al)).trans (ra x)
            · exact (val_big ns x _ (by simp [z,ns];omega)).trans ((val_big gs x _ (by simp [z];omega)).symm.trans (ra x))
          · have same : i=n+k := by omega
            exact ⟨n+gs.length,Or.inl (by simp [ns]),same ▸ outputEq⟩
  obtain ⟨gs,fanGs,count,reps⟩ := go C.size le_rfl
  have full : S.filter (· < C.size) = S := Finset.filter_true_of_mem bounds
  rw [full] at count
  by_cases out : C.output < n+C.size
  · obtain ⟨a,_,resultEq⟩ := reps _ out
    exact ⟨gs.length, count.le, ⟨gs,a⟩,fanGs,le_rfl,resultEq⟩
  · exact ⟨0,by omega,⟨[],n⟩,by simp [FanInTwo],le_rfl,fun x => (val_big [] x n (by simp)).trans
        (val_big C.gates _ C.output (by change n+C.size ≤ C.output;omega)).symm⟩
end Internal4111




open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem pin_two_columns : ∀ (n : ℕ) (C : Circuit) (u v : Fin n) (S : Finset ℕ),
    FanInTwo C → (let W := fun (i : ℕ) (x : Fin n → Bool) =>
        PEqualNP.LowMerge.wireVal C (List.ofFn (Function.update (Function.update x u false) v false)) i
      ∀ j ∈ S, j < C.size ∧ ((∀ x, W (n+j) x = false) ∨ ∃ i < n+j, W (n+j) = W i)) →
    ∃ s, s + S.card ≤ C.size ∧ HasCircuitSize n
      (fun x => circuitFun n C (Function.update (Function.update x u false) v false)) s := by
  intro n C u v S fan q
  exact Internal4111.compile C u v S fan (fun j hj => (q j hj).1) (fun j hj => (q j hj).2)
end PEqualNP.Outside.L_meta_17201_aux

theorem PEqualNP.Outside.L_meta_17201 :
∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin x1) (x5 : Finset ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     (have x7 : ℕ → (Fin x1 → Bool) → Bool := fun (x7 : ℕ) (x8 : Fin x1 → Bool) => PEqualNP.LowMerge.wireVal x2 (List.ofFn (Function.update (Function.update x8 x3 Bool.false) x4 Bool.false)) x7;       ∀ x8 ∈ x5, x8 < x2.size ∧ ((∀ (x10 : Fin x1 → Bool), x7 (x1 + x8) x10 = Bool.false) ∨ ∃ x10 < x1 + x8, x7 (x1 + x8) = x7 x10)) →       ∃ (x8 : ℕ), x8 + x5.card ≤ x2.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x9 : Fin x1 → Bool) => PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update (Function.update x9 x3 Bool.false) x4 Bool.false)) x8 := by
  exact PEqualNP.Outside.L_meta_17201_aux.pin_two_columns
