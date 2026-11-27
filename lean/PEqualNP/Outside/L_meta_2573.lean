import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2573

open PEqualNP.CircuitLowerBounds

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

def reGate (ρ : ℕ → ℕ) (g : Gate) : Gate := Gate.mk g.op (g.inputs.map ρ)

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stepW x).getD C.output false := rfl

lemma getD_snoc_len (l : List Bool) (b : Bool) (n : ℕ) (h : n = l.length) :
    (l ++ [b]).getD n false = b := by
  subst h; simp

lemma fold_len (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma wires_len (C : Circuit) (x : List Bool) : (C.wires x).length = x.length + C.size :=
  fold_len C.gates x

lemma fold_shape (gs : List Gate) :
    ∀ w : List Bool, ∃ u : List Bool, u.length = gs.length ∧ gs.foldl stepW w = w ++ u := by
  induction gs with
  | nil => intro w; exact ⟨[], rfl, by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨u, hu, he⟩ := ih (stepW w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ u, ?_, ?_⟩
    · simp [hu]
    · rw [List.foldl_cons, he]
      simp [stepW]

lemma fold_old (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  obtain ⟨u, _, he⟩ := fold_shape gs w
  rw [he, List.getD_append _ _ _ _ h]

lemma getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

lemma getD_ofFn_fin {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD i.val false = f i :=
  getD_ofFn f i.val i.isLt

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  rw [wires_eq, fold_old _ _ _ (by simp), getD_ofFn_fin]

lemma or_eval2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  show (a || (b || false)) = _
  rw [Bool.or_false]

lemma and_eval2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  show (a && (b && true)) = _
  rw [Bool.and_true]

lemma final_op (op : GateOp) (U : List Bool) (p q n : ℕ) (hn : n = U.length) :
    (stepW U (Gate.mk op [p, q])).getD n false = op.eval [U.getD p false, U.getD q false] :=
  getD_snoc_len _ _ _ hn

lemma reGate_op (ρ : ℕ → ℕ) (g : Gate) : (reGate ρ g).op = g.op := rfl

lemma reGate_len (ρ : ℕ → ℕ) (g : Gate) : (reGate ρ g).inputs.length = g.inputs.length := by
  show (g.inputs.map ρ).length = _
  rw [List.length_map]

lemma snoc (n : ℕ) (f : Fin n → Bool) (v : Bool) :
    List.ofFn f ++ [v] = List.ofFn (fun i : Fin (n + 1) => (Fin.lastCases v f i : Bool)) := by
  rw [List.ofFn_succ' (fun i : Fin (n + 1) => (Fin.lastCases v f i : Bool))]
  simp

lemma snoc2 (n : ℕ) (f : Fin n → Bool) (v w : Bool) :
    (List.ofFn f ++ [v]) ++ [w] = List.ofFn (fun j : Fin (n + 1 + 1) =>
      (Fin.lastCases w (fun i : Fin (n + 1) => (Fin.lastCases v f i : Bool)) j : Bool)) := by
  rw [snoc n f v]
  exact snoc (n + 1) _ w

lemma cons_ofFn (n : ℕ) (f : Fin n → Bool) (b : Bool) :
    b :: List.ofFn f = List.ofFn (Fin.cons b f : Fin (n + 1) → Bool) := by
  rw [List.ofFn_succ]
  simp

lemma prepend_wires (gs : List Gate) (C : Circuit) (x : List Bool) :
    (Circuit.mk (gs ++ C.gates) C.output).wires x = C.wires (gs.foldl stepW x) := by
  show (gs ++ C.gates).foldl stepW x = C.gates.foldl stepW (gs.foldl stepW x)
  rw [List.foldl_append]

lemma prepend_gates (gs : List Gate) (C : Circuit) (x : List Bool) :
    (Circuit.mk (gs ++ C.gates) C.output).eval x = C.eval (gs.foldl stepW x) := by
  show ((gs ++ C.gates).foldl stepW x).getD C.output false
    = (C.gates.foldl stepW (gs.foldl stepW x)).getD C.output false
  rw [List.foldl_append]

lemma prepend_size (gs : List Gate) (C : Circuit) :
    (Circuit.mk (gs ++ C.gates) C.output).size = C.size + gs.length := by
  show (gs ++ C.gates).length = C.gates.length + gs.length
  rw [List.length_append, Nat.add_comm]

lemma prepend_all (P : Gate → Prop) (gs : List Gate) (C : Circuit) (hgs : ∀ g ∈ gs, P g)
    (hC : ∀ g ∈ C.gates, P g) : ∀ g ∈ (Circuit.mk (gs ++ C.gates) C.output).gates, P g := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact hgs g h
  · exact hC g h

lemma prepend_mono (gs : List Gate) (C : Circuit)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.MetaComplexity.Monotone2 (Circuit.mk (gs ++ C.gates) C.output) :=
  prepend_all _ gs C hgs hC

lemma bin_ok (c : Bool) (a b : ℕ) :
    (Gate.mk (if c = true then GateOp.and else GateOp.or) [a, b]).op
        ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      (Gate.mk (if c = true then GateOp.and else GateOp.or) [a, b]).inputs.length ≤ 2 := by
  cases c <;> simp

lemma cons_mono (c : Bool) (a b : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.MetaComplexity.Monotone2
      (Circuit.mk (Gate.mk (if c = true then GateOp.and else GateOp.or) [a, b] :: C.gates)
        C.output) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact bin_ok c a b
  · exact hC g hg

lemma prepend1 (n : ℕ) (g : Gate) (C : Circuit) (x : Fin n → Bool) (v : Bool)
    (hv : g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = v) :
    (Circuit.mk (g :: C.gates) C.output).eval (List.ofFn x)
      = C.eval (List.ofFn (fun i : Fin (n + 1) => (Fin.lastCases v x i : Bool))) := by
  subst hv
  rw [← snoc n x]
  rfl

lemma prepend_or (n : ℕ) (a b : Fin n) (C : Circuit) (x : Fin n → Bool) :
    (Circuit.mk (Gate.mk GateOp.or [a.val, b.val] :: C.gates) C.output).eval (List.ofFn x)
      = C.eval (List.ofFn (fun i : Fin (n + 1) => (Fin.lastCases (x a || x b) x i : Bool))) := by
  refine prepend1 n _ C x _ ?_
  show GateOp.or.eval [(List.ofFn x).getD a.val false, (List.ofFn x).getD b.val false] = _
  rw [or_eval2, getD_ofFn_fin, getD_ofFn_fin]

lemma prepend_and (n : ℕ) (a b : Fin n) (C : Circuit) (x : Fin n → Bool) :
    (Circuit.mk (Gate.mk GateOp.and [a.val, b.val] :: C.gates) C.output).eval (List.ofFn x)
      = C.eval (List.ofFn (fun i : Fin (n + 1) => (Fin.lastCases (x a && x b) x i : Bool))) := by
  refine prepend1 n _ C x _ ?_
  show GateOp.and.eval [(List.ofFn x).getD a.val false, (List.ofFn x).getD b.val false] = _
  rw [and_eval2, getD_ofFn_fin, getD_ofFn_fin]

lemma prepend_ite (n : ℕ) (c : Bool) (a b : Fin n) (C : Circuit) (x : Fin n → Bool) :
    (Circuit.mk (Gate.mk (if c = true then GateOp.and else GateOp.or) [a.val, b.val] :: C.gates)
        C.output).eval (List.ofFn x)
      = C.eval (List.ofFn (fun i : Fin (n + 1) =>
          (Fin.lastCases (if c = true then x a && x b else x a || x b) x i : Bool))) := by
  cases c
  · exact prepend_or n a b C x
  · exact prepend_and n a b C x

lemma exists_front1 (n : ℕ) (c : Bool) (a b : Fin n) (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ C.size + 1 ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x)
        = C.eval (List.ofFn (fun i : Fin (n + 1) =>
            (Fin.lastCases (if c = true then x a && x b else x a || x b) x i : Bool))) :=
  ⟨Circuit.mk (Gate.mk (if c = true then GateOp.and else GateOp.or) [a.val, b.val] :: C.gates)
      C.output, cons_mono c _ _ C hC, le_refl _, fun x => prepend_ite n c a b C x⟩

lemma exists_front2 (n : ℕ) (c1 c2 : Bool) (a b : Fin n) (c d : Fin (n + 1)) (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ C.size + 2 ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x)
        = C.eval (List.ofFn (fun j : Fin (n + 1 + 1) =>
            (Fin.lastCases
              (if c2 = true then
                (Fin.lastCases (if c1 = true then x a && x b else x a || x b) x c : Bool) &&
                (Fin.lastCases (if c1 = true then x a && x b else x a || x b) x d : Bool)
              else
                (Fin.lastCases (if c1 = true then x a && x b else x a || x b) x c : Bool) ||
                (Fin.lastCases (if c1 = true then x a && x b else x a || x b) x d : Bool))
              (fun i : Fin (n + 1) =>
                (Fin.lastCases (if c1 = true then x a && x b else x a || x b) x i : Bool))
              j : Bool))) :=
  ⟨Circuit.mk (Gate.mk (if c1 = true then GateOp.and else GateOp.or) [a.val, b.val] ::
      Gate.mk (if c2 = true then GateOp.and else GateOp.or) [c.val, d.val] :: C.gates) C.output,
    cons_mono c1 _ _ (Circuit.mk (Gate.mk (if c2 = true then GateOp.and else GateOp.or)
      [c.val, d.val] :: C.gates) C.output) (cons_mono c2 _ _ C hC),
    le_refl _,
    fun x => (prepend_ite n c1 a b (Circuit.mk (Gate.mk (if c2 = true then GateOp.and
      else GateOp.or) [c.val, d.val] :: C.gates) C.output) x).trans
        (prepend_ite (n + 1) c2 c d C _)⟩

lemma fold_pair (P Q : List Bool) (ρ : ℕ → ℕ)
    (hρ : ∀ (v : List Bool) (i : ℕ), (P ++ v).getD (ρ i) false = (Q ++ v).getD i false)
    (gs : List Gate) :
    ∀ v : List Bool, ∃ v' : List Bool, v'.length = v.length + gs.length ∧
      gs.foldl stepW (Q ++ v) = Q ++ v' ∧
      (gs.map (reGate ρ)).foldl stepW (P ++ v) = P ++ v' := by
  induction gs with
  | nil => intro v; exact ⟨v, by simp, rfl, rfl⟩
  | cons g gs ih =>
    intro v
    obtain ⟨v', hl, h1, h2⟩ :=
      ih (v ++ [g.op.eval (g.inputs.map fun i => (Q ++ v).getD i false)])
    have hm : (g.inputs.map ρ).map (fun i => (P ++ v).getD i false)
        = g.inputs.map (fun i => (Q ++ v).getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => hρ v i)
    refine ⟨v', ?_, ?_, ?_⟩
    · simp at hl ⊢; omega
    · rw [List.foldl_cons, ← h1]
      simp [stepW]
    · rw [List.map_cons, List.foldl_cons, ← h2]
      have hs : stepW (P ++ v) (reGate ρ g)
          = P ++ (v ++ [g.op.eval (g.inputs.map fun i => (Q ++ v).getD i false)]) := by
        show (P ++ v) ++ [g.op.eval ((g.inputs.map ρ).map fun i => (P ++ v).getD i false)] = _
        rw [hm, List.append_assoc]
      rw [hs]

lemma renumber (P Q : List Bool) (ρ : ℕ → ℕ)
    (hρ : ∀ (v : List Bool) (i : ℕ), (P ++ v).getD (ρ i) false = (Q ++ v).getD i false)
    (D : Circuit) :
    ((D.gates.map (reGate ρ)).foldl stepW P).getD (ρ D.output) false = D.eval Q := by
  obtain ⟨v', _, h1, h2⟩ := fold_pair P Q ρ hρ D.gates []
  rw [List.append_nil] at h1 h2
  rw [h2, hρ v' D.output, ← h1]
  rfl

def rot (n i : ℕ) : ℕ := if i = 0 then n else if i ≤ n then i - 1 else i

lemma rot_spec (n : ℕ) (X : List Bool) (hX : X.length = n) (v : Bool) (u : List Bool) (i : ℕ) :
    ((X ++ [v]) ++ u).getD (rot n i) false = ((v :: X) ++ u).getD i false := by
  subst hX
  have hL : (X ++ [v]) ++ u = X ++ (v :: u) := by simp
  have hR : (v :: X) ++ u = v :: (X ++ u) := rfl
  rw [hL, hR]
  rcases i with _ | j
  · have e : rot X.length 0 = X.length := by simp [rot]
    rw [e, List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  · by_cases h : j < X.length
    · have h1 : j + 1 ≤ X.length := h
      have e : rot X.length (j + 1) = j := by simp [rot, h1]
      rw [e, List.getD_append _ _ _ _ h, List.getD_cons_succ, List.getD_append _ _ _ _ h]
    · have h1 : ¬ (j + 1 ≤ X.length) := by omega
      have e : rot X.length (j + 1) = j + 1 := by simp [rot, h1]
      have e2 : j + 1 - X.length = (j - X.length) + 1 := by omega
      rw [e, List.getD_cons_succ, List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), e2, List.getD_cons_succ]

lemma front_cons_eval (n : ℕ) (g : Gate) (C : Circuit) (x : Fin n → Bool) :
    (Circuit.mk (g :: C.gates.map (reGate (rot n))) (rot n C.output)).eval (List.ofFn x)
      = C.eval (g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) :: List.ofFn x) := by
  show ((C.gates.map (reGate (rot n))).foldl stepW (List.ofFn x ++
      [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)])).getD
        (rot n C.output) false = _
  exact renumber _ _ (rot n) (fun u i => rot_spec n (List.ofFn x) (by simp) _ u i) C

lemma bin_val (n : ℕ) (c : Bool) (a b : Fin n) (x : Fin n → Bool) :
    (Gate.mk (if c = true then GateOp.and else GateOp.or) [a.val, b.val]).op.eval
        ((Gate.mk (if c = true then GateOp.and else GateOp.or) [a.val, b.val]).inputs.map
          fun i => (List.ofFn x).getD i false)
      = (if c = true then x a && x b else x a || x b) := by
  cases c
  · show GateOp.or.eval [(List.ofFn x).getD a.val false, (List.ofFn x).getD b.val false]
      = (x a || x b)
    rw [or_eval2, getD_ofFn_fin, getD_ofFn_fin]
  · show GateOp.and.eval [(List.ofFn x).getD a.val false, (List.ofFn x).getD b.val false]
      = (x a && x b)
    rw [and_eval2, getD_ofFn_fin, getD_ofFn_fin]

lemma exists_front_cons (n : ℕ) (c : Bool) (a b : Fin n) (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ C.size + 1 ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x)
        = C.eval ((if c = true then x a && x b else x a || x b) :: List.ofFn x) := by
  refine ⟨Circuit.mk (Gate.mk (if c = true then GateOp.and else GateOp.or) [a.val, b.val] ::
    C.gates.map (reGate (rot n))) (rot n C.output), ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact bin_ok c _ _
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      have := hC g' hg'
      exact ⟨this.1, by rw [reGate_len]; exact this.2⟩
  · simp [Circuit.size]
  · intro x
    rw [front_cons_eval, bin_val]

def rho (M k : ℕ) (σ : Fin k → Fin M) (i : ℕ) : ℕ :=
  if h : i < k then (σ ⟨i, h⟩).val else M + (i - k)

def safeOut (M s o : ℕ) : ℕ := if o < M then o else M + s

lemma rho_spec (M k : ℕ) (σ : Fin k → Fin M) (W : List Bool) (hW : W.length = M)
    (v : List Bool) (i : ℕ) :
    (W ++ v).getD (rho M k σ i) false
      = ((List.ofFn fun j : Fin k => W.getD (σ j).val false) ++ v).getD i false := by
  subst hW
  by_cases h : i < k
  · have hr : rho W.length k σ i = (σ ⟨i, h⟩).val := by simp [rho, h]
    rw [hr, List.getD_append _ _ _ _ (σ ⟨i, h⟩).isLt,
      List.getD_append _ _ _ _ (by simpa using h), getD_ofFn _ i h]
  · have h' : k ≤ i := Nat.le_of_not_lt h
    have hr : rho W.length k σ i = W.length + (i - k) := by simp [rho, h]
    rw [hr, List.getD_append_right _ _ _ _ (Nat.le_add_right _ _),
      List.getD_append_right _ _ _ _ (by simpa using h'), Nat.add_sub_cancel_left]
    simp

lemma safeOut_spec (W v : List Bool) (M s o : ℕ) (hW : W.length = M) (hv : v.length = s) :
    (W ++ v).getD (safeOut M s o) false = W.getD o false := by
  by_cases h : o < M
  · have e : safeOut M s o = o := by simp [safeOut, h]
    rw [e, List.getD_append _ _ _ _ (by omega)]
  · have e : safeOut M s o = M + s := by simp [safeOut, h]
    rw [e, List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

def substC (m k : ℕ) (C D : Circuit) (σ : Fin k → Fin (m + C.size)) : Circuit :=
  Circuit.mk (C.gates ++ D.gates.map (reGate (rho (m + C.size) k σ)))
    (rho (m + C.size) k σ D.output)

def comp (op : GateOp) (m k : ℕ) (C D : Circuit) (σ : Fin k → Fin (m + C.size)) : Circuit :=
  Circuit.mk (C.gates ++ (D.gates.map (reGate (rho (m + C.size) k σ)) ++
    [Gate.mk op [safeOut (m + C.size) D.size C.output, rho (m + C.size) k σ D.output]]))
    (m + C.size + D.size)

lemma subst_eval (m k : ℕ) (C D : Circuit) (σ : Fin k → Fin (m + C.size)) (x : Fin m → Bool) :
    (substC m k C D σ).eval (List.ofFn x)
      = D.eval (List.ofFn fun j : Fin k => (C.wires (List.ofFn x)).getD (σ j).val false) := by
  have hW : (C.gates.foldl stepW (List.ofFn x)).length = m + C.size := by
    rw [fold_len]; simp [Circuit.size]
  show ((C.gates ++ D.gates.map (reGate (rho (m + C.size) k σ))).foldl stepW
      (List.ofFn x)).getD (rho (m + C.size) k σ D.output) false = _
  rw [List.foldl_append]
  exact renumber _ _ _ (rho_spec (m + C.size) k σ _ hW) D

lemma subst_size (m k : ℕ) (C D : Circuit) (σ : Fin k → Fin (m + C.size)) :
    (substC m k C D σ).size = C.size + D.size := by
  show (C.gates ++ D.gates.map (reGate (rho (m + C.size) k σ))).length = _
  rw [List.length_append, List.length_map]
  rfl

lemma subst_mono (m k : ℕ) (C D : Circuit) (σ : Fin k → Fin (m + C.size))
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (hD : PEqualNP.MetaComplexity.Monotone2 D) :
    PEqualNP.MetaComplexity.Monotone2 (substC m k C D σ) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hC g hg
  · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    have := hD g' hg'
    exact ⟨this.1, by rw [reGate_len]; exact this.2⟩

lemma comp_eval (op : GateOp) (m k : ℕ) (C D : Circuit) (σ : Fin k → Fin (m + C.size))
    (x : Fin m → Bool) :
    (comp op m k C D σ).eval (List.ofFn x)
      = op.eval [C.eval (List.ofFn x),
          D.eval (List.ofFn fun j : Fin k => (C.wires (List.ofFn x)).getD (σ j).val false)] := by
  have hW : (C.gates.foldl stepW (List.ofFn x)).length = m + C.size := by
    rw [fold_len]; simp [Circuit.size]
  obtain ⟨v', hl, h1, h2⟩ := fold_pair (C.gates.foldl stepW (List.ofFn x))
    (List.ofFn fun j : Fin k => (C.gates.foldl stepW (List.ofFn x)).getD (σ j).val false)
    (rho (m + C.size) k σ) (rho_spec (m + C.size) k σ _ hW) D.gates []
  rw [List.append_nil] at h1 h2
  have hl' : v'.length = D.size := by simpa [Circuit.size] using hl
  show ((C.gates ++ (D.gates.map (reGate (rho (m + C.size) k σ)) ++
      [Gate.mk op [safeOut (m + C.size) D.size C.output,
        rho (m + C.size) k σ D.output]])).foldl stepW (List.ofFn x)).getD
        (m + C.size + D.size) false
    = op.eval [(C.gates.foldl stepW (List.ofFn x)).getD C.output false,
        (D.gates.foldl stepW (List.ofFn fun j : Fin k =>
          (C.gates.foldl stepW (List.ofFn x)).getD (σ j).val false)).getD D.output false]
  rw [List.foldl_append, List.foldl_append, h2, h1, List.foldl_cons, List.foldl_nil,
    final_op op _ _ _ _ (by rw [List.length_append, hW, hl']),
    safeOut_spec _ _ _ _ _ hW hl', rho_spec (m + C.size) k σ _ hW]

lemma comp_or_eval (m k : ℕ) (C D : Circuit) (σ : Fin k → Fin (m + C.size)) (x : Fin m → Bool) :
    (comp GateOp.or m k C D σ).eval (List.ofFn x)
      = (C.eval (List.ofFn x) ||
          D.eval (List.ofFn fun j : Fin k => (C.wires (List.ofFn x)).getD (σ j).val false)) := by
  rw [comp_eval, or_eval2]

lemma comp_and_eval (m k : ℕ) (C D : Circuit) (σ : Fin k → Fin (m + C.size)) (x : Fin m → Bool) :
    (comp GateOp.and m k C D σ).eval (List.ofFn x)
      = (C.eval (List.ofFn x) &&
          D.eval (List.ofFn fun j : Fin k => (C.wires (List.ofFn x)).getD (σ j).val false)) := by
  rw [comp_eval, and_eval2]

lemma comp_size (op : GateOp) (m k : ℕ) (C D : Circuit) (σ : Fin k → Fin (m + C.size)) :
    (comp op m k C D σ).size = C.size + D.size + 1 := by
  show (C.gates ++ (D.gates.map (reGate (rho (m + C.size) k σ)) ++ [_])).length = _
  rw [List.length_append, List.length_append, List.length_map]
  rfl

lemma comp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (m k : ℕ)
    (C D : Circuit) (σ : Fin k → Fin (m + C.size))
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (hD : PEqualNP.MetaComplexity.Monotone2 D) :
    PEqualNP.MetaComplexity.Monotone2 (comp op m k C D σ) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hC g hg
  · rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      have := hD g' hg'
      exact ⟨this.1, by rw [reGate_len]; exact this.2⟩
    · rw [List.mem_singleton] at hg
      subst hg
      rcases hop with rfl | rfl <;> simp

lemma exists_comp_or (m k : ℕ) (C D : Circuit) (σ : Fin k → Fin (m + C.size))
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (hD : PEqualNP.MetaComplexity.Monotone2 D) :
    ∃ E : Circuit, PEqualNP.MetaComplexity.Monotone2 E ∧ E.size ≤ C.size + D.size + 1 ∧
      ∀ x : Fin m → Bool, E.eval (List.ofFn x)
        = (C.eval (List.ofFn x) ||
            D.eval (List.ofFn fun j : Fin k => (C.wires (List.ofFn x)).getD (σ j).val false)) :=
  ⟨comp GateOp.or m k C D σ, comp_mono _ (Or.inr rfl) m k C D σ hC hD,
    le_of_eq (comp_size _ m k C D σ), comp_or_eval m k C D σ⟩

lemma exists_comp_and (m k : ℕ) (C D : Circuit) (σ : Fin k → Fin (m + C.size))
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (hD : PEqualNP.MetaComplexity.Monotone2 D) :
    ∃ E : Circuit, PEqualNP.MetaComplexity.Monotone2 E ∧ E.size ≤ C.size + D.size + 1 ∧
      ∀ x : Fin m → Bool, E.eval (List.ofFn x)
        = (C.eval (List.ofFn x) &&
            D.eval (List.ofFn fun j : Fin k => (C.wires (List.ofFn x)).getD (σ j).val false)) :=
  ⟨comp GateOp.and m k C D σ, comp_mono _ (Or.inl rfl) m k C D σ hC hD,
    le_of_eq (comp_size _ m k C D σ), comp_and_eval m k C D σ⟩

lemma exists_subst (m k : ℕ) (C D : Circuit) (σ : Fin k → Fin (m + C.size))
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (hD : PEqualNP.MetaComplexity.Monotone2 D) :
    ∃ E : Circuit, PEqualNP.MetaComplexity.Monotone2 E ∧ E.size ≤ C.size + D.size ∧
      ∀ x : Fin m → Bool, E.eval (List.ofFn x)
        = D.eval (List.ofFn fun j : Fin k => (C.wires (List.ofFn x)).getD (σ j).val false) :=
  ⟨substC m k C D σ, subst_mono m k C D σ hC hD, le_of_eq (subst_size m k C D σ),
    subst_eval m k C D σ⟩

lemma exists_or_map (n1 n2 : ℕ) (r : Fin n1 → Fin n2) (C4 C5 : Circuit)
    (h4 : PEqualNP.MetaComplexity.Monotone2 C4) (h5 : PEqualNP.MetaComplexity.Monotone2 C5) :
    ∃ E : Circuit, PEqualNP.MetaComplexity.Monotone2 E ∧ E.size ≤ C4.size + C5.size + 1 ∧
      ∀ x : Fin n2 → Bool, E.eval (List.ofFn x)
        = (C4.eval (List.ofFn fun j : Fin n1 => x (r j)) || C5.eval (List.ofFn x)) := by
  refine ⟨comp GateOp.or n2 n1 C5 C4 (fun j => Fin.castAdd C5.size (r j)),
    comp_mono _ (Or.inr rfl) _ _ C5 C4 _ h5 h4, ?_, ?_⟩
  · rw [comp_size]; omega
  · intro x
    have e : (fun j : Fin n1 =>
        (C5.wires (List.ofFn x)).getD (Fin.castAdd C5.size (r j)).val false)
        = fun j : Fin n1 => x (r j) := funext fun j => wires_input C5 x (r j)
    rw [comp_or_eval, e, Bool.or_comm]

lemma append_wires (C : Circuit) (gs : List Gate) (o : ℕ) (x : List Bool) :
    (Circuit.mk (C.gates ++ gs) o).wires x = gs.foldl stepW (C.wires x) := by
  show (C.gates ++ gs).foldl stepW x = gs.foldl stepW (C.gates.foldl stepW x)
  rw [List.foldl_append]

lemma append_old (C : Circuit) (gs : List Gate) (o : ℕ) (x : List Bool) (i : ℕ)
    (h : i < x.length + C.size) :
    ((Circuit.mk (C.gates ++ gs) o).wires x).getD i false = (C.wires x).getD i false := by
  rw [append_wires, fold_old _ _ _ (by rw [wires_len]; exact h)]

lemma append1_eval (n : ℕ) (C : Circuit) (g : Gate) (x : List Bool) (hx : x.length = n) :
    (Circuit.mk (C.gates ++ [g]) (n + C.size)).eval x
      = g.op.eval (g.inputs.map fun i => (C.wires x).getD i false) := by
  show ((Circuit.mk (C.gates ++ [g]) (n + C.size)).wires x).getD (n + C.size) false = _
  rw [append_wires]
  exact getD_snoc_len _ _ _ (by rw [wires_len, hx])

lemma append_or_eval (n : ℕ) (C : Circuit) (a b : ℕ) (x : List Bool) (hx : x.length = n) :
    (Circuit.mk (C.gates ++ [Gate.mk GateOp.or [a, b]]) (n + C.size)).eval x
      = ((C.wires x).getD a false || (C.wires x).getD b false) := by
  rw [append1_eval n C _ x hx]
  exact or_eval2 _ _

lemma append_and_eval (n : ℕ) (C : Circuit) (a b : ℕ) (x : List Bool) (hx : x.length = n) :
    (Circuit.mk (C.gates ++ [Gate.mk GateOp.and [a, b]]) (n + C.size)).eval x
      = ((C.wires x).getD a false && (C.wires x).getD b false) := by
  rw [append1_eval n C _ x hx]
  exact and_eval2 _ _

lemma append_mono (c : Bool) (a b : ℕ) (C : Circuit) (o : ℕ)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.MetaComplexity.Monotone2
      (Circuit.mk (C.gates ++ [Gate.mk (if c = true then GateOp.and else GateOp.or) [a, b]])
        o) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hC g hg
  · rw [List.mem_singleton] at hg
    subst hg
    exact bin_ok c a b

lemma step_shift (b : Bool) (w : List Bool) (g : Gate) :
    stepW (b :: w) (reGate Nat.succ g) = b :: stepW w g := by
  have hm : (g.inputs.map Nat.succ).map (fun i => (b :: w).getD i false)
      = g.inputs.map (fun i => w.getD i false) := by
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => by simp)
  show (b :: w) ++ [g.op.eval ((g.inputs.map Nat.succ).map fun i => (b :: w).getD i false)] = _
  rw [hm]
  rfl

lemma fold_shift (b : Bool) (gs : List Gate) :
    ∀ w : List Bool, (gs.map (reGate Nat.succ)).foldl stepW (b :: w) = b :: gs.foldl stepW w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, step_shift, ih]

lemma shift_eval (C : Circuit) (b : Bool) (x : List Bool) :
    (Circuit.mk (C.gates.map (reGate Nat.succ)) (C.output + 1)).eval (b :: x) = C.eval x := by
  show ((C.gates.map (reGate Nat.succ)).foldl stepW (b :: x)).getD (C.output + 1) false = _
  rw [fold_shift]
  rfl

def ext (n : ℕ) (C : Circuit) (k : ℕ) : Circuit :=
  Circuit.mk (C.gates.map (reGate Nat.succ) ++
    [Gate.mk GateOp.and [0, k + 1], Gate.mk GateOp.or [C.output + 1, n + C.gates.length + 1]])
    (n + C.gates.length + 2)

lemma ext_final (W : List Bool) (b : Bool) (k o L : ℕ) (hL : L = W.length) (ho : o < L) :
    (stepW (stepW (b :: W) (Gate.mk GateOp.and [0, k + 1]))
        (Gate.mk GateOp.or [o + 1, L + 1])).getD (L + 2) false
      = (W.getD o false || b && W.getD k false) := by
  subst hL
  have ha : stepW (b :: W) (Gate.mk GateOp.and [0, k + 1]) = (b :: W) ++ [b && W.getD k false] := by
    show (b :: W) ++ [GateOp.and.eval [(b :: W).getD 0 false, (b :: W).getD (k + 1) false]] = _
    simp [GateOp.eval]
  rw [ha]
  have h1 : ((b :: W) ++ [b && W.getD k false]).getD (o + 1) false = W.getD o false := by
    rw [List.getD_append _ _ _ _ (by simp; omega)]
    simp
  have h2 : ((b :: W) ++ [b && W.getD k false]).getD (W.length + 1) false
      = (b && W.getD k false) := getD_snoc_len _ _ _ (by simp)
  rw [final_op GateOp.or _ _ _ _ (by simp), h1, h2, or_eval2]

lemma ext_eval (n : ℕ) (C : Circuit) (k : ℕ) (b : Bool) (x : Fin n → Bool)
    (ho : C.output < n + C.size) :
    (ext n C k).eval (b :: List.ofFn x)
      = (C.eval (List.ofFn x) || b && (C.wires (List.ofFn x)).getD k false) := by
  have hlen : n + C.gates.length = (C.gates.foldl stepW (List.ofFn x)).length := by
    rw [fold_len]; simp
  show ((C.gates.map (reGate Nat.succ) ++ [Gate.mk GateOp.and [0, k + 1],
      Gate.mk GateOp.or [C.output + 1, n + C.gates.length + 1]]).foldl stepW
        (b :: List.ofFn x)).getD (n + C.gates.length + 2) false = _
  rw [List.foldl_append, fold_shift]
  exact ext_final (C.gates.foldl stepW (List.ofFn x)) b k C.output (n + C.gates.length) hlen ho

lemma ext_mono (n : ℕ) (C : Circuit) (k : ℕ) (h : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.MetaComplexity.Monotone2 (ext n C k) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    have := h g' hg'
    exact ⟨this.1, by rw [reGate_len]; exact this.2⟩
  · rcases List.mem_cons.mp hg with rfl | hg
    · simp
    · rw [List.mem_singleton] at hg
      subst hg
      simp

lemma exists_or_and_front (n : ℕ) (C : Circuit) (k : ℕ)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (ho : C.output < n + C.size) :
    ∃ E : Circuit, PEqualNP.MetaComplexity.Monotone2 E ∧ E.size ≤ C.size + 2 ∧
      ∀ (b : Bool) (x : Fin n → Bool), E.eval (b :: List.ofFn x)
        = (C.eval (List.ofFn x) || b && (C.wires (List.ofFn x)).getD k false) := by
  refine ⟨ext n C k, ext_mono n C k hC, ?_, fun b x => ext_eval n C k b x ho⟩
  show (C.gates.map (reGate Nat.succ) ++ [_, _]).length ≤ C.gates.length + 2
  rw [List.length_append, List.length_map]
  exact le_refl _

lemma snoc_rel {α : Type} (R : α → α → Prop) (z : α) (hz : R z z) {l l' : List α} {a b : α}
    (hl : l.length = l'.length) (h : ∀ i, R (l.getD i z) (l'.getD i z)) (hab : R a b) (i : ℕ) :
    R ((l ++ [a]).getD i z) ((l' ++ [b]).getD i z) := by
  by_cases hi : i < l'.length
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hi]
    exact h i
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
    by_cases h0 : i - l'.length = 0
    · rw [h0]
      simp only [List.getD_cons_zero]
      exact hab
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      exact hz

lemma all_mono (w w' : List Bool) (h : ∀ i, w.getD i false = true → w'.getD i false = true)
    (ins : List ℕ) :
    (ins.map fun i => w.getD i false).all id = true →
      (ins.map fun i => w'.getD i false).all id = true := by
  induction ins with
  | nil => intro _; rfl
  | cons a t ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true, id_eq]
    exact fun hh => ⟨h a hh.1, ih hh.2⟩

lemma any_mono (w w' : List Bool) (h : ∀ i, w.getD i false = true → w'.getD i false = true)
    (ins : List ℕ) :
    (ins.map fun i => w.getD i false).any id = true →
      (ins.map fun i => w'.getD i false).any id = true := by
  induction ins with
  | nil => intro hh; exact hh
  | cons a t ih =>
    simp only [List.map_cons, List.any_cons, Bool.or_eq_true, id_eq]
    exact fun hh => hh.elim (fun h1 => Or.inl (h a h1)) (fun h2 => Or.inr (ih h2))

def evg (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

lemma evg_mono (w w' : List Bool) (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : ∀ i, w.getD i false = true → w'.getD i false = true) :
    evg g w = true → evg g w' = true := by
  rcases hg with hg | hg
  · unfold evg
    rw [hg]
    exact all_mono w w' h g.inputs
  · unfold evg
    rw [hg]
    exact any_mono w w' h g.inputs

theorem fold_mono : ∀ (gs : List Gate) (w w' : List Bool),
    w.length = w'.length → (∀ i, w.getD i false = true → w'.getD i false = true) →
      (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
        ∀ i, (gs.foldl stepW w).getD i false = true → (gs.foldl stepW w').getD i false = true
  | [], _, _, _, h, _ => h
  | g :: gs, w, w', hl, h, hg => by
    have h1 := evg_mono w w' g (hg g (by simp)) h
    exact fold_mono gs (w ++ [evg g w]) (w' ++ [evg g w'])
      (by simp [hl]) (snoc_rel (fun a b : Bool => a = true → b = true) false (fun hh => hh) hl h h1)
      (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))

lemma mono2_ops (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) :
    ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  have h := (hC g hg).1
  simpa using h

lemma wires_mono (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    {n : ℕ} (x y : Fin n → Bool) (h : ∀ k, x k = true → y k = true) (i : ℕ) :
    (C.wires (List.ofFn x)).getD i false = true → (C.wires (List.ofFn y)).getD i false = true := by
  refine fold_mono C.gates (List.ofFn x) (List.ofFn y) (by simp) ?_ hC i
  intro k
  by_cases hk : k < n
  · rw [getD_ofFn x k hk, getD_ofFn y k hk]
    exact h _
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    intro hh
    exact (Bool.false_ne_true hh).elim

lemma eval_mono (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    {n : ℕ} (x y : Fin n → Bool) (h : ∀ k, x k = true → y k = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true :=
  wires_mono C (mono2_ops C hC) x y h C.output


lemma gW_lt (W u : List Bool) (i : ℕ) (h : i < W.length) :
    (W ++ u).getD i false = W.getD i false := by
  rw [List.getD_append _ _ _ _ h]

lemma gW_ge (W u : List Bool) (N : ℕ) (hW : W.length = N) (j : ℕ) :
    (W ++ u).getD (N + j) false = u.getD j false := by
  subst hW
  rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

lemma st0 (W u : List Bool) : ([] : List Gate).foldl stepW (W ++ u) = W ++ u := rfl

lemma st2 (W u : List Bool) (op : GateOp) (a b : ℕ) (va vb : Bool)
    (ha : (W ++ u).getD a false = va) (hb : (W ++ u).getD b false = vb) (gs : List Gate)
    (R : List Bool) (h : gs.foldl stepW (W ++ (u ++ [op.eval [va, vb]])) = R) :
    (Gate.mk op [a, b] :: gs).foldl stepW (W ++ u) = R := by
  subst ha hb
  rw [List.foldl_cons]
  show gs.foldl stepW ((W ++ u) ++ [op.eval [(W ++ u).getD a false, (W ++ u).getD b false]]) = R
  rw [List.append_assoc]
  exact h

lemma nth_2_1 (W : List Bool) (N : ℕ) (hW : W.length = N) (e0 e1 : Bool) :
    (W ++ ([] ++ [e0] ++ [e1])).getD (N + 1) false = e1 := by
  rw [gW_ge W _ N hW 1]
  rfl

lemma nth_3_2 (W : List Bool) (N : ℕ) (hW : W.length = N) (e0 e1 e2 : Bool) :
    (W ++ ([] ++ [e0] ++ [e1] ++ [e2])).getD (N + 2) false = e2 := by
  rw [gW_ge W _ N hW 2]
  rfl

lemma nth_4_3 (W : List Bool) (N : ℕ) (hW : W.length = N) (e0 e1 e2 e3 : Bool) :
    (W ++ ([] ++ [e0] ++ [e1] ++ [e2] ++ [e3])).getD (N + 3) false = e3 := by
  rw [gW_ge W _ N hW 3]
  rfl

lemma nth_6_5 (W : List Bool) (N : ℕ) (hW : W.length = N) (e0 e1 e2 e3 e4 e5 : Bool) :
    (W ++ ([] ++ [e0] ++ [e1] ++ [e2] ++ [e3] ++ [e4] ++ [e5])).getD (N + 5) false = e5 := by
  rw [gW_ge W _ N hW 5]
  rfl

lemma nth_7_6 (W : List Bool) (N : ℕ) (hW : W.length = N) (e0 e1 e2 e3 e4 e5 e6 : Bool) :
    (W ++ ([] ++ [e0] ++ [e1] ++ [e2] ++ [e3] ++ [e4] ++ [e5] ++ [e6])).getD (N + 6) false = e6 := by
  rw [gW_ge W _ N hW 6]
  rfl

lemma nth_8_7 (W : List Bool) (N : ℕ) (hW : W.length = N) (e0 e1 e2 e3 e4 e5 e6 e7 : Bool) :
    (W ++ ([] ++ [e0] ++ [e1] ++ [e2] ++ [e3] ++ [e4] ++ [e5] ++ [e6] ++ [e7])).getD (N + 7) false = e7 := by
  rw [gW_ge W _ N hW 7]
  rfl

lemma nth_10_9 (W : List Bool) (N : ℕ) (hW : W.length = N) (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 : Bool) :
    (W ++ ([] ++ [e0] ++ [e1] ++ [e2] ++ [e3] ++ [e4] ++ [e5] ++ [e6] ++ [e7] ++ [e8] ++ [e9])).getD (N + 9) false = e9 := by
  rw [gW_ge W _ N hW 9]
  rfl

lemma nth_11_10 (W : List Bool) (N : ℕ) (hW : W.length = N) (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 : Bool) :
    (W ++ ([] ++ [e0] ++ [e1] ++ [e2] ++ [e3] ++ [e4] ++ [e5] ++ [e6] ++ [e7] ++ [e8] ++ [e9] ++ [e10])).getD (N + 10) false = e10 := by
  rw [gW_ge W _ N hW 10]
  rfl

lemma nth_12_11 (W : List Bool) (N : ℕ) (hW : W.length = N) (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : Bool) :
    (W ++ ([] ++ [e0] ++ [e1] ++ [e2] ++ [e3] ++ [e4] ++ [e5] ++ [e6] ++ [e7] ++ [e8] ++ [e9] ++ [e10] ++ [e11])).getD (N + 11) false = e11 := by
  rw [gW_ge W _ N hW 11]
  rfl

lemma nth_13_4 (W : List Bool) (N : ℕ) (hW : W.length = N) (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 : Bool) :
    (W ++ ([] ++ [e0] ++ [e1] ++ [e2] ++ [e3] ++ [e4] ++ [e5] ++ [e6] ++ [e7] ++ [e8] ++ [e9] ++ [e10] ++ [e11] ++ [e12])).getD (N + 4) false = e4 := by
  rw [gW_ge W _ N hW 4]
  rfl

lemma nth_14_13 (W : List Bool) (N : ℕ) (hW : W.length = N) (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 : Bool) :
    (W ++ ([] ++ [e0] ++ [e1] ++ [e2] ++ [e3] ++ [e4] ++ [e5] ++ [e6] ++ [e7] ++ [e8] ++ [e9] ++ [e10] ++ [e11] ++ [e12] ++ [e13])).getD (N + 13) false = e13 := by
  rw [gW_ge W _ N hW 13]
  rfl

lemma nth_14_8 (W : List Bool) (N : ℕ) (hW : W.length = N) (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 : Bool) :
    (W ++ ([] ++ [e0] ++ [e1] ++ [e2] ++ [e3] ++ [e4] ++ [e5] ++ [e6] ++ [e7] ++ [e8] ++ [e9] ++ [e10] ++ [e11] ++ [e12] ++ [e13])).getD (N + 8) false = e8 := by
  rw [gW_ge W _ N hW 8]
  rfl

lemma nth_15_14 (W : List Bool) (N : ℕ) (hW : W.length = N) (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 : Bool) :
    (W ++ ([] ++ [e0] ++ [e1] ++ [e2] ++ [e3] ++ [e4] ++ [e5] ++ [e6] ++ [e7] ++ [e8] ++ [e9] ++ [e10] ++ [e11] ++ [e12] ++ [e13] ++ [e14])).getD (N + 14) false = e14 := by
  rw [gW_ge W _ N hW 14]
  rfl

lemma nth_15_12 (W : List Bool) (N : ℕ) (hW : W.length = N) (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 : Bool) :
    (W ++ ([] ++ [e0] ++ [e1] ++ [e2] ++ [e3] ++ [e4] ++ [e5] ++ [e6] ++ [e7] ++ [e8] ++ [e9] ++ [e10] ++ [e11] ++ [e12] ++ [e13] ++ [e14])).getD (N + 12) false = e12 := by
  rw [gW_ge W _ N hW 12]
  rfl

lemma uu0 (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 : Bool) : (([] ++ [e0] ++ [e1] ++ [e2] ++ [e3] ++ [e4] ++ [e5] ++ [e6] ++ [e7] ++ [e8] ++ [e9] ++ [e10] ++ [e11] ++ [e12] ++ [e13] ++ [e14] ++ [e15]) : List Bool).getD 0 false = e0 := rfl

lemma uu15 (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 : Bool) : (([] ++ [e0] ++ [e1] ++ [e2] ++ [e3] ++ [e4] ++ [e5] ++ [e6] ++ [e7] ++ [e8] ++ [e9] ++ [e10] ++ [e11] ++ [e12] ++ [e13] ++ [e14] ++ [e15]) : List Bool).getD 15 false = e15 := rfl

def gs16 (N o k : ℕ) : List Gate :=
  [Gate.mk GateOp.or [k, 12], Gate.mk GateOp.or [12, 14], Gate.mk GateOp.or [N + 1, 20], Gate.mk GateOp.or [N + 2, 24], Gate.mk GateOp.and [0, N + 3], Gate.mk GateOp.or [12, 18], Gate.mk GateOp.or [N + 5, 22], Gate.mk GateOp.or [N + 6, 23], Gate.mk GateOp.and [2, N + 7], Gate.mk GateOp.or [12, 16], Gate.mk GateOp.or [N + 9, 17], Gate.mk GateOp.or [N + 10, 19], Gate.mk GateOp.and [8, N + 11], Gate.mk GateOp.or [o, N + 4], Gate.mk GateOp.or [N + 13, N + 8], Gate.mk GateOp.or [N + 14, N + 12]]

lemma gs16_ok (N o k : ℕ) : ∀ g ∈ gs16 N o k,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [gs16, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma fold16 (W : List Bool) (N o k : ℕ) (hW : W.length = N) (ho : o < N) (hk : k < N)
    (h25 : 25 ≤ N) :
    ∃ U : List Bool, (gs16 N o k).foldl stepW W = W ++ U ∧ U.getD 0 false = GateOp.or.eval [W.getD k false, W.getD 12 false] ∧
      U.getD 15 false = GateOp.or.eval [GateOp.or.eval [GateOp.or.eval [W.getD o false, GateOp.and.eval [W.getD 0 false, GateOp.or.eval [GateOp.or.eval [GateOp.or.eval [W.getD 12 false, W.getD 14 false], W.getD 20 false], W.getD 24 false]]], GateOp.and.eval [W.getD 2 false, GateOp.or.eval [GateOp.or.eval [GateOp.or.eval [W.getD 12 false, W.getD 18 false], W.getD 22 false], W.getD 23 false]]], GateOp.and.eval [W.getD 8 false, GateOp.or.eval [GateOp.or.eval [GateOp.or.eval [W.getD 12 false, W.getD 16 false], W.getD 17 false], W.getD 19 false]]] := by
  have h : ∃ U : List Bool, (gs16 N o k).foldl stepW (W ++ []) = W ++ U ∧
      U.getD 0 false = GateOp.or.eval [W.getD k false, W.getD 12 false] ∧
      U.getD 15 false = GateOp.or.eval [GateOp.or.eval [GateOp.or.eval [W.getD o false, GateOp.and.eval [W.getD 0 false, GateOp.or.eval [GateOp.or.eval [GateOp.or.eval [W.getD 12 false, W.getD 14 false], W.getD 20 false], W.getD 24 false]]], GateOp.and.eval [W.getD 2 false, GateOp.or.eval [GateOp.or.eval [GateOp.or.eval [W.getD 12 false, W.getD 18 false], W.getD 22 false], W.getD 23 false]]], GateOp.and.eval [W.getD 8 false, GateOp.or.eval [GateOp.or.eval [GateOp.or.eval [W.getD 12 false, W.getD 16 false], W.getD 17 false], W.getD 19 false]]] := by
    unfold gs16
    refine ⟨?U, ?h1, ?h2, ?h3⟩
    case h1 =>
      refine st2 W _ GateOp.or (k) (12) (W.getD k false) (W.getD 12 false) (gW_lt W _ k (by omega)) (gW_lt W _ 12 (by omega)) _ _ ?_
      refine st2 W _ GateOp.or (12) (14) (W.getD 12 false) (W.getD 14 false) (gW_lt W _ 12 (by omega)) (gW_lt W _ 14 (by omega)) _ _ ?_
      refine st2 W _ GateOp.or (N + 1) (20) (GateOp.or.eval [W.getD 12 false, W.getD 14 false]) (W.getD 20 false) (nth_2_1 W N hW _ _) (gW_lt W _ 20 (by omega)) _ _ ?_
      refine st2 W _ GateOp.or (N + 2) (24) (GateOp.or.eval [GateOp.or.eval [W.getD 12 false, W.getD 14 false], W.getD 20 false]) (W.getD 24 false) (nth_3_2 W N hW _ _ _) (gW_lt W _ 24 (by omega)) _ _ ?_
      refine st2 W _ GateOp.and (0) (N + 3) (W.getD 0 false) (GateOp.or.eval [GateOp.or.eval [GateOp.or.eval [W.getD 12 false, W.getD 14 false], W.getD 20 false], W.getD 24 false]) (gW_lt W _ 0 (by omega)) (nth_4_3 W N hW _ _ _ _) _ _ ?_
      refine st2 W _ GateOp.or (12) (18) (W.getD 12 false) (W.getD 18 false) (gW_lt W _ 12 (by omega)) (gW_lt W _ 18 (by omega)) _ _ ?_
      refine st2 W _ GateOp.or (N + 5) (22) (GateOp.or.eval [W.getD 12 false, W.getD 18 false]) (W.getD 22 false) (nth_6_5 W N hW _ _ _ _ _ _) (gW_lt W _ 22 (by omega)) _ _ ?_
      refine st2 W _ GateOp.or (N + 6) (23) (GateOp.or.eval [GateOp.or.eval [W.getD 12 false, W.getD 18 false], W.getD 22 false]) (W.getD 23 false) (nth_7_6 W N hW _ _ _ _ _ _ _) (gW_lt W _ 23 (by omega)) _ _ ?_
      refine st2 W _ GateOp.and (2) (N + 7) (W.getD 2 false) (GateOp.or.eval [GateOp.or.eval [GateOp.or.eval [W.getD 12 false, W.getD 18 false], W.getD 22 false], W.getD 23 false]) (gW_lt W _ 2 (by omega)) (nth_8_7 W N hW _ _ _ _ _ _ _ _) _ _ ?_
      refine st2 W _ GateOp.or (12) (16) (W.getD 12 false) (W.getD 16 false) (gW_lt W _ 12 (by omega)) (gW_lt W _ 16 (by omega)) _ _ ?_
      refine st2 W _ GateOp.or (N + 9) (17) (GateOp.or.eval [W.getD 12 false, W.getD 16 false]) (W.getD 17 false) (nth_10_9 W N hW _ _ _ _ _ _ _ _ _ _) (gW_lt W _ 17 (by omega)) _ _ ?_
      refine st2 W _ GateOp.or (N + 10) (19) (GateOp.or.eval [GateOp.or.eval [W.getD 12 false, W.getD 16 false], W.getD 17 false]) (W.getD 19 false) (nth_11_10 W N hW _ _ _ _ _ _ _ _ _ _ _) (gW_lt W _ 19 (by omega)) _ _ ?_
      refine st2 W _ GateOp.and (8) (N + 11) (W.getD 8 false) (GateOp.or.eval [GateOp.or.eval [GateOp.or.eval [W.getD 12 false, W.getD 16 false], W.getD 17 false], W.getD 19 false]) (gW_lt W _ 8 (by omega)) (nth_12_11 W N hW _ _ _ _ _ _ _ _ _ _ _ _) _ _ ?_
      refine st2 W _ GateOp.or (o) (N + 4) (W.getD o false) (GateOp.and.eval [W.getD 0 false, GateOp.or.eval [GateOp.or.eval [GateOp.or.eval [W.getD 12 false, W.getD 14 false], W.getD 20 false], W.getD 24 false]]) (gW_lt W _ o (by omega)) (nth_13_4 W N hW _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ ?_
      refine st2 W _ GateOp.or (N + 13) (N + 8) (GateOp.or.eval [W.getD o false, GateOp.and.eval [W.getD 0 false, GateOp.or.eval [GateOp.or.eval [GateOp.or.eval [W.getD 12 false, W.getD 14 false], W.getD 20 false], W.getD 24 false]]]) (GateOp.and.eval [W.getD 2 false, GateOp.or.eval [GateOp.or.eval [GateOp.or.eval [W.getD 12 false, W.getD 18 false], W.getD 22 false], W.getD 23 false]]) (nth_14_13 W N hW _ _ _ _ _ _ _ _ _ _ _ _ _ _) (nth_14_8 W N hW _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ ?_
      refine st2 W _ GateOp.or (N + 14) (N + 12) (GateOp.or.eval [GateOp.or.eval [W.getD o false, GateOp.and.eval [W.getD 0 false, GateOp.or.eval [GateOp.or.eval [GateOp.or.eval [W.getD 12 false, W.getD 14 false], W.getD 20 false], W.getD 24 false]]], GateOp.and.eval [W.getD 2 false, GateOp.or.eval [GateOp.or.eval [GateOp.or.eval [W.getD 12 false, W.getD 18 false], W.getD 22 false], W.getD 23 false]]]) (GateOp.and.eval [W.getD 8 false, GateOp.or.eval [GateOp.or.eval [GateOp.or.eval [W.getD 12 false, W.getD 16 false], W.getD 17 false], W.getD 19 false]]) (nth_15_14 W N hW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (nth_15_12 W N hW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ ?_
      exact st0 W _
    case h2 => exact uu0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    case h3 => exact uu15 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [List.append_nil] at h
  exact h

lemma pairs : ∀ a b : Fin 25, (a : ℕ) < 12 → 12 ≤ (b : ℕ) →
    ((a : ℕ) + (b : ℕ) + 2) % 13 ∈ [0, 1, 3, 9] → (a : ℕ) ∈ [0, 2, 8] →
    (a = 0 ∧ b = 12) ∨ (a = 0 ∧ b = 14) ∨ (a = 0 ∧ b = 20) ∨ (a = 0 ∧ b = 24) ∨ (a = 2 ∧ b = 12) ∨ (a = 2 ∧ b = 18) ∨ (a = 2 ∧ b = 22) ∨ (a = 2 ∧ b = 23) ∨ (a = 8 ∧ b = 12) ∨ (a = 8 ∧ b = 16) ∨ (a = 8 ∧ b = 17) ∨ (a = 8 ∧ b = 19) := by
  decide +kernel

lemma key (x8 : Fin 25 → Bool) : (∃ (x9 : Fin (25 : ℕ)) (x10 : Fin (25 : ℕ)), ↑x9 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x10 ∧ (↑x9 + ↑x10 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x9 ∈ [(0 : ℕ), (2 : ℕ), (8 : ℕ)] ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) ↔
    (((x8 0 && (((x8 12 || x8 14) || x8 20) || x8 24)) || (x8 2 && (((x8 12 || x8 18) || x8 22) || x8 23))) || (x8 8 && (((x8 12 || x8 16) || x8 17) || x8 19))) = true := by
  constructor
  · rintro ⟨a, b, h1, h2, h3, h4, h5, h6⟩
    rcases pairs a b h1 h2 h3 h4 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [h5, h6]
  · intro h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with (⟨h0, ((h | h) | h) | h⟩ | ⟨h0, ((h | h) | h) | h⟩) | ⟨h0, ((h | h) | h) | h⟩
    · exact ⟨0, 12, by decide, by decide, by decide, by decide, h0, h⟩
    · exact ⟨0, 14, by decide, by decide, by decide, by decide, h0, h⟩
    · exact ⟨0, 20, by decide, by decide, by decide, by decide, h0, h⟩
    · exact ⟨0, 24, by decide, by decide, by decide, by decide, h0, h⟩
    · exact ⟨2, 12, by decide, by decide, by decide, by decide, h0, h⟩
    · exact ⟨2, 18, by decide, by decide, by decide, by decide, h0, h⟩
    · exact ⟨2, 22, by decide, by decide, by decide, by decide, h0, h⟩
    · exact ⟨2, 23, by decide, by decide, by decide, by decide, h0, h⟩
    · exact ⟨8, 12, by decide, by decide, by decide, by decide, h0, h⟩
    · exact ⟨8, 16, by decide, by decide, by decide, by decide, h0, h⟩
    · exact ⟨8, 17, by decide, by decide, by decide, by decide, h0, h⟩
    · exact ⟨8, 19, by decide, by decide, by decide, by decide, h0, h⟩

lemma big : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → x1.output < (25 : ℕ) + x1.size → x2 < (25 : ℕ) + x1.size → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size ≤ x1.size + (16 : ℕ) ∧ x6.output < (25 : ℕ) + x6.size ∧ x7 < (25 : ℕ) + x6.size ∧ ∀ (x8 : Fin (25 : ℕ) → Bool), (x6.eval (List.ofFn x8) = Bool.true ↔ x1.eval (List.ofFn x8) = Bool.true ∨ ∃ (x9 : Fin (25 : ℕ)) (x10 : Fin (25 : ℕ)), ↑x9 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x10 ∧ (↑x9 + ↑x10 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x9 ∈ [(0 : ℕ), (2 : ℕ), (8 : ℕ)] ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) ∧ (x6.wires (List.ofFn x8)).getD x7 Bool.false = ((x1.wires (List.ofFn x8)).getD x2 Bool.false || x8 (12 : Fin (25 : ℕ))) := by
  intro C k hC ho hk
  have hsz : (Circuit.mk (C.gates ++ gs16 (25 + C.size) C.output k) (25 + C.size + 15)).size
      = C.size + 16 := by
    show (C.gates ++ gs16 (25 + C.size) C.output k).length = C.gates.length + 16
    rw [List.length_append]
    rfl
  refine ⟨Circuit.mk (C.gates ++ gs16 (25 + C.size) C.output k) (25 + C.size + 15), 25 + C.size,
    ?_, ?_, ?_, ?_, fun x => ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hC g h
    · exact gs16_ok _ _ _ g h
  · rw [hsz]
  · rw [hsz]
    show 25 + C.size + 15 < 25 + (C.size + 16)
    omega
  · rw [hsz]
    omega
  · have hW : (C.wires (List.ofFn x)).length = 25 + C.size := by
      rw [wires_len, List.length_ofFn]
    obtain ⟨U, hU, h0, h15⟩ := fold16 (C.wires (List.ofFn x)) (25 + C.size) C.output k hW ho hk
      (by omega)
    have hwires : (Circuit.mk (C.gates ++ gs16 (25 + C.size) C.output k)
        (25 + C.size + 15)).wires (List.ofFn x) = C.wires (List.ofFn x) ++ U := by
      rw [append_wires]
      exact hU
    have i0 : (C.wires (List.ofFn x)).getD 0 false = x 0 := wires_input C x 0
    have i2 : (C.wires (List.ofFn x)).getD 2 false = x 2 := wires_input C x 2
    have i8 : (C.wires (List.ofFn x)).getD 8 false = x 8 := wires_input C x 8
    have i12 : (C.wires (List.ofFn x)).getD 12 false = x 12 := wires_input C x 12
    have i14 : (C.wires (List.ofFn x)).getD 14 false = x 14 := wires_input C x 14
    have i16 : (C.wires (List.ofFn x)).getD 16 false = x 16 := wires_input C x 16
    have i17 : (C.wires (List.ofFn x)).getD 17 false = x 17 := wires_input C x 17
    have i18 : (C.wires (List.ofFn x)).getD 18 false = x 18 := wires_input C x 18
    have i19 : (C.wires (List.ofFn x)).getD 19 false = x 19 := wires_input C x 19
    have i20 : (C.wires (List.ofFn x)).getD 20 false = x 20 := wires_input C x 20
    have i22 : (C.wires (List.ofFn x)).getD 22 false = x 22 := wires_input C x 22
    have i23 : (C.wires (List.ofFn x)).getD 23 false = x 23 := wires_input C x 23
    have i24 : (C.wires (List.ofFn x)).getD 24 false = x 24 := wires_input C x 24
    constructor
    · have heval : (Circuit.mk (C.gates ++ gs16 (25 + C.size) C.output k)
          (25 + C.size + 15)).eval (List.ofFn x)
          = (((C.eval (List.ofFn x) || (x 0 && (((x 12 || x 14) || x 20) || x 24))) || (x 2 && (((x 12 || x 18) || x 22) || x 23))) || (x 8 && (((x 12 || x 16) || x 17) || x 19))) := by
        show ((Circuit.mk (C.gates ++ gs16 (25 + C.size) C.output k)
          (25 + C.size + 15)).wires (List.ofFn x)).getD (25 + C.size + 15) false = _
        rw [hwires, gW_ge _ _ _ hW 15, h15]
        simp only [or_eval2, and_eval2, i0, i2, i8, i12, i14, i16, i17, i18, i19, i20, i22, i23, i24]
        rfl
      rw [heval]
      refine Iff.trans ?_ (or_congr Iff.rfl (key x).symm)
      simp only [Bool.or_eq_true, or_assoc]
    · have h7 : (C.wires (List.ofFn x) ++ U).getD (25 + C.size) false = U.getD 0 false :=
        gW_ge (C.wires (List.ofFn x)) U (25 + C.size) hW 0
      rw [hwires, h7, h0, or_eval2, i12]

end PEqualNP.Outside.L_meta_2573

theorem PEqualNP.Outside.L_meta_2573 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → x1.output < (25 : ℕ) + x1.size → x2 < (25 : ℕ) + x1.size → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size ≤ x1.size + (16 : ℕ) ∧ x6.output < (25 : ℕ) + x6.size ∧ x7 < (25 : ℕ) + x6.size ∧ ∀ (x8 : Fin (25 : ℕ) → Bool), (x6.eval (List.ofFn x8) = Bool.true ↔ x1.eval (List.ofFn x8) = Bool.true ∨ ∃ (x9 : Fin (25 : ℕ)) (x10 : Fin (25 : ℕ)), ↑x9 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x10 ∧ (↑x9 + ↑x10 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x9 ∈ [(0 : ℕ), (2 : ℕ), (8 : ℕ)] ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) ∧ (x6.wires (List.ofFn x8)).getD x7 Bool.false = ((x1.wires (List.ofFn x8)).getD x2 Bool.false || x8 (12 : Fin (25 : ℕ))) := by
  exact PEqualNP.Outside.L_meta_2573.big
