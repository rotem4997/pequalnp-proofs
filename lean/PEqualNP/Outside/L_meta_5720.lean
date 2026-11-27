import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5720

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (W : List Bool) (g : Gate) : List Bool :=
  W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]

def run (gs : List Gate) (W : List Bool) : List Bool := gs.foldl step W

theorem run_append (gs : List Gate) (g : Gate) (W : List Bool) :
    run (gs ++ [g]) W = step (run gs W) g := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (W : List Bool) :
    (run gs W).length = W.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_append]; simp [step, ih]; omega

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

def val (W : List Bool) (o : Option ℕ) : Bool :=
  match o with
  | none => false
  | some j => W.getD j false

def drop (op : GateOp) (o : Option ℕ) : Option ℕ :=
  match op with
  | GateOp.and => none
  | _ => o

def tstep (n : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) : List Gate × List (Option ℕ) :=
  match s.2.getD (g.inputs.getD 0 0) none, s.2.getD (g.inputs.getD 1 0) none with
  | some a, some b => (s.1 ++ [⟨g.op, [a, b]⟩], s.2 ++ [some (n + s.1.length)])
  | some a, none => (s.1, s.2 ++ [drop g.op (some a)])
  | none, ob => (s.1, s.2 ++ [drop g.op ob])

def init (n : ℕ) (v : Fin n) : List Gate × List (Option ℕ) :=
  ([], List.ofFn (fun i : Fin n => if i = v then none else some i.val))

def trans (n : ℕ) (v : Fin n) (gs : List Gate) : List Gate × List (Option ℕ) :=
  gs.foldl (tstep n) (init n v)

theorem trans_append (n : ℕ) (v : Fin n) (gs : List Gate) (g : Gate) :
    trans n v (gs ++ [g]) = tstep n (trans n v gs) g := by
  simp [trans, List.foldl_append]

def Inv (n : ℕ) (v : Fin n) (x : Fin n → Bool) (gs : List Gate)
    (N : List Gate) (φ : List (Option ℕ)) : Prop :=
  φ.length = n + gs.length ∧
  (∀ w, val (run N (List.ofFn x)) (φ.getD w none)
      = (run gs (List.ofFn (Function.update x v false))).getD w false) ∧
  (∀ w j, φ.getD w none = some j → j < n + N.length) ∧
  (∀ g ∈ N, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ k, ∀ i ∈ (N.getD k ⟨GateOp.or, []⟩).inputs, i < n + k) ∧
  N.length ≤ gs.length ∧
  (N.length = gs.length → N = gs ∧ ∀ w < φ.length, w ≠ v.val → φ.getD w none = some w) ∧
  φ.getD v.val none = none

theorem snoc_val (W W' W'' : List Bool) (φ : List (Option ℕ)) (o : Option ℕ) (b : Bool)
    (hl : φ.length = W.length)
    (h : ∀ w, val W' (φ.getD w none) = W.getD w false)
    (hs : ∀ w, val W'' (φ.getD w none) = val W' (φ.getD w none))
    (ho : val W'' o = b) :
    ∀ w, val W'' ((φ ++ [o]).getD w none) = (W ++ [b]).getD w false := by
  intro w
  rcases lt_trichotomy w φ.length with hw | hw | hw
  · rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ (by omega), hs, h]
  · subst hw
    rw [List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ (by omega)]
    simp [hl, ho]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem inv_init (n : ℕ) (v : Fin n) (x : Fin n → Bool) :
    Inv n v x [] (init n v).1 (init n v).2 := by
  refine ⟨by simp [init], ?_, ?_, by simp [init], ?_, by simp [init], ?_, ?_⟩
  · intro w
    by_cases hw : w < n
    · have : (init n v).2.getD w none = if (⟨w, hw⟩ : Fin n) = v then none else some w := by
        unfold init
        rw [List.getD_eq_getElem _ _ (by simpa using hw)]
        simp
      rw [this]
      simp only [run, List.foldl_nil, init]
      rw [getD_ofFn _ _ hw]
      by_cases hv : (⟨w, hw⟩ : Fin n) = v
      · simp [hv, val]
      · simp [hv, val, hw]
    · rw [List.getD_eq_default _ _ (by simp [init]; omega),
        List.getD_eq_default _ _ (by simp [run]; omega)]
      rfl
  · intro w j h
    by_cases hw : w < n
    · unfold init at h
      rw [List.getD_eq_getElem _ _ (by simpa using hw)] at h
      simp at h
      simp [init]; omega
    · rw [List.getD_eq_default _ _ (by simp [init]; omega)] at h
      cases h
  · intro k i hi
    simp [init] at hi
  · intro _
    refine ⟨by simp [init], ?_⟩
    intro w hw hv
    have hw : w < n := by simpa [init] using hw
    unfold init
    rw [List.getD_eq_getElem _ _ (by simpa using hw)]
    have : (⟨w, hw⟩ : Fin n) ≠ v := fun h => hv (by rw [← h])
    simp [this]
  · unfold init
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp

def comb (op : GateOp) (p q : Bool) : Bool :=
  match op with
  | GateOp.and => p && q
  | _ => p || q

theorem eval_two (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (p q : Bool) :
    op.eval [p, q] = comb op p q := by
  rcases hop with h | h <;> subst h <;> simp [GateOp.eval, comb]

theorem inv_step (n : ℕ) (v : Fin n) (x : Fin n → Bool) (gs N : List Gate)
    (φ : List (Option ℕ)) (op : GateOp) (a b : ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or) (ha : a < n + gs.length) (hb : b < n + gs.length)
    (h : Inv n v x gs N φ) :
    Inv n v x (gs ++ [⟨op, [a, b]⟩]) (tstep n (N, φ) ⟨op, [a, b]⟩).1
      (tstep n (N, φ) ⟨op, [a, b]⟩).2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hWl : (run gs (List.ofFn (Function.update x v false))).length = n + gs.length := by
    rw [run_length]; simp
  have hW'l : (run N (List.ofFn x)).length = n + N.length := by
    rw [run_length]; simp
  have hv : v.val < φ.length := by have := v.isLt; omega
  have h8' : ∀ o, (φ ++ [o]).getD v.val none = none := by
    intro o; rw [List.getD_append _ _ _ _ hv]; exact h8
  have hstep : run (gs ++ [⟨op, [a, b]⟩]) (List.ofFn (Function.update x v false))
      = run gs (List.ofFn (Function.update x v false)) ++
        [comb op ((run gs (List.ofFn (Function.update x v false))).getD a false) ((run gs (List.ofFn (Function.update x v false))).getD b false)] := by
    rw [run_append, step]
    simp only [List.map_cons, List.map_nil]
    rw [eval_two op hop]
  have h3' : ∀ m, n + N.length ≤ m → ∀ o, (∀ j, o = some j → j < m) →
      ∀ w j, (φ ++ [o]).getD w none = some j → j < m := by
    intro m hm o ho w j hj
    rcases lt_trichotomy w φ.length with hw | hw | hw
    · rw [List.getD_append _ _ _ _ hw] at hj; have := h3 w j hj; omega
    · subst hw
      rw [List.getD_append_right _ _ _ _ le_rfl] at hj
      simp at hj
      exact ho j hj
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
      cases hj
  have hdrop : ∀ o, (∀ j, o = some j → j < n + N.length) →
      val (run N (List.ofFn x)) o = comb op ((run gs (List.ofFn (Function.update x v false))).getD a false) ((run gs (List.ofFn (Function.update x v false))).getD b false) →
      Inv n v x (gs ++ [⟨op, [a, b]⟩]) N (φ ++ [o]) := by
    intro o ho hval
    refine ⟨by simp [h1]; omega, ?_, h3' _ le_rfl o ho, h4, h5, by simp; omega, ?_, h8' o⟩
    · rw [hstep]
      exact snoc_val _ _ _ φ o _ (by rw [hWl, h1]) h2 (fun _ => rfl) hval
    · intro hc; simp at hc; omega
  have ea := h2 a
  have eb := h2 b
  rcases hφa : φ.getD a none with _ | a'
  · rw [hφa] at ea
    have ht : tstep n (N, φ) ⟨op, [a, b]⟩ = (N, φ ++ [drop op (φ.getD b none)]) := by
      unfold tstep; dsimp only []; rw [show ([a, b] : List ℕ).getD 0 0 = a from rfl, show ([a, b] : List ℕ).getD 1 0 = b from rfl]; rw [hφa]
    rw [ht]
    apply hdrop
    · intro j hj
      rcases hop with h | h <;> subst h <;> simp [drop] at hj
      exact h3 b j hj
    · rw [← ea, ← eb]
      rcases hop with h | h <;> subst h <;> simp [drop, val, comb]
  · rw [hφa] at ea
    rcases hφb : φ.getD b none with _ | b'
    · rw [hφb] at eb
      have ht : tstep n (N, φ) ⟨op, [a, b]⟩ = (N, φ ++ [drop op (some a')]) := by
        unfold tstep; dsimp only []; rw [show ([a, b] : List ℕ).getD 0 0 = a from rfl, show ([a, b] : List ℕ).getD 1 0 = b from rfl]; rw [hφa, hφb]
      rw [ht]
      apply hdrop
      · intro j hj
        rcases hop with h | h <;> subst h <;> simp [drop] at hj
        exact h3 a j (by rw [hφa, hj])
      · rw [← ea, ← eb]
        rcases hop with h | h <;> subst h <;> simp [drop, val, comb]
    · rw [hφb] at eb
      have ht : tstep n (N, φ) ⟨op, [a, b]⟩
          = (N ++ [⟨op, [a', b']⟩], φ ++ [some (n + N.length)]) := by
        unfold tstep; dsimp only []; rw [show ([a, b] : List ℕ).getD 0 0 = a from rfl, show ([a, b] : List ℕ).getD 1 0 = b from rfl]; rw [hφa, hφb]
      rw [ht]
      have ha' := h3 a a' hφa
      have hb' := h3 b b' hφb
      have hstep' : run (N ++ [⟨op, [a', b']⟩]) (List.ofFn x)
          = run N (List.ofFn x) ++ [comb op ((run N (List.ofFn x)).getD a' false) ((run N (List.ofFn x)).getD b' false)] := by
        rw [run_append, step]
        simp only [List.map_cons, List.map_nil]
        rw [eval_two op hop]
      refine ⟨by simp [h1]; omega, ?_, ?_, ?_, ?_, by simp; omega, ?_, h8' _⟩
      · rw [hstep, hstep']
        refine snoc_val _ _ _ φ _ _ (by rw [hWl, h1]) h2 ?_ ?_
        · intro w
          rcases hφw : φ.getD w none with _ | j
          · rfl
          · have := h3 w j hφw
            simp only [val]
            rw [List.getD_append _ _ _ _ (by omega)]
        · simp only [val] at ea eb ⊢
          rw [← hW'l, List.getD_append_right _ _ _ _ le_rfl]
          rw [Nat.sub_self, List.getD_cons_zero, ea, eb]
      · intro w j hj
        have := h3' (n + N.length + 1) (by omega) _ (fun j hj => by simp at hj; omega) w j hj
        simp; omega
      · intro g hg
        rcases List.mem_append.1 hg with hg | hg
        · exact h4 g hg
        · simp at hg; subst hg; exact ⟨hop, rfl⟩
      · intro k i hi
        rcases lt_trichotomy k N.length with hk | hk | hk
        · rw [List.getD_append _ _ _ _ hk] at hi; exact h5 k i hi
        · subst hk
          rw [List.getD_append_right _ _ _ _ le_rfl] at hi
          simp at hi
          rcases hi with hi | hi <;> omega
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
          simp at hi
      · intro hc
        have hc : N.length = gs.length := by simpa using hc
        obtain ⟨hN, hid⟩ := h7 hc
        have hav : a ≠ v.val := fun e => by rw [e, h8] at hφa; cases hφa
        have hbv : b ≠ v.val := fun e => by rw [e, h8] at hφb; cases hφb
        have e1 := hid a (by omega) hav
        have e2 := hid b (by omega) hbv
        rw [hφa] at e1; rw [hφb] at e2
        cases e1; cases e2
        refine ⟨by rw [hN], ?_⟩
        intro w hw hwv
        have hw : w < φ.length + 1 := by simpa using hw
        rcases Nat.lt_succ_iff_lt_or_eq.1 hw with hw | hw
        · rw [List.getD_append _ _ _ _ hw]; exact hid w hw hwv
        · subst hw
          rw [List.getD_append_right _ _ _ _ le_rfl]
          simp; omega

theorem inv_trans (n : ℕ) (v : Fin n) (x : Fin n → Bool) (gs : List Gate)
    (hA : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hR : ∀ k < gs.length, ∀ i ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs, i < n + k) :
    Inv n v x gs (trans n v gs).1 (trans n v gs).2 := by
  induction gs using List.reverseRecOn with
  | nil => exact inv_init n v x
  | append_singleton gs g ih =>
    have ih := ih (fun g hg => hA g (List.mem_append_left _ hg)) (fun k hk i hi => by
      have := hR k (by simp; omega) i
      rw [List.getD_append _ _ _ _ hk] at this
      exact this hi)
    obtain ⟨hop, hlen⟩ := hA g (by simp)
    have hr := hR gs.length (by simp)
    rw [List.getD_append_right _ _ _ _ le_rfl] at hr
    simp at hr
    obtain ⟨op, ins⟩ := g
    simp only at hop hlen hr
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hlen
    rw [trans_append]
    exact inv_step n v x gs _ _ op a b hop (hr a (by simp)) (hr b (by simp)) ih

end PEqualNP.Outside.L_meta_5720

theorem PEqualNP.Outside.L_meta_5720 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1), PEqualNP.TopForm.IsAO2 x1 x2 → (∃ (x5 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x5 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x5 x3 Bool.false)) → (∃ (x6 : Fin x1 → Bool) (x7 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x6 x3 Bool.false) ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x7 x3 Bool.false)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size < x2.size ∧ ∀ (x8 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x7 x8 = PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x8 x3 Bool.false) := by
  intro n C v hC hdep hnc
  obtain ⟨hAO, hRB, hTwo⟩ := hC
  have hA : ∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨hAO g hg, hTwo g hg⟩
  have hI := fun x => PEqualNP.Outside.L_meta_5720.inv_trans n v x C.gates hA
    (fun k hk i hi => hRB k hk i hi)
  have hcf : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin n → Bool),
      PEqualNP.MetaComplexity.circuitFun n D x
        = (PEqualNP.Outside.L_meta_5720.run D.gates (List.ofFn x)).getD D.output false :=
    fun D x => rfl
  obtain ⟨y, z, hyz⟩ := hnc
  have hex : ∃ y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C
      (Function.update y v false) = true := by
    by_contra hne
    have hne' : ∀ y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C
        (Function.update y v false) = false := fun y => by
      by_contra h
      exact hne ⟨y, by simpa using h⟩
    have e1 := hne' y
    have e2 := hne' z
    exact hyz (by rw [e1, e2])
  obtain ⟨y, hy⟩ := hex
  obtain ⟨_, k2, _, _, _, _, _, _⟩ := hI y
  have hy2 := k2 C.output
  rw [← hcf C, hy] at hy2
  rcases hφo : (PEqualNP.Outside.L_meta_5720.trans n v C.gates).2.getD C.output none with _ | j
  · rw [hφo] at hy2; simp [PEqualNP.Outside.L_meta_5720.val] at hy2
  have hfun : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n
      ⟨(PEqualNP.Outside.L_meta_5720.trans n v C.gates).1, j⟩ x
      = PEqualNP.MetaComplexity.circuitFun n C (Function.update x v false) := by
    intro x
    obtain ⟨_, k2, _, _, _, _, _, _⟩ := hI x
    have := k2 C.output
    rw [hφo] at this
    rw [hcf, hcf]
    exact this
  obtain ⟨k1, _, _, k4, k5, k6, k7, k8⟩ := hI y
  refine ⟨⟨(PEqualNP.Outside.L_meta_5720.trans n v C.gates).1, j⟩,
    ⟨fun g hg => (k4 g hg).1, fun k _ i hi => k5 k i hi, fun g hg => (k4 g hg).2⟩, ?_, hfun⟩
  rcases Nat.lt_or_ge (PEqualNP.Outside.L_meta_5720.trans n v C.gates).1.length C.gates.length
    with hlt | hge
  · exact hlt
  · exfalso
    obtain ⟨hN, hid⟩ := k7 (le_antisymm k6 hge)
    have hov : C.output ≠ v.val := fun e => by rw [e, k8] at hφo; cases hφo
    have hol : C.output < (PEqualNP.Outside.L_meta_5720.trans n v C.gates).2.length := by
      by_contra hc
      rw [List.getD_eq_default _ _ (by omega)] at hφo
      cases hφo
    have := hid C.output hol hov
    rw [hφo] at this
    cases this
    obtain ⟨x, hx⟩ := hdep
    apply hx
    rw [← hfun x, hN]
