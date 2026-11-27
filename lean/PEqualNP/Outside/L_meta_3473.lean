import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3473

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A generic evaluation of a list of two-input gates over values of type a.
def gw {α : Type} (z : α) (ev : GateOp → α → α → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun w g => w ++ [ev g.op (w.getD (g.inputs.getD 0 0) z) (w.getD (g.inputs.getD 1 0) z)])
    init

theorem gw_snoc {α : Type} (z : α) (ev : GateOp → α → α → α) (gs : List Gate) (g : Gate)
    (init : List α) :
    gw z ev (gs ++ [g]) init = gw z ev gs init ++
      [ev g.op ((gw z ev gs init).getD (g.inputs.getD 0 0) z)
        ((gw z ev gs init).getD (g.inputs.getD 1 0) z)] := by
  simp only [gw, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem gw_length {α : Type} (z : α) (ev : GateOp → α → α → α) (gs : List Gate) (init : List α) :
    (gw z ev gs init).length = init.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [gw]
  | append_singleton gs g ih => rw [gw_snoc]; simp [ih]; omega

theorem getD_snoc {α : Type} (l : List α) (x d : α) (i : ℕ) :
    (l ++ [x]).getD i d = if i < l.length then l.getD i d else if i = l.length then x else d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem getD_ge {α : Type} (l : List α) (d : α) (i : ℕ) (h : l.length ≤ i) : l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; simp

theorem gw_prefix {α : Type} (z : α) (ev : GateOp → α → α → α) (gs : List Gate) (init : List α)
    (i : ℕ) (hi : i < init.length) : (gw z ev gs init).getD i z = init.getD i z := by
  induction gs using List.reverseRecOn with
  | nil => simp [gw]
  | append_singleton gs g ih =>
    rw [gw_snoc, getD_snoc, gw_length, if_pos (by omega), ih]

-- Relations between two evaluations are carried by the gates.
theorem gw_rel {α : Type} (z : α) (ev : GateOp → α → α → α) (R : α → α → Prop) (P : ℕ → Prop)
    (hz : R z z) (hev : ∀ op a b a' b', R a a' → R b b' → R (ev op a b) (ev op a' b'))
    (gs : List Gate) (hgs : ∀ g ∈ gs, P (g.inputs.getD 0 0) ∧ P (g.inputs.getD 1 0))
    (i1 i2 : List α) (hl : i1.length = i2.length)
    (hi : ∀ i, P i → R (i1.getD i z) (i2.getD i z)) :
    ∀ i, P i → R ((gw z ev gs i1).getD i z) ((gw z ev gs i2).getD i z) := by
  induction gs using List.reverseRecOn with
  | nil => simpa [gw] using hi
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hgs g' (by simp [hg']))
    have hg := hgs g (by simp)
    intro i hPi
    rw [gw_snoc, gw_snoc, getD_snoc, getD_snoc, gw_length, gw_length, hl]
    split_ifs with h1 h2
    · rw [← hl, ← gw_length z ev gs i1] at h1
      have := ih' i hPi
      simpa using this
    · exact hev _ _ _ _ _ (ih' _ hg.1) (ih' _ hg.2)
    · exact hz

-- The constant propagation of input v set to false.
def initMap (n v : ℕ) : List (Option ℕ) := (List.range n).map fun i => if i = v then none else some i

def pstep (n : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) : List Gate × List (Option ℕ) :=
  match g.op, s.2.getD (g.inputs.getD 0 0) none, s.2.getD (g.inputs.getD 1 0) none with
  | GateOp.and, some a, some b => (s.1 ++ [⟨g.op, [a, b]⟩], s.2 ++ [some (n + s.1.length)])
  | GateOp.and, _, _ => (s.1, s.2 ++ [none])
  | _, some a, some b => (s.1 ++ [⟨g.op, [a, b]⟩], s.2 ++ [some (n + s.1.length)])
  | _, some a, none => (s.1, s.2 ++ [some a])
  | _, none, some b => (s.1, s.2 ++ [some b])
  | _, none, none => (s.1, s.2 ++ [none])

def proc (n v : ℕ) (gs : List Gate) : List Gate × List (Option ℕ) :=
  gs.foldl (pstep n) ([], initMap n v)

theorem proc_snoc (n v : ℕ) (gs : List Gate) (g : Gate) :
    proc n v (gs ++ [g]) = pstep n (proc n v gs) g := by
  simp only [proc, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem initMap_getD (n v i : ℕ) :
    (initMap n v).getD i none = if i < n ∧ i ≠ v then some i else none := by
  unfold initMap
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · simp [h]
  · rw [List.getElem?_eq_none (by simp; omega)]; simp [h]

theorem pstep_cases (n : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) :
    (∃ a b, s.2.getD (g.inputs.getD 0 0) none = some a ∧ s.2.getD (g.inputs.getD 1 0) none = some b ∧
      pstep n s g = (s.1 ++ [⟨g.op, [a, b]⟩], s.2 ++ [some (n + s.1.length)])) ∨
    (pstep n s g = (s.1, s.2 ++ [none]) ∧
      (s.2.getD (g.inputs.getD 0 0) none = none ∨ s.2.getD (g.inputs.getD 1 0) none = none) ∧
      (g.op ≠ GateOp.and → s.2.getD (g.inputs.getD 0 0) none = none ∧
        s.2.getD (g.inputs.getD 1 0) none = none)) ∨
    (∃ a, g.op ≠ GateOp.and ∧ s.2.getD (g.inputs.getD 0 0) none = some a ∧
      s.2.getD (g.inputs.getD 1 0) none = none ∧ pstep n s g = (s.1, s.2 ++ [some a])) ∨
    (∃ b, g.op ≠ GateOp.and ∧ s.2.getD (g.inputs.getD 0 0) none = none ∧
      s.2.getD (g.inputs.getD 1 0) none = some b ∧ pstep n s g = (s.1, s.2 ++ [some b])) := by
  unfold pstep
  generalize s.2.getD (g.inputs.getD 0 0) none = ma
  generalize s.2.getD (g.inputs.getD 1 0) none = mb
  rcases g with ⟨op, ins⟩
  cases op <;> cases ma <;> cases mb <;> simp

theorem proc_struct (n v : ℕ) (hv : v < n) (gs : List Gate) :
    (proc n v gs).2.length = n + gs.length ∧
    (∀ i j, (proc n v gs).2.getD i none = some j → j < n + (proc n v gs).1.length) ∧
    (∀ k < (proc n v gs).1.length, ∀ i ∈ ((proc n v gs).1.getD k ⟨GateOp.or, []⟩).inputs,
      i < n + k) ∧
    (∀ g ∈ (proc n v gs).1, (∃ g0 ∈ gs, g.op = g0.op) ∧ g.inputs.length = 2) ∧
    (proc n v gs).2.getD v none = none ∧
    (proc n v gs).1.length ≤ gs.length ∧
    ((∃ g ∈ gs, g.inputs.getD 0 0 = v ∨ g.inputs.getD 1 0 = v) →
      (proc n v gs).1.length < gs.length) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨by simp [proc, initMap], ?_, by simp [proc], by simp [proc], ?_, by simp [proc],
      by simp⟩
    · intro i j h
      simp only [proc, List.foldl_nil, initMap_getD] at h
      split_ifs at h with h1
      · simp at h; simp [proc]; omega
    · simp only [proc, List.foldl_nil]; rw [initMap_getD]; simp
  | append_singleton gs g ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih
    rw [proc_snoc]
    set s := proc n v gs with hs
    have hv' : v < s.2.length := by omega
    rcases pstep_cases n s g with ⟨a, b, ha, hb, he⟩ | ⟨he, hn, _⟩ | ⟨a, _, ha, hb, he⟩ |
      ⟨b, _, ha, hb, he⟩ <;> rw [he] <;> simp only
    · refine ⟨by simp [h1]; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i j hij
        rw [getD_snoc] at hij
        split_ifs at hij with c1 c2
        · have := h2 i j hij; simp; omega
        · simp at hij; simp; omega
      · intro k hk i hi
        simp only [List.length_append, List.length_singleton] at hk
        rw [getD_snoc] at hi
        split_ifs at hi with c1 c2
        · exact h3 k c1 i hi
        · subst c2
          simp at hi
          rcases hi with rfl | rfl
          · have := h2 _ _ ha; omega
          · have := h2 _ _ hb; omega
        · omega
      · intro g' hg'
        simp only [List.mem_append, List.mem_singleton] at hg'
        rcases hg' with hg' | rfl
        · obtain ⟨⟨g0, hg0, hop⟩, hl⟩ := h4 g' hg'
          exact ⟨⟨g0, by simp [hg0], hop⟩, hl⟩
        · exact ⟨⟨g, by simp, rfl⟩, by simp⟩
      · rw [getD_snoc, if_pos hv']; exact h5
      · simp; omega
      · intro ⟨g', hg', hr⟩
        simp only [List.mem_append, List.mem_singleton] at hg'
        rcases hg' with hg' | rfl
        · have := h7 ⟨g', hg', hr⟩; simp; omega
        · rcases hr with hr | hr
          · rw [hr, h5] at ha; simp at ha
          · rw [hr, h5] at hb; simp at hb
    all_goals
      refine ⟨by simp [h1]; omega, ?_, h3, ?_, ?_, by simp; omega, ?_⟩
      · intro i j hij
        rw [getD_snoc] at hij
        split_ifs at hij with c1 c2
        all_goals first
          | exact h2 i j hij
          | (simp at hij; done)
          | (simp at hij; subst hij; exact h2 _ _ ha)
          | (simp at hij; subst hij; exact h2 _ _ hb)
      · intro g' hg'
        obtain ⟨⟨g0, hg0, hop⟩, hl⟩ := h4 g' hg'
        exact ⟨⟨g0, by simp [hg0], hop⟩, hl⟩
      · rw [getD_snoc, if_pos hv']; exact h5
      · intro ⟨g', hg', hr⟩
        simp only [List.mem_append, List.mem_singleton] at hg'
        rcases hg' with hg' | rfl
        · have := h7 ⟨g', hg', hr⟩; simp; omega
        · simp; omega

-- The values: every old wire either carries z (with v set to z) or is copied by a new wire.
theorem proc_sem {α : Type} (z : α) (ev : GateOp → α → α → α)
    (hA1 : ∀ y, ev GateOp.and z y = z) (hA2 : ∀ y, ev GateOp.and y z = z)
    (hO1 : ∀ op, op ≠ GateOp.and → ∀ y, ev op z y = y)
    (hO2 : ∀ op, op ≠ GateOp.and → ∀ y, ev op y z = y)
    (n v : ℕ) (hv : v < n) (initO initN : List α) (hO : initO.length = n)
    (hN : initN.length = n) (hOv : initO.getD v z = z)
    (hagree : ∀ i < n, i ≠ v → initN.getD i z = initO.getD i z) (gs : List Gate) :
    ∀ i, ((proc n v gs).2.getD i none = none → (gw z ev gs initO).getD i z = z) ∧
      (∀ j, (proc n v gs).2.getD i none = some j →
        (gw z ev (proc n v gs).1 initN).getD j z = (gw z ev gs initO).getD i z) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i
    simp only [proc, List.foldl_nil, initMap_getD]
    constructor
    · intro h
      split_ifs at h with c
      all_goals first
        | (simp at h; done)
        | skip
      all_goals
        simp only [gw, List.foldl_nil]
        by_cases hi : i < n
        · have : i = v := by omega
          subst this; exact hOv
        · exact getD_ge _ _ _ (by omega)
    · intro j h
      split_ifs at h with c
      · simp at h; subst h; simp only [gw, List.foldl_nil]; exact hagree i c.1 c.2
  | append_singleton gs g ih =>
    obtain ⟨h1, h2, -, -, -, -, -⟩ := proc_struct n v hv gs
    rw [proc_snoc]
    set s := proc n v gs with hs
    have hlo : (gw z ev gs initO).length = s.2.length := by rw [gw_length, h1, hO]
    have hln : (gw z ev s.1 initN).length = n + s.1.length := by rw [gw_length, hN]
    -- old entries keep their meaning
    have old : ∀ e : Option ℕ, ∀ ng : List Gate, (∀ j, (∃ i, s.2.getD i none = some j) →
        (gw z ev ng initN).getD j z = (gw z ev s.1 initN).getD j z) →
        (e = none → ev g.op ((gw z ev gs initO).getD (g.inputs.getD 0 0) z)
            ((gw z ev gs initO).getD (g.inputs.getD 1 0) z) = z) →
        (∀ j, e = some j → (gw z ev ng initN).getD j z = ev g.op
            ((gw z ev gs initO).getD (g.inputs.getD 0 0) z)
            ((gw z ev gs initO).getD (g.inputs.getD 1 0) z)) →
        ∀ i, ((s.2 ++ [e]).getD i none = none → (gw z ev (gs ++ [g]) initO).getD i z = z) ∧
          (∀ j, (s.2 ++ [e]).getD i none = some j →
            (gw z ev ng initN).getD j z = (gw z ev (gs ++ [g]) initO).getD i z) := by
      intro e ng hkeep hnone hsome i
      rw [gw_snoc, getD_snoc, getD_snoc, hlo]
      split_ifs with c1 c2
      · exact ⟨(ih i).1, fun j hj => (hkeep j ⟨i, hj⟩).trans ((ih i).2 j hj)⟩
      · exact ⟨hnone, hsome⟩
      · exact ⟨fun _ => rfl, fun j hj => by simp at hj⟩
    have va := ih (g.inputs.getD 0 0)
    have vb := ih (g.inputs.getD 1 0)
    rcases pstep_cases n s g with ⟨a, b, ha, hb, he⟩ | ⟨he, hn, hn2⟩ | ⟨a, hop, ha, hb, he⟩ |
      ⟨b, hop, ha, hb, he⟩ <;> rw [he] <;> simp only
    · apply old
      · rintro j ⟨i, hi⟩
        rw [gw_snoc, getD_snoc, hln, if_pos (h2 i j hi)]
      · intro h; simp at h
      · intro j hj
        simp at hj; subst hj
        rw [gw_snoc, getD_snoc, hln, if_neg (by omega), if_pos rfl]
        simp only [List.getD_cons_zero, List.getD_cons_succ]
        rw [va.2 a ha, vb.2 b hb]
    · apply old
      · intro j _; rfl
      · intro _
        by_cases hop : g.op = GateOp.and
        · rcases hn with h | h
          · rw [va.1 h, hop, hA1]
          · rw [vb.1 h, hop, hA2]
        · obtain ⟨h, h'⟩ := hn2 hop
          rw [va.1 h, vb.1 h', hO1 _ hop]
      · intro j hj; simp at hj
    · apply old
      · intro j _; rfl
      · intro h; simp at h
      · intro j hj
        simp at hj; subst hj
        rw [vb.1 hb, hO2 _ hop, va.2 a ha]
    · apply old
      · intro j _; rfl
      · intro h; simp at h
      · intro j hj
        simp at hj; subst hj
        rw [va.1 ha, hO1 _ hop, vb.2 b hb]

-- The two semantics as instances of gw.
def evB : GateOp → Bool → Bool → Bool
  | GateOp.and, a, b => a && b
  | _, a, b => a || b

def evL : GateOp → Bool × Bool → Bool × Bool → Bool × Bool
  | GateOp.and, p, q => (p.1 && q.1, (p.1 && q.2) || (p.2 && q.1))
  | _, p, q => (p.1 || q.1, p.2 || q.2)

theorem wires_eq (C : Circuit)
    (h : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x : List Bool) : C.wires x = gw false evB C.gates x := by
  unfold Circuit.wires gw
  generalize C.gates = gs at h
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))]
    congr 1
    obtain ⟨hop, hl⟩ := h g (by simp)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl
    rcases hop with hop | hop <;> simp [hop, hab, evB, GateOp.eval]

theorem linear_eq (C : Circuit)
    (h : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (isLine : ℕ → Bool) (x : List Bool) :
    PEqualNP.ReadK.linearParts C isLine x = gw (false, false) evL C.gates
      ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)) := by
  unfold PEqualNP.ReadK.linearParts gw
  generalize ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)) = init
  generalize C.gates = gs at h
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))]
    congr 1
    obtain ⟨hop, hl⟩ := h g (by simp)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl
    rcases hop with hop | hop <;> simp [hop, hab, evL]

theorem evB_l1 (y : Bool) : evB GateOp.and false y = false := by simp [evB]
theorem evB_l2 (y : Bool) : evB GateOp.and y false = false := by simp [evB]
theorem evB_l3 (op : GateOp) (hop : op ≠ GateOp.and) (y : Bool) : evB op false y = y := by
  cases op <;> simp_all [evB]
theorem evB_l4 (op : GateOp) (hop : op ≠ GateOp.and) (y : Bool) : evB op y false = y := by
  cases op <;> simp_all [evB]
theorem evL_l1 (y : Bool × Bool) : evL GateOp.and (false, false) y = (false, false) := by simp [evL]
theorem evL_l2 (y : Bool × Bool) : evL GateOp.and y (false, false) = (false, false) := by simp [evL]
theorem evL_l3 (op : GateOp) (hop : op ≠ GateOp.and) (y : Bool × Bool) :
    evL op (false, false) y = y := by
  cases op <;> simp_all [evL]
theorem evL_l4 (op : GateOp) (hop : op ≠ GateOp.and) (y : Bool × Bool) :
    evL op y (false, false) = y := by
  cases op <;> simp_all [evL]
theorem evB_mono (op : GateOp) (a b a' b' : Bool) (e1 : a = true → a' = true)
    (e2 : b = true → b' = true) : evB op a b = true → evB op a' b' = true := by
  cases op <;> cases a <;> cases b <;> cases a' <;> cases b' <;> simp_all [evB]

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < n then f ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · simp [h]
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

end PEqualNP.Outside.L_meta_3473

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_3473 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1), PEqualNP.TopForm.IsAO2 x1 x2 → (∃ (x5 : Fin x1 → Bool) (x6 : Fin x1 → Bool), (∀ (x7 : Fin x1), x7 ≠ x3 → x5 x7 = x6 x7) ∧ PEqualNP.MetaComplexity.circuitFun x1 x2 x5 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x6) → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x6 : Fin x1) => Decidable.decide (x6 = x3)) = Bool.false → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size < x2.size ∧ (∀ (x8 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x7 x8 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 x2 x8 = Bool.true) ∧ (∀ (x8 : Fin x1 → Bool), x8 x3 = Bool.false → PEqualNP.MetaComplexity.circuitFun x1 x7 x8 = PEqualNP.MetaComplexity.circuitFun x1 x2 x8) ∧ ∀ (x8 : ℕ → Bool) (x9 x10 : ℕ), ↑x3 ≠ x9 → ↑x3 ≠ x10 → PEqualNP.ReadK.lineSingle x7 x1 x8 x9 x10 = PEqualNP.ReadK.lineSingle x2 x1 x8 x9 x10 := by
  intro n C v hAO hdep hev
  obtain ⟨hand, hrb, hlen⟩ := hAO
  have hgs : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨hand g hg, hlen g hg⟩
  have hv : (v : ℕ) < n := v.isLt
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := L_meta_3473.proc_struct n v hv C.gates
  have hng : ∀ g ∈ (L_meta_3473.proc n v C.gates).1,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
    intro g hg
    obtain ⟨⟨g0, hg0, hop⟩, hl⟩ := h4 g hg
    exact ⟨hop ▸ (hgs g0 hg0).1, hl⟩
  let ng := (L_meta_3473.proc n v C.gates).1
  let out' : ℕ := match (L_meta_3473.proc n v C.gates).2.getD C.output none with
    | some o => o
    | none => n + ng.length
  let C' : Circuit := ⟨ng, out'⟩
  have key : ∀ {α : Type} (z : α) (ev : GateOp → α → α → α),
      (∀ y, ev GateOp.and z y = z) → (∀ y, ev GateOp.and y z = z) →
      (∀ op, op ≠ GateOp.and → ∀ y, ev op z y = y) →
      (∀ op, op ≠ GateOp.and → ∀ y, ev op y z = y) →
      ∀ (initO initN : List α), initO.length = n → initN.length = n → initO.getD v z = z →
      (∀ i < n, i ≠ v → initN.getD i z = initO.getD i z) →
      (L_meta_3473.gw z ev ng initN).getD out' z =
        (L_meta_3473.gw z ev C.gates initO).getD C.output z := by
    intro α z ev hA1 hA2 hO1 hO2 initO initN hO hN hOv hag
    have hs := L_meta_3473.proc_sem z ev hA1 hA2 hO1 hO2 n v hv initO initN hO hN hOv hag
      C.gates C.output
    simp only [out']
    cases hm : (L_meta_3473.proc n v C.gates).2.getD C.output none with
    | none =>
      rw [hs.1 hm]
      exact L_meta_3473.getD_ge _ _ _ (by rw [L_meta_3473.gw_length, hN])
    | some o => exact hs.2 o hm
  have lawsB1 := L_meta_3473.evB_l1
  have lawsB2 := L_meta_3473.evB_l2
  have lawsB3 := L_meta_3473.evB_l3
  have lawsB4 := L_meta_3473.evB_l4
  have lawsL1 := L_meta_3473.evL_l1
  have lawsL2 := L_meta_3473.evL_l2
  have lawsL3 := L_meta_3473.evL_l3
  have lawsL4 := L_meta_3473.evL_l4
  -- some gate reads v
  have hread : ∃ g ∈ C.gates, g.inputs.getD 0 0 = v ∨ g.inputs.getD 1 0 = v := by
    by_contra hno
    push_neg at hno
    obtain ⟨x5, x6, hagr, hne⟩ := hdep
    by_cases ho : C.output = v
    · apply absurd hev
      unfold circuitFun Circuit.eval
      rw [L_meta_3473.wires_eq C hgs, ho, L_meta_3473.gw_prefix _ _ _ _ _ (by simp [hv]),
        L_meta_3473.ofFn_getD, dif_pos hv]
      simp
    · apply hne
      unfold circuitFun Circuit.eval
      rw [L_meta_3473.wires_eq C hgs, L_meta_3473.wires_eq C hgs]
      refine L_meta_3473.gw_rel false L_meta_3473.evB Eq (fun i => i ≠ (v : ℕ)) rfl
        (fun _ _ _ _ _ e1 e2 => by rw [e1, e2]) C.gates hno _ _ (by simp) ?_ C.output ho
      intro i hi
      rw [L_meta_3473.ofFn_getD, L_meta_3473.ofFn_getD]
      split_ifs with h
      · exact hagr ⟨i, h⟩ (fun e => hi (by rw [← e]))
      · rfl
  -- the value of the new circuit
  have hval : ∀ x8 : Fin n → Bool, circuitFun n C' x8 =
      circuitFun n C (fun i => if i = v then false else x8 i) := by
    intro x8
    unfold circuitFun Circuit.eval
    rw [L_meta_3473.wires_eq C' hng, L_meta_3473.wires_eq C hgs]
    apply key false L_meta_3473.evB lawsB1 lawsB2 lawsB3 lawsB4 _ _ (by simp) (by simp)
    · rw [L_meta_3473.ofFn_getD, dif_pos hv]; simp
    · intro i hi hiv
      rw [L_meta_3473.ofFn_getD, L_meta_3473.ofFn_getD, dif_pos hi, dif_pos hi]
      have : (⟨i, hi⟩ : Fin n) ≠ v := fun e => hiv (by rw [← e])
      simp [this]
  refine ⟨C', ⟨fun g hg => (hng g hg).1, fun k hk i hi => h3 k hk i hi,
    fun g hg => (hng g hg).2⟩, h7 hread, ?_, ?_, ?_⟩
  · intro x8 hx
    rw [hval] at hx
    unfold circuitFun Circuit.eval at hx ⊢
    rw [L_meta_3473.wires_eq C hgs] at hx ⊢
    refine L_meta_3473.gw_rel false L_meta_3473.evB (fun a b => a = true → b = true)
      (fun _ => True) (by simp) ?_ C.gates (by simp) _ _ (by simp) ?_ C.output trivial hx
    · exact fun op a b a2 b2 e1 e2 => L_meta_3473.evB_mono op a b a2 b2 e1 e2
    · intro i _
      rw [L_meta_3473.ofFn_getD, L_meta_3473.ofFn_getD]
      split_ifs <;> simp_all
  · intro x8 hx
    rw [hval]
    congr 1
    funext i
    split_ifs with h
    · rw [h, hx]
    · rfl
  · intro isLine p l hp hl
    unfold PEqualNP.ReadK.lineSingle
    rw [L_meta_3473.linear_eq C' hng, L_meta_3473.linear_eq C hgs]
    congr 1
    apply key (false, false) L_meta_3473.evL lawsL1 lawsL2 lawsL3 lawsL4 _ _ (by simp) (by simp)
    · rw [List.getD_eq_getElem?_getD]
      have ep : ((v : ℕ) == p) = false := beq_eq_false_iff_ne.mpr hp
      have el : ((v : ℕ) == l) = false := beq_eq_false_iff_ne.mpr hl
      simp [List.getElem?_zipIdx, hv, ep, el]
    · intro i _ _; rfl
