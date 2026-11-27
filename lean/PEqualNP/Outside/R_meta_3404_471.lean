import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
-- Cut at the actual NOT gates. The intervening AND/OR gates retain all earlier wires.
-- Missing NOT operands and forward operands both read false, including for the last gate.
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.R_meta_3404_471
    (one : ∀ (S : Finset (Fin 9)) (A D : Circuit) (p : Option ℕ), S.card ≤ 2 →
      Monotone2 A → Monotone2 D → A.size + D.size ≤ 12 →
      let base := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 4,decide (∃ i ∈ S, x i = true)]
      let cut := fun (w : List Bool) (p : Option ℕ) => w ++ [!(p.elim false (fun i => w.getD i false))]
      let F := fun (x : Fin 9 → Bool) => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      ∃ x, D.eval (cut (A.wires (base x)) p) ≠ F x)
    (two : ∀ (S : Finset (Fin 9)) (A B D : Circuit) (p q : Option ℕ), S.card ≤ 2 →
      Monotone2 A → Monotone2 B → Monotone2 D → A.size + B.size + D.size ≤ 11 →
      let base := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 4,decide (∃ i ∈ S, x i = true)]
      let cut := fun (w : List Bool) (p : Option ℕ) => w ++ [!(p.elim false (fun i => w.getD i false))]
      let F := fun (x : Fin 9 → Bool) => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      ∃ x, D.eval (cut (B.wires (cut (A.wires (base x)) p)) q) ≠ F x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card ≤ (2 : ℕ) → (1 : ℕ) ≤ PEqualNP.NotBracket.notCount x1 → PEqualNP.NotBracket.notCount x1 ≤ (2 : ℕ) → (∀ (x7 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x8 ∈ x2, x7 x8 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x7 x8.1 && x7 x8.2) → (14 : ℕ) ≤ x1.size := by
  let _ : DecidableEq GateOp := lineDegreeGateOpDecEq
  let mark (g : Gate) := decide (g.op = GateOp.not)
  let cut := fun (w : List Bool) (p : Option ℕ) => w ++ [!(p.elim false (fun i => w.getD i false))]
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have atNot (w : List Bool) (g : Gate) (h : g.op = GateOp.not) :
      step w g = cut w g.inputs.head? := by
    obtain ⟨op,ins⟩ := g
    change op = GateOp.not at h
    subst op
    cases ins <;> rfl
  have peel (L : List Gate) (hn : 0 < (L.filter mark).length) :
      ∃ (A : List Gate) (g : Gate) (B : List Gate), L = A ++ g :: B ∧ A.filter mark = [] ∧ mark g = true := by
    induction L with
    | nil => simp at hn
    | cons h t ih =>
      by_cases test : mark h = true
      · exact ⟨[],h,t,rfl,rfl,test⟩
      · have ht : 0 < (t.filter mark).length := by simpa [List.filter_cons,test] using hn
        obtain ⟨A,g,B,rfl,hA,hg⟩ := ih ht
        exact ⟨h :: A,g,B,rfl,by simp [test,hA],hg⟩
  have counts (A B : List Gate) (g : Gate) (no : A.filter mark = []) (yes : mark g = true) :
      ((A ++ g :: B).filter mark).length = (B.filter mark).length + 1 := by simp [no,yes]
  intro C S fan sc lo hi computes
  change 1 ≤ (C.gates.filter mark).length at lo
  change (C.gates.filter mark).length ≤ 2 at hi
  by_contra! small
  obtain ⟨A,g,T,eq,clean,hg⟩ := peel C.gates lo
  have n1 : g.op = GateOp.not := of_decide_eq_true hg
  have ct := counts A T g clean hg
  rw [← eq] at ct
  have mono (U : List Gate) (o : ℕ) (inc : ∀ a ∈ U, a ∈ C.gates) (empty : U.filter mark = []) :
      Monotone2 ⟨U,o⟩ := by
    intro a ha
    obtain ⟨op,arity⟩ := fan a (inc a ha)
    have nt : a.op ≠ GateOp.not := by
      intro ht
      have mem : a ∈ U.filter mark := List.mem_filter.mpr ⟨ha,by simp [mark,ht]⟩
      rw [empty] at mem
      exact List.not_mem_nil mem
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
    exact ⟨op.imp_right (fun h => h.resolve_right nt),arity⟩
  let base := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 4,decide (∃ i ∈ S, x i = true)]
  let F := fun (x : Fin 9 → Bool) => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
  have original (x : Fin 9 → Bool) : (C.gates.foldl step (base x)).getD C.output false = F x := computes x
  have monA := mono A 0 (fun a ha => by rw [eq]; exact List.mem_append_left _ ha) clean
  have inT (a : Gate) (ha : a ∈ T) : a ∈ C.gates := by rw [eq]; exact List.mem_append_right _ (List.mem_cons_of_mem _ ha)
  change C.gates.length < 14 at small
  rw [eq,List.length_append,List.length_cons] at small
  by_cases tail0 : (T.filter mark).length = 0
  · have monT := mono T C.output inT (List.length_eq_zero_iff.mp tail0)
    obtain ⟨x,bad⟩ := one S ⟨A,0⟩ ⟨T,C.output⟩ g.inputs.head? sc monA monT (by change A.length + T.length ≤ 12; omega)
    apply bad
    have res := original x
    rw [eq,List.foldl_append,List.foldl_cons,atNot _ g n1] at res
    exact res
  · obtain ⟨B,h,D,eqT,cleanB,hh⟩ := peel T (by omega)
    have n2 : h.op = GateOp.not := of_decide_eq_true hh
    have ct2 := counts B D h cleanB hh
    rw [← eqT] at ct2
    have empty : D.filter mark = [] := List.length_eq_zero_iff.mp (by omega)
    have monB := mono B 0 (fun a ha => inT a (by rw [eqT]; exact List.mem_append_left _ ha)) cleanB
    have monD := mono D C.output (fun a ha => inT a (by rw [eqT]; exact List.mem_append_right _ (List.mem_cons_of_mem _ ha))) empty
    rw [eqT,List.length_append,List.length_cons] at small
    obtain ⟨x,bad⟩ := two S ⟨A,0⟩ ⟨B,0⟩ ⟨D,C.output⟩ g.inputs.head? h.inputs.head? sc monA monB monD (by change A.length + B.length + D.length ≤ 11; omega)
    apply bad
    have res := original x
    rw [eq,List.foldl_append,List.foldl_cons,atNot _ g n1,eqT,List.foldl_append,List.foldl_cons,atNot _ h n2] at res
    exact res
