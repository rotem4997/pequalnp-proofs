import PEqualNP.Defs

/-!
# Folding a rewired AND/OR circuit to an `IsAO2` circuit

A PROGRAM has gates indexed by a type `ι`, each an AND or an OR of two SOURCES; a source is the constant
false (`none`), an input variable or another gate. A `rank` makes it acyclic, `K` is a set of gates closed
under operands. The values `v` solve the gate equations on `K` (`Sol`).

* `fold_prog`: such a program, true at its output on the all-ones input, is an `IsAO2` circuit with at most
  one gate per gate of `K` having both operands true at the all-ones input (a gate with a false operand folds).
* `sol_exists`: the gate equations have a solution. `sol_le` / `le_sol`: super- and sub-solutions at one input.
* `fold_computes`: correctness test; a program at most `F` that accepts every edge gives a circuit for `F`.
* `redirect`: the case of a circuit whose operands are redirected or zeroed, gate numbers kept.
* `adj_of_AO`: a circuit computing `F` with a gate in its output cone has an edge to accept.
-/

namespace PEqualNP.MetaComplexity.FoldProg

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm
open PEqualNP.CleanedNonEdge

/-- A source: constant false, an input, or a gate. -/
abbrev Src (n : ℕ) (ι : Type) := Option (Fin n ⊕ ι)

/-- The value of a source at input `x` when gate `i` has value `t i`. -/
def srcAt {n : ℕ} {ι : Type} (x : Fin n → Bool) (t : ι → Bool) (s : Src n ι) : Bool :=
  s.elim false (Sum.elim x t)

/-- AND (`true`) or OR (`false`) of two bits. -/
def opv (a : Bool) (p q : Bool) : Bool := if a then p && q else p || q

theorem opv_mono (a p q p' q' : Bool) (h : p = true → p' = true) (h' : q = true → q' = true) :
    opv a p q = true → opv a p' q' = true := by
  cases a <;> cases p <;> cases q <;> cases p' <;> cases q' <;> simp_all [opv]

structure Prog (n : ℕ) (ι : Type) where
  isAnd : ι → Bool
  src : ι → Fin 2 → Src n ι

variable {n : ℕ} {ι : Type}

/-- The set `K` is closed under operands, which have smaller rank. -/
def Closed (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) : Prop :=
  ∀ i ∈ K, ∀ b : Fin 2, ∀ j : ι, P.src i b = some (Sum.inr j) → j ∈ K ∧ rank j < rank i

/-- The gate equations on `K` at one input. -/
def SolAt (P : Prog n ι) (K : Finset ι) (x : Fin n → Bool) (t : ι → Bool) : Prop :=
  ∀ i ∈ K, t i = opv (P.isAnd i) (srcAt x t (P.src i 0)) (srcAt x t (P.src i 1))

/-- The gate equations on `K` at every input. -/
def Sol (P : Prog n ι) (K : Finset ι) (v : ι → (Fin n → Bool) → Bool) : Prop :=
  ∀ x, SolAt P K x (fun i => v i x)

theorem rank_induction (rank : ι → ℕ) (p : ι → Prop)
    (h : ∀ i, (∀ j, rank j < rank i → p j) → p i) : ∀ i, p i := by
  have key : ∀ m, ∀ i, rank i = m → p i := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih => exact fun i hi => h i fun j hj => ih (rank j) (hi ▸ hj) j rfl
  exact fun i => key _ i rfl

/-- A solution is below every super-solution. The test `hs` need only hold where `K` reads. -/
theorem sol_le (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) (hcl : Closed P rank K) (x : Fin n → Bool)
    (t u : ι → Bool) (ht : SolAt P K x t)
    (hs : ∀ i ∈ K, opv (P.isAnd i) (srcAt x u (P.src i 0)) (srcAt x u (P.src i 1)) = true → u i = true) :
    ∀ i ∈ K, t i = true → u i = true := by
  refine fun i => rank_induction rank (fun i => i ∈ K → t i = true → u i = true) ?_ i
  intro i ih hi hti
  rw [ht i hi] at hti
  refine hs i hi (opv_mono _ _ _ _ _ ?_ ?_ hti)
  all_goals
    intro h
    revert h
    generalize hb : P.src i _ = s
    rcases s with _ | (a | j)
    · exact fun h => h
    · exact fun h => h
    · intro h
      obtain ⟨hj, hr⟩ := hcl i hi _ j hb
      exact ih j hr hj h

/-- A solution is above every sub-solution. -/
theorem le_sol (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) (hcl : Closed P rank K) (x : Fin n → Bool)
    (t u : ι → Bool) (ht : SolAt P K x t)
    (hs : ∀ i ∈ K, u i = true → opv (P.isAnd i) (srcAt x u (P.src i 0)) (srcAt x u (P.src i 1)) = true) :
    ∀ i ∈ K, u i = true → t i = true := by
  refine fun i => rank_induction rank (fun i => i ∈ K → u i = true → t i = true) ?_ i
  intro i ih hi hui
  rw [ht i hi]
  refine opv_mono _ _ _ _ _ ?_ ?_ (hs i hi hui)
  all_goals
    intro h
    revert h
    generalize hb : P.src i _ = s
    rcases s with _ | (a | j)
    · exact fun h => h
    · exact fun h => h
    · intro h
      obtain ⟨hj, hr⟩ := hcl i hi _ j hb
      exact ih j hr hj h

/-- Solutions are monotone in the input. -/
theorem sol_mono (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) (hcl : Closed P rank K)
    (v : ι → (Fin n → Bool) → Bool) (hv : Sol P K v) (x y : Fin n → Bool)
    (hxy : ∀ a, x a = true → y a = true) : ∀ i ∈ K, v i x = true → v i y = true := by
  refine sol_le P rank K hcl x (fun i => v i x) (fun i => v i y) (hv x) ?_
  intro i hi h
  have e := hv y i hi
  simp only at e
  rw [e]
  refine opv_mono _ _ _ _ _ ?_ ?_ h
  all_goals
    generalize P.src i _ = s
    rcases s with _ | (a | j)
    · exact fun h => h
    · exact hxy a
    · exact fun h => h

/-- The gate equations have a solution. -/
theorem sol_exists (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) (hcl : Closed P rank K) :
    ∃ v : ι → (Fin n → Bool) → Bool, Sol P K v := by
  classical
  suffices h : ∀ L : Finset ι, L ⊆ K → Closed P rank L → ∃ v : ι → (Fin n → Bool) → Bool, Sol P L v from
    h K (Finset.Subset.refl K) hcl
  intro L
  induction L using Finset.induction_on_max_value rank with
  | empty => exact fun _ _ => ⟨fun _ _ => false, fun _ i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha hmax ih =>
    intro hsub hL
    have hs : Closed P rank s := by
      intro i hi b j hj
      obtain ⟨h1, h2⟩ := hL i (Finset.mem_insert_of_mem hi) b j hj
      refine ⟨(Finset.mem_insert.1 h1).resolve_left ?_, h2⟩
      rintro rfl
      exact absurd (hmax i hi) (by omega)
    obtain ⟨v, hv⟩ := ih ((Finset.subset_insert a s).trans hsub) hs
    let v' : ι → (Fin n → Bool) → Bool := fun i x => if i = a then
      opv (P.isAnd a) (srcAt x (fun j => v j x) (P.src a 0)) (srcAt x (fun j => v j x) (P.src a 1)) else v i x
    have hsrc : ∀ i ∈ insert a s, ∀ b x, srcAt x (fun j => v' j x) (P.src i b)
        = srcAt x (fun j => v j x) (P.src i b) := by
      intro i hi b x
      rcases hb : P.src i b with _ | (c | j)
      · rfl
      · rfl
      · obtain ⟨_, hr⟩ := hL i hi b j hb
        have hja : j ≠ a := by
          rintro rfl
          rcases Finset.mem_insert.1 hi with rfl | hi'
          · exact absurd hr (lt_irrefl _)
          · exact absurd (hmax i hi') (by omega)
        simp [srcAt, v', hja]
    refine ⟨v', fun x i hi => ?_⟩
    simp only
    rw [hsrc i hi 0 x, hsrc i hi 1 x]
    rcases Finset.mem_insert.1 hi with rfl | hi'
    · simp [v']
    · have hia : i ≠ a := by
        rintro rfl
        exact ha hi'
      have := hv x i hi'
      simpa [v', hia] using this

theorem wires_length (gs : List Gate) (w0 : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).length
      = w0.length + gs.length := by
  induction gs generalizing w0 with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega

theorem wires_snoc (gs : List Gate) (g : Gate) (o : ℕ) (x : List Bool) :
    (⟨gs ++ [g], o⟩ : Circuit).wires x = (⟨gs, o⟩ : Circuit).wires x
      ++ [g.op.eval (g.inputs.map fun i => ((⟨gs, o⟩ : Circuit).wires x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem wireVal_old (gs : List Gate) (g : Gate) (w : ℕ) (hw : w < n + gs.length) (x : Fin n → Bool) :
    wireVal n ⟨gs ++ [g], 0⟩ w x = wireVal n ⟨gs, 0⟩ w x := by
  unfold wireVal
  rw [wires_snoc, List.getD_append]
  have : ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).length = n + gs.length := by
    have h := wires_length gs (List.ofFn x)
    rw [List.length_ofFn] at h
    exact h
  omega

theorem wireVal_new (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    wireVal n ⟨gs ++ [g], 0⟩ (n + gs.length) x
      = g.op.eval (g.inputs.map fun i => wireVal n ⟨gs, 0⟩ i x) := by
  unfold wireVal
  have : ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).length = n + gs.length := by
    have h := wires_length gs (List.ofFn x)
    rw [List.length_ofFn] at h
    exact h
  rw [wires_snoc, List.getD_append_right _ _ _ _ (by omega), this]
  simp

theorem wires_prefix (gs : List Gate) (w0 : List Bool) (i : ℕ) (hi : i < w0.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).getD i false
      = w0.getD i false := by
  induction gs generalizing w0 with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

theorem wireVal_input (gs : List Gate) (i : Fin n) (x : Fin n → Bool) :
    wireVal n ⟨gs, 0⟩ (i : ℕ) x = x i := by
  unfold wireVal Circuit.wires
  rw [wires_prefix _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

/-- What the induction carries: a source is constant false, or a wire computes it. -/
def Res (gs : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∀ x, f x = false) ∨ (f (fun _ => true) = true ∧ ∃ w < n + gs.length, ∀ x, wireVal n ⟨gs, 0⟩ w x = f x)

theorem res_mono (gs : List Gate) (g : Gate) (f : (Fin n → Bool) → Bool) (h : Res gs f) :
    Res (gs ++ [g]) f := by
  rcases h with h | ⟨h1, w, hw, h2⟩
  · exact Or.inl h
  · refine Or.inr ⟨h1, w, by simp; omega, fun x => ?_⟩
    rw [wireVal_old gs g w hw x, h2 x]

theorem isAO2_snoc (gs : List Gate) (o : GateOp) (ho : o = GateOp.and ∨ o = GateOp.or) (a b : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length) (h : IsAO2 n ⟨gs, 0⟩) :
    IsAO2 n ⟨gs ++ [⟨o, [a, b]⟩], 0⟩ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact h1 g hg
    · rw [List.mem_singleton.1 hg]
      exact ho
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hjl : j < gs.length
    · have e : gateAt ⟨gs ++ [⟨o, [a, b]⟩], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
        exact List.getD_append _ _ _ _ hjl
      rw [e] at hi
      exact h2 j hjl i hi
    · have hj' : j = gs.length := by omega
      subst hj'
      have e : gateAt ⟨gs ++ [⟨o, [a, b]⟩], 0⟩ gs.length = ⟨o, [a, b]⟩ := by
        simp [gateAt]
      rw [e] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact h3 g hg
    · rw [List.mem_singleton.1 hg]
      rfl

/-- The gates of `K` that stay: both operands true at the all-ones input. -/
def kept (P : Prog n ι) (v : ι → (Fin n → Bool) → Bool) (K : Finset ι) : Finset ι :=
  K.filter fun i => srcAt (fun _ => true) (fun j => v j fun _ => true) (P.src i 0) = true ∧
    srcAt (fun _ => true) (fun j => v j fun _ => true) (P.src i 1) = true

theorem build (P : Prog n ι) (rank : ι → ℕ) (v : ι → (Fin n → Bool) → Bool) (K : Finset ι)
    (hcl : Closed P rank K) (hv : Sol P K v) :
    ∃ gs : List Gate, IsAO2 n ⟨gs, 0⟩ ∧ gs.length ≤ (kept P v K).card ∧ ∀ i ∈ K, Res gs (v i) := by
  classical
  induction K using Finset.induction_on_max_value rank with
  | empty =>
    refine ⟨[], ⟨?_, ?_, ?_⟩, by simp, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    · intro g hg; simp at hg
    · intro j hj; simp at hj
    · intro g hg; simp at hg
  | insert a s ha hmax ih =>
    have hs : Closed P rank s := by
      intro i hi b j hj
      obtain ⟨h1, h2⟩ := hcl i (Finset.mem_insert_of_mem hi) b j hj
      refine ⟨(Finset.mem_insert.1 h1).resolve_left ?_, h2⟩
      rintro rfl
      exact absurd (hmax i hi) (by omega)
    obtain ⟨gs, hAO, hlen, hres⟩ := ih hs fun x i hi => hv x i (Finset.mem_insert_of_mem hi)
    have hsrc' : ∀ b : Fin 2, Res gs (fun x => srcAt x (fun j => v j x) (P.src a b)) := by
      intro b
      rcases hb : P.src a b with _ | (c | j)
      · exact Or.inl fun x => rfl
      · exact Or.inr ⟨rfl, c, by have := c.2; omega, fun x => wireVal_input gs c x⟩
      · obtain ⟨h1, h2⟩ := hcl a (Finset.mem_insert_self a s) b j hb
        refine hres j ((Finset.mem_insert.1 h1).resolve_left ?_)
        rintro rfl
        exact absurd h2 (lt_irrefl _)
    have hsrc : ∀ b : Fin 2, (∀ x, srcAt x (fun j => v j x) (P.src a b) = false) ∨
        (srcAt (fun _ => true) (fun j => v j fun _ => true) (P.src a b) = true ∧ ∃ w < n + gs.length,
          ∀ x, wireVal n ⟨gs, 0⟩ w x = srcAt x (fun j => v j x) (P.src a b)) := hsrc'
    have hva : ∀ x, v a x = opv (P.isAnd a) (srcAt x (fun j => v j x) (P.src a 0))
        (srcAt x (fun j => v j x) (P.src a 1)) := fun x => hv x a (Finset.mem_insert_self a s)
    have hsub : kept P v s ⊆ kept P v (insert a s) :=
      Finset.filter_subset_filter _ (Finset.subset_insert a s)
    have hlen' : gs.length ≤ (kept P v (insert a s)).card := hlen.trans (Finset.card_le_card hsub)
    have same : Res gs (v a) → ∃ gs : List Gate, IsAO2 n ⟨gs, 0⟩ ∧
        gs.length ≤ (kept P v (insert a s)).card ∧ ∀ i ∈ insert a s, Res gs (v i) := by
      intro h
      refine ⟨gs, hAO, hlen', fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi'
      · exact h
      · exact hres i hi'
    rcases hsrc 0 with h0 | ⟨h0, w0, hw0, hv0⟩
    · -- first operand constant false
      refine same ?_
      cases hop : P.isAnd a
      · rcases hsrc 1 with h1 | ⟨h1, w1, hw1, hv1⟩
        · exact Or.inl fun x => by rw [hva x, h0 x, h1 x, hop]; rfl
        · refine Or.inr ⟨by rw [hva, h0, h1, hop]; rfl, w1, hw1, fun x => ?_⟩
          rw [hv1 x, hva x, h0 x, hop]; simp [opv]
      · exact Or.inl fun x => by rw [hva x, h0 x, hop]; rfl
    · rcases hsrc 1 with h1 | ⟨h1, w1, hw1, hv1⟩
      · refine same ?_
        cases hop : P.isAnd a
        · refine Or.inr ⟨by rw [hva, h0, h1, hop]; rfl, w0, hw0, fun x => ?_⟩
          rw [hv0 x, hva x, h1 x, hop]; simp [opv]
        · exact Or.inl fun x => by rw [hva x, h1 x, hop]; simp [opv]
      · -- both operands kept: append a gate
        have hak : a ∈ kept P v (insert a s) :=
          Finset.mem_filter.2 ⟨Finset.mem_insert_self a s, h0, h1⟩
        have hcard : (kept P v s).card + 1 ≤ (kept P v (insert a s)).card := by
          have hnot : a ∉ kept P v s := fun h => ha (Finset.mem_filter.1 h).1
          rw [← Finset.card_insert_of_notMem hnot]
          exact Finset.card_le_card (Finset.insert_subset hak hsub)
        let o : GateOp := if P.isAnd a then GateOp.and else GateOp.or
        have ho : o = GateOp.and ∨ o = GateOp.or := by
          by_cases h : P.isAnd a = true <;> simp [o, h]
        refine ⟨gs ++ [⟨o, [w0, w1]⟩], isAO2_snoc gs o ho w0 w1 hw0 hw1 hAO, ?_, fun i hi => ?_⟩
        · simp only [List.length_append, List.length_singleton]; omega
        · rcases Finset.mem_insert.1 hi with rfl | hi'
          · refine Or.inr ⟨?_, n + gs.length, by simp, fun x => ?_⟩
            · rw [hva]
              simp only at h0 h1
              rw [h0, h1]
              cases P.isAnd i <;> rfl
            · rw [wireVal_new, hva x]
              simp only [List.map_cons, List.map_nil, hv0 x, hv1 x]
              by_cases h : P.isAnd i = true
              · simp [o, h, opv, GateOp.eval]
              · simp [o, h, opv, GateOp.eval]
          · exact res_mono gs _ _ (hres i hi')

/-- The fold: a program true at its output on the all-ones input is an `IsAO2` circuit, with at most one
gate per gate of `K` whose two operands are both true at the all-ones input. -/
theorem fold_prog (P : Prog n ι) (rank : ι → ℕ) (v : ι → (Fin n → Bool) → Bool) (K : Finset ι)
    (hcl : Closed P rank K) (hv : Sol P K v) (o : Src n ι) (ho : ∀ j, o = some (Sum.inr j) → j ∈ K)
    (h1 : srcAt (fun _ => true) (fun j => v j fun _ => true) o = true) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ (kept P v K).card ∧
      ∀ x : Fin n → Bool, circuitFun n D x = srcAt x (fun j => v j x) o := by
  obtain ⟨gs, hAO, hlen, hres⟩ := build P rank v K hcl hv
  have hR : Res gs (fun x => srcAt x (fun j => v j x) o) := by
    rcases o with _ | (c | j)
    · exact Or.inl fun x => rfl
    · exact Or.inr ⟨rfl, c, by have := c.2; omega, fun x => wireVal_input gs c x⟩
    · exact hres j (ho j rfl)
  rcases hR with h | ⟨_, w, _, hw⟩
  · exact absurd (h1.symm.trans (h fun _ => true)) (by decide)
  · refine ⟨⟨gs, w⟩, ⟨hAO.1, ?_, hAO.2.2⟩, hlen, fun x => hw x⟩
    exact hAO.2.1

theorem graphFun_empty (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u w, G.Adj u w ∧ x u = true ∧ x w = true := by
  simp [graphFun]

/-- The correctness test: a program below `F` that accepts every edge (of a graph with an edge) gives an
`IsAO2` circuit computing `F`. -/
theorem fold_computes (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (P : Prog n ι) (rank : ι → ℕ)
    (v : ι → (Fin n → Bool) → Bool) (K : Finset ι) (hcl : Closed P rank K) (hv : Sol P K v) (o : Src n ι)
    (ho : ∀ j, o = some (Sum.inr j) → j ∈ K) (hne : ∃ u w, G.Adj u w)
    (hle : ∀ x : Fin n → Bool, srcAt x (fun j => v j x) o = true → graphFun G ∅ x = true)
    (hedge : ∀ u w, G.Adj u w →
      srcAt (PEqualNP.EdgeOwnership.pairInput u w) (fun j => v j (PEqualNP.EdgeOwnership.pairInput u w)) o = true) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ (kept P v K).card ∧ circuitFun n D = graphFun G ∅ := by
  have hmono : ∀ x y : Fin n → Bool, (∀ a, x a = true → y a = true) →
      srcAt x (fun j => v j x) o = true → srcAt y (fun j => v j y) o = true := by
    intro x y hxy
    rcases o with _ | (c | j)
    · exact fun h => h
    · exact hxy c
    · exact sol_mono P rank K hcl v hv x y hxy j (ho j rfl)
  have h1 : srcAt (fun _ => true) (fun j => v j fun _ => true) o = true := by
    obtain ⟨u, w, h⟩ := hne
    exact hmono _ _ (fun _ _ => rfl) (hedge u w h)
  obtain ⟨D, hD, hs, hf⟩ := fold_prog P rank v K hcl hv o ho h1
  refine ⟨D, hD, hs, funext fun x => ?_⟩
  rw [hf x]
  apply Bool.eq_iff_iff.2
  refine ⟨hle x, fun h => ?_⟩
  obtain ⟨u, w, huw, hu, hw⟩ := (graphFun_empty G x).1 h
  refine hmono _ x ?_ (hedge u w huw)
  intro a ha
  simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at ha
  rcases ha with rfl | rfl
  · exact hu
  · exact hw

end PEqualNP.MetaComplexity.FoldProg
