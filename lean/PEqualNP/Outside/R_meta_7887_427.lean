import Mathlib
import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadTwo

theorem PEqualNP.Outside.R_meta_7887_427
    (many :
      let G := edgeGraph 11 (([9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97]: List ℕ).map (fun k => (k/11,k%11)))
      ∀ C : Circuit, IsLeastAO G C → TopForm.TopForm G C → 2 ≤ (junk G C).card → C.size ≤ 21 →
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < 2 * (Ustar G C).card →
        let R := fun (v : Fin 11) => (Finset.range C.size).filter fun j => (v : ℕ) ∈ (gateAt C j).inputs
        let B := fun (v : Fin 11) (j : ℕ) => ∃ k < 11 + j, ∀ x : Fin 11 → Bool, x v = false → wval C x (11+j) = wval C x k
        (∀ v : Fin 11, v.val < 4 → (R v).card = 2 ∧ ∀ j ∈ R v, (gateAt C j).op ≠ GateOp.and) →
        ∃ v : Fin 11, v.val < 4 ∧ ∃ j ∉ R v, j < C.size ∧ B v j)
    (few :
      let G := edgeGraph 11 (([9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97]: List ℕ).map (fun k => (k/11,k%11)))
      ∀ C : Circuit, IsLeastAO G C → TopForm.TopForm G C → 2 ≤ (junk G C).card → C.size ≤ 21 →
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < 2 * (Ustar G C).card →
        let R := fun (v : Fin 11) => (Finset.range C.size).filter fun j => (v : ℕ) ∈ (gateAt C j).inputs
        let B := fun (v : Fin 11) (j : ℕ) => ∃ k < 11 + j, ∀ x : Fin 11 → Bool, x v = false → wval C x (11+j) = wval C x k
        (∀ v : Fin 11, v.val < 4 → (R v).card ≤ 2 ∧ ∀ j ∈ R v, (gateAt C j).op = GateOp.and → (R v).card ≤ 1) →
        (∃ v : Fin 11, v.val < 4 ∧ (R v).card ≤ 1) →
        ∃ v : Fin 11, v.val < 4 ∧ ∃ K : Finset ℕ, Disjoint (R v) K ∧
          3 ≤ (R v).card + K.card ∧ ∀ j ∈ K, j < C.size ∧ B v j) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →         x2.size ≤ (21 : ℕ) →           (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →             (∀ (x8 : Fin (11 : ℕ)),                 ↑x8 < (4 : ℕ) →                   ¬have x10 : ℕ → Prop := fun (x10 : ℕ) => x10 < x2.size ∧ ↑x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).inputs;                     (∃ (x11 : ℕ) (x12 : ℕ) (x13 : ℕ), x11 < x12 ∧ x12 < x13 ∧ x10 x11 ∧ x10 x12 ∧ x10 x13) ∨ ∃ (x11 : ℕ) (x12 : ℕ), x11 ≠ x12 ∧ x10 x11 ∧ x10 x12 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and) →               ∃ (x9 : Fin (11 : ℕ)),                 ↑x9 < (4 : ℕ) ∧                   have x10 : ℕ → Prop := fun (x10 : ℕ) => ∃ x11 < (11 : ℕ) + x10, ∀ (x12 : Fin (11 : ℕ) → Bool), x12 x9 = Bool.false → PEqualNP.ReadTwo.wval x2 x12 ((11 : ℕ) + x10) = PEqualNP.ReadTwo.wval x2 x12 x11;                   ∃ (x11 : ℕ) (x12 : ℕ) (x13 : ℕ), x11 < x12 ∧ x12 < x13 ∧ x13 < x2.size ∧ x10 x11 ∧ x10 x12 ∧ x10 x13) := by
  classical
  let G := edgeGraph 11 (([9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97]: List ℕ).map (fun k => (k/11,k%11)))
  intro G0 C least top hj hs he hr
  let R := fun (v : Fin 11) => (Finset.range C.size).filter fun j => (v : ℕ) ∈ (gateAt C j).inputs
  let B := fun (v : Fin 11) (j : ℕ) => ∃ k < 11 + j, ∀ x : Fin 11 → Bool, x v = false → wval C x (11+j) = wval C x k
  have members (v : Fin 11) (j : ℕ) : j ∈ R v ↔ j < C.size ∧ v.val ∈ (gateAt C j).inputs := by simp [R]
  have three (K : Finset ℕ) (hk : 3 ≤ K.card) : ∃ a b c, a < b ∧ b < c ∧ a ∈ K ∧ b ∈ K ∧ c ∈ K := by
    let e := K.orderEmbOfFin rfl
    let a : Fin K.card := ⟨0, by omega⟩
    let b : Fin K.card := ⟨1, by omega⟩
    let c : Fin K.card := ⟨2, by omega⟩
    exact ⟨e a, e b, e c, e.strictMono (show a < b by change 0 < 1; decide), e.strictMono (show b < c by change 1 < 2; decide),
      K.orderEmbOfFin_mem rfl a, K.orderEmbOfFin_mem rfl b, K.orderEmbOfFin_mem rfl c⟩
  have hrange (v : Fin 11) (hv : v.val < 4) : (R v).card ≤ 2 ∧
      ∀ j ∈ R v, (gateAt C j).op = GateOp.and → (R v).card ≤ 1 := by
    constructor
    · by_contra! hn
      obtain ⟨a,b,c,hab,hbc,ha,hb,hc⟩ := three _ hn
      exact hr v hv (.inl ⟨a,b,c,hab,hbc,(members _ _).1 ha,(members _ _).1 hb,(members _ _).1 hc⟩)
    · intro j hj hop
      by_contra! hn
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hn
      obtain ⟨k, hk, hne⟩ : ∃ k ∈ R v, j ≠ k := by
        by_cases h : j = a
        · exact ⟨b,hb,h ▸ hab⟩
        · exact ⟨a,ha,h⟩
      exact hr v hv (.inr ⟨j,k,hne,(members _ _).1 hj,(members _ _).1 hk,hop⟩)
  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_length (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [stepWire]
      omega

  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp [stepWire]
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key

  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    delta PEqualNP.MetaComplexity.NestedCover.gateAt
    simp [List.getD_eq_getElem?_getD, hj]

  have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
      val C x u = x.getD u false := by
    dsimp only [val]; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

  have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj

  have wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
      wval C x i.val = x i := by
    change val C (List.ofFn x) i.val = x i
    rw [val_input List.length_ofFn i.isLt]
    simp [List.getD_eq_getElem?_getD]

  have wval_gate {n : ℕ} {C : Circuit} (h : ReadsBack n C)
      (x : Fin n → Bool) {g : ℕ} (hg : g < C.size) :
      wval C x (n + g) = (gateAt C g).op.eval ((gateAt C g).inputs.map (wval C x)) := by
    change val C (List.ofFn x) (n + g) = _
    rw [val_gate List.length_ofFn hg]
    congr 1
    apply List.map_congr_left
    intro u hu
    exact ite_eq_left (h g hg u hu)


  have and2 : ∀ a b : Bool, GateOp.and.eval [a,b] = (a && b) := by decide
  have or2 : ∀ a b : Bool, GateOp.or.eval [a,b] = (a || b) := by decide
  have direct (v : Fin 11) (j : ℕ) (hj : j ∈ R v) : B v j := by
    obtain ⟨hin, hread⟩ := (members _ _).1 hj
    have hao : IsAO2 11 C := least.1
    obtain ⟨a,b,ab⟩ := List.length_eq_two.mp (hao.2.2 _ (gateAt_mem hin))
    have uv : v.val = a ∨ v.val = b := by simpa [ab] using hread
    rcases hao.1 _ (gateAt_mem hin) with hand | hor
    · refine ⟨v.val, by have := v.isLt; omega, ?_⟩
      intro x hx
      rw [wval_gate hao.2.1 x hin, hand, ab, wval_input, hx]
      rcases uv with rfl | rfl <;> simp [and2, or2, wval_input, hx]
    · rcases uv with rfl | rfl
      · refine ⟨b, hao.2.1 j hin b (by simp [ab]), ?_⟩
        intro x hx
        rw [wval_gate hao.2.1 x hin, hor, ab]
        simp [and2, or2, wval_input, hx]
      · refine ⟨a, hao.2.1 j hin a (by simp [ab]), ?_⟩
        intro x hx
        rw [wval_gate hao.2.1 x hin, hor, ab]
        simp [and2, or2, wval_input, hx]
  have cert : ∃ v : Fin 11, v.val < 4 ∧ ∃ K : Finset ℕ,
      Disjoint (R v) K ∧ 3 ≤ (R v).card + K.card ∧ ∀ j ∈ K, j < C.size ∧ B v j := by
    by_cases sparse : ∃ v : Fin 11, v.val < 4 ∧ (R v).card ≤ 1
    · exact few C least top hj hs he hrange sparse
    · have twice (v : Fin 11) (hv : v.val < 4) : (R v).card = 2 ∧ ∀ j ∈ R v, (gateAt C j).op ≠ GateOp.and := by
        obtain ⟨hm,ha⟩ := hrange v hv
        have hn : ¬(R v).card ≤ 1 := fun h => sparse ⟨v,hv,h⟩
        exact ⟨by omega,fun j hj hand => hn (ha j hj hand)⟩
      obtain ⟨v,hv,j,hn,hj,hb⟩ := many C least top hj hs he twice
      exact ⟨v,hv,{j},Finset.disjoint_singleton_right.mpr hn, by simp [(twice v hv).1],
        fun k hk => by simpa [Finset.mem_singleton.mp hk] using And.intro hj hb⟩
  obtain ⟨v,hv,K,hdis,hcard,hK⟩ := cert
  have h3 : 3 ≤ (R v ∪ K).card := by rwa [Finset.card_union_of_disjoint hdis]
  obtain ⟨a,b,c,hab,hbc,ha,hb,hc⟩ := three _ h3
  have good (j : ℕ) (hj : j ∈ R v ∪ K) : j < C.size ∧ B v j := by
    rcases Finset.mem_union.mp hj with h | h
    · exact ⟨((members _ _).1 h).1, direct v j h⟩
    · exact hK j h
  exact ⟨v,hv,a,b,c,hab,hbc,(good _ hc).1,(good _ ha).2,(good _ hb).2,(good _ hc).2⟩
