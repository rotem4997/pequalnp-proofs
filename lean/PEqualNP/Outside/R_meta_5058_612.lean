import Mathlib
import PEqualNP.Defs

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

-- The cyclic plane has one orbit of vertices and one orbit of nonincident
-- point-line pairs. Relabeling bare inputs leaves gate indices untouched,
-- including every gate counted at either of the distinguished inputs.
-- Fix the inputs in T to true and inline each AND whose side becomes true.
-- The residual bounds involve ordinary AND counts only. With at most twenty
-- gates, the 42 distinct input neighborhoods force a repeated reader. The
-- one-point bound then leaves only size eighteen with read degree at most two.
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_5058_612
    (symmetry : let G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b : Fin 42 =>
      a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
      (∀ u : Fin 42, ∃ e : G ≃g G, e u = 0) ∧
      (∀ u v : Fin 42, u.val < 21 → 21 ≤ v.val → ¬ G.Adj u v →
        ∃ e : G ≃g G, e u = 0 ∧ e v = 22))
    (cofactor : ∀ (n : ℕ) (C : AndCountCircuit n) (T : Finset (Fin n)), C.eval T = false →
      ∃ D : AndCountCircuit n, D.WellFormed ∧
        D.size + {i : Fin C.size | ∃ v ∈ T, v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard ≤ C.size ∧
        ∀ U, D.eval U = C.eval (T ∪ U))
    (readTwo : let G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b : Fin 42 =>
      a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
      ∀ C : AndCountCircuit 42, C.WellFormed → C.Computes G → C.outVars = ∅ →
      (∀ (i : Fin C.size) (v : Fin 42), C.gateVal {v} i = false) →
      (∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i)) → C.size = 18 → (∀ v : Fin 42, {i : Fin C.size | v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard ≤ 2) → False)
    (residual : let G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b : Fin 42 =>
      a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
      ∀ (T : Finset (Fin 42)), T = {0} ∨ T = {0,22} →
      ∀ D : AndCountCircuit 42, D.WellFormed →
        (∀ U : Finset (Fin 42), D.eval U = true ↔
          ∃ p ∈ T ∪ U, ∃ q ∈ T ∪ U, G.Adj p q) →
        (if T = {0} then 16 else 14) ≤ D.size) :
    have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x2.WellFormed → x2.Computes x1 → x2.outVars = ∅ → (∀ (x6 : Fin x2.size) (x7 : Fin (42 : ℕ)), x2.gateVal {x7} x6 = Bool.false) → (∀ (x7 : Fin x2.size), Disjoint (x2.leftVars x7) (x2.rightVars x7)) → x2.size ≤ (20 : ℕ) → (19 : ℕ) ≤ x2.size ∧ (∀ (x9 : Fin (42 : ℕ)), {x10 : Fin x2.size | x9 ∈ x2.leftVars x10 ∨ x9 ∈ x2.rightVars x10}.ncard + (16 : ℕ) ≤ x2.size) ∧ ∀ (x9 x10 : Fin (42 : ℕ)), ↑x9 < (21 : ℕ) → (21 : ℕ) ≤ ↑x10 → ¬x1.Adj x9 x10 → {x14 : Fin x2.size | x9 ∈ x2.leftVars x14 ∨ x9 ∈ x2.rightVars x14 ∨ x10 ∈ x2.leftVars x14 ∨ x10 ∈ x2.rightVars x14}.ncard + (14 : ℕ) ≤ x2.size := by
  let G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b : Fin 42 =>
      a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
  let neighbor (a : Fin 42) : Fin 42 :=
    Fin.ofNat 42 (if a.val < 21 then 21 + a.val else a.val - 21)
  let nextNeighbor (a : Fin 42) : Fin 42 :=
    Fin.ofNat 42 (if a.val < 21 then 21 + (a.val+5)%21 else (a.val+16)%21)
  have separate : ∀ a b : Fin 42, a = b ∨
      (G.Adj a (neighbor a) ∧ ¬ G.Adj b (neighbor a)) ∨
      (G.Adj a (nextNeighbor a) ∧ ¬ G.Adj b (nextNeighbor a)) := by
    letI (a b : Fin 42) : Decidable (G.Adj a b) := by
      change Decidable ((SimpleGraph.fromRel _).Adj a b)
      rw [SimpleGraph.fromRel_adj]
      infer_instance
    decide
  have distinguish (a b : Fin 42) : a = b ∨ ∃ t, G.Adj a t ∧ ¬ G.Adj b t := by
    rcases separate a b with eq | h | h
    · exact Or.inl eq
    · exact Or.inr ⟨_,h⟩
    · exact Or.inr ⟨_,h⟩
  classical
  dsimp only
  intro C wf comp out sing sides bound
  have sideFormula {k : ℕ} (U B : Finset (Fin 42)) (F : Finset (Fin k)) (i : Fin k)
      (vals : Fin k → Bool) : sideTrue U B F i vals =
      decide ((∃ a ∈ B, a ∈ U) ∨ ∃ j ∈ F, j < i ∧ vals j = true) := rfl
  have fuelSucc (E : AndCountCircuit 42) (U : Finset (Fin 42)) (d : ℕ) (i : Fin E.size) :
      E.gateValFuel U (d+1) i =
        (sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U d) &&
         sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U d)) := rfl
  have evalFormula (E : AndCountCircuit 42) (U : Finset (Fin 42)) : E.eval U =
      decide ((∃ v ∈ E.outVars, v ∈ U) ∨ ∃ j ∈ E.outGates, E.gateVal U j = true) := rfl
  have distinct (v w : Fin 42)
      (identical : ∀ i, (v ∈ C.leftVars i ↔ w ∈ C.leftVars i) ∧
                          (v ∈ C.rightVars i ↔ w ∈ C.rightVars i)) : v = w := by
    rcases distinguish v w with eq | ⟨t,adj,non⟩
    · exact eq
    exfalso
    have touch (B : Finset (Fin 42)) (same : v ∈ B ↔ w ∈ B) :
        (∃ s ∈ B, s ∈ ({v,t} : Finset _)) ↔ (∃ s ∈ B, s ∈ ({w,t} : Finset _)) := by
      simpa only [Finset.mem_insert,Finset.mem_singleton,and_or_left,exists_or,exists_eq_right]
        using or_congr same (Iff.rfl (a := t ∈ B))
    have fuel (d : ℕ) (i : Fin C.size) :
        C.gateValFuel {v,t} d i = C.gateValFuel {w,t} d i := by
      induction d generalizing i with
      | zero => rfl
      | succ d ih =>
        simp only [fuelSucc,sideFormula,touch _ (identical i).1,touch _ (identical i).2,ih]
    have gates (i : Fin C.size) : C.gateVal {v,t} i = C.gateVal {w,t} i := fuel _ i
    have eval : C.eval {v,t} = C.eval {w,t} := by
      simp only [evalFormula,out,Finset.notMem_empty,false_and,exists_false,
        false_or,gates]
    have pair (s : Fin 42) : C.eval {s,t} = true ↔ G.Adj s t := by
      rw [comp]
      constructor
      · rintro ⟨a,ha,b,hb,h⟩
        simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
          first | exact h | exact h.symm | exact (G.loopless.irrefl _ h).elim
      · exact fun h => ⟨s,by simp,t,by simp,h⟩
    exact non ((pair w).mp (eval ▸ (pair v).mpr adj))
  have existsTwice (k : ℕ) (hk : k ≤ 20) (L R : Fin k → Finset (Fin 42))
      (dis : ∀ i, Disjoint (L i) (R i))
      (dist : ∀ v w : Fin 42, (∀ i, (v ∈ L i ↔ w ∈ L i) ∧ (v ∈ R i ↔ w ∈ R i)) → v=w) :
      ∃ v : Fin 42, 2 ≤ {i : Fin k | v ∈ L i ∨ v ∈ R i}.ncard := by
    classical
    by_contra! small
    have unique (v : Fin 42) (a b : Fin k) (ha : v ∈ L a ∨ v ∈ R a) (hb : v ∈ L b ∨ v ∈ R b) : a = b := by
      have few : {i : Fin k | v ∈ L i ∨ v ∈ R i}.ncard ≤ 1 := by have := small v; omega
      exact ((Set.ncard_le_one (s := {i : Fin k | v ∈ L i ∨ v ∈ R i}) (Set.toFinite _)).mp few) a ha b hb
    have represent (v : Fin 42) : ∃ c : Option (Fin k × Bool), ∀ i : Fin k,
        (v ∈ L i ↔ c = some (i,false)) ∧ (v ∈ R i ↔ c = some (i,true)) := by
      by_cases hv : ∃ i, v ∈ L i ∨ v ∈ R i
      · obtain ⟨j,hj⟩ := hv
        have noOther (i : Fin k) (ne : i ≠ j) : v ∉ L i ∧ v ∉ R i :=
          ⟨fun hl => ne (unique v i j (Or.inl hl) hj),fun hr => ne (unique v i j (Or.inr hr) hj)⟩
        rcases hj with left | right
        · refine ⟨some (j,false),?_⟩
          intro i
          by_cases eq : i=j
          · subst i
            simp [left,Finset.disjoint_left.mp (dis j) left]
          · simp [(noOther i eq).1,(noOther i eq).2,Ne.symm eq]
        · refine ⟨some (j,true),?_⟩
          intro i
          by_cases eq : i=j
          · subst i
            simp [right,Finset.disjoint_right.mp (dis j) right]
          · simp [(noOther i eq).1,(noOther i eq).2,Ne.symm eq]
      · refine ⟨none,?_⟩
        intro i
        exact ⟨iff_of_false (fun h => hv ⟨i,Or.inl h⟩) (by simp),
               iff_of_false (fun h => hv ⟨i,Or.inr h⟩) (by simp)⟩
    choose code codes using represent
    have inj : Function.Injective code := by
      intro v w same
      apply dist
      intro i
      have vx := codes v i
      rw [same] at vx
      exact ⟨vx.1.trans (codes w i).1.symm,vx.2.trans (codes w i).2.symm⟩
    have fin := Fintype.card_le_of_injective code inj
    simp only [Fintype.card_fin,Fintype.card_option,Fintype.card_prod,Fintype.card_bool] at fin
    omega
  have relabel (e : G ≃g G) :
      ∃ D : AndCountCircuit 42, ∃ sz : D.size = C.size,
        D.Computes G ∧
        (∀ (i : Fin C.size) (v : Fin 42),
           (e v ∈ D.leftVars (i.cast sz.symm) ↔ v ∈ C.leftVars i) ∧
           (e v ∈ D.rightVars (i.cast sz.symm) ↔ v ∈ C.rightVars i)) := by
    let f := e.toEquiv.toEmbedding
    let D : AndCountCircuit 42 := {
      size := C.size
      leftVars := fun i => (C.leftVars i).map f
      rightVars := fun i => (C.rightVars i).map f
      leftGates := C.leftGates
      rightGates := C.rightGates
      outVars := C.outVars.map f
      outGates := C.outGates }
    have mem (B : Finset (Fin 42)) (v : Fin 42) : e v ∈ B.map f ↔ v ∈ B :=
      Finset.mem_map' f
    have pre (U : Finset (Fin 42)) (v : Fin 42) :
        v ∈ U.map e.toEquiv.symm.toEmbedding ↔ e v ∈ U := by
      simp
    have bare (B U : Finset (Fin 42)) :
        (∃ x ∈ B.map f, x ∈ U) ↔ ∃ x ∈ B, x ∈ U.map e.toEquiv.symm.toEmbedding := by
      constructor
      · rintro ⟨x,hx,hU⟩
        obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hx
        exact ⟨v,hv,(pre U v).mpr hU⟩
      · rintro ⟨v,hv,hU⟩
        exact ⟨e v,(mem B v).mpr hv,(pre U v).mp hU⟩
    have fuel (U : Finset (Fin 42)) (d : ℕ) (i : Fin C.size) :
        D.gateValFuel U d i = C.gateValFuel (U.map e.toEquiv.symm.toEmbedding) d i := by
      induction d generalizing i with
      | zero => rfl
      | succ d ih =>
        simp only [fuelSucc,sideFormula]
        change (decide ((∃ x ∈ (C.leftVars i).map f, x ∈ U) ∨ _) &&
                decide ((∃ x ∈ (C.rightVars i).map f, x ∈ U) ∨ _)) = _
        simp only [bare,ih]
        rfl
    have val (U : Finset (Fin 42)) (i : Fin C.size) :
        D.gateVal U i = C.gateVal (U.map e.toEquiv.symm.toEmbedding) i := fuel U _ i
    have eval (U : Finset (Fin 42)) :
        D.eval U = C.eval (U.map e.toEquiv.symm.toEmbedding) := by
      unfold AndCountCircuit.eval
      change decide ((∃ x ∈ C.outVars.map f, x ∈ U) ∨ _) = _
      simp only [bare,val]
      rfl
    refine ⟨D,rfl,?_,fun i v => ⟨mem _ _,mem _ _⟩⟩
    · intro U
      rw [eval,comp]
      constructor
      · rintro ⟨v,hv,w,hw,h⟩
        exact ⟨e v,(pre U v).mp hv,e w,(pre U w).mp hw,e.map_adj_iff.mpr h⟩
      · rintro ⟨v,hv,w,hw,h⟩
        refine ⟨e.symm v,?_,e.symm w,?_,e.symm.map_adj_iff.mpr h⟩
        · exact Finset.mem_map_of_mem _ hv
        · exact Finset.mem_map_of_mem _ hw
  have residualCost (D : AndCountCircuit 42) (hd : D.Computes G)
      (T : Finset (Fin 42)) (allowed : T = {0} ∨ T = {0,22})
      (independent : ¬ ∃ a ∈ T, ∃ b ∈ T, G.Adj a b) :
      {i : Fin D.size | ∃ v ∈ T, v ∈ D.leftVars i ∨ v ∈ D.rightVars i}.ncard +
        (if T = {0} then 16 else 14) ≤ D.size := by
    have off : D.eval T = false := Bool.eq_false_iff.mpr (fun h => independent ((hd T).mp h))
    obtain ⟨E,hw,hsize,hE⟩ := cofactor 42 D T off
    have hmin := residual T allowed E hw (by intro U; rw [hE, hd])
    omega
  have vertex (D : AndCountCircuit 42) (hd : D.Computes G) :
      {i : Fin D.size | (0 : Fin 42) ∈ D.leftVars i ∨ (0 : Fin 42) ∈ D.rightVars i}.ncard + 16 ≤ D.size := by
    have cut := residualCost D hd {0} (Or.inl rfl) (by simp)
    simpa only [Finset.mem_singleton,
      exists_eq_left,ite_true] using cut
  have nonedge (D : AndCountCircuit 42) (hd : D.Computes G) :
      {i : Fin D.size | (0 : Fin 42) ∈ D.leftVars i ∨ (0 : Fin 42) ∈ D.rightVars i ∨
        (22 : Fin 42) ∈ D.leftVars i ∨ (22 : Fin 42) ∈ D.rightVars i}.ncard + 14 ≤ D.size := by
    have hn : ¬ G.Adj 0 22 := by decide +kernel
    have hn' : ¬ G.Adj 22 0 := fun h => hn h.symm
    have cut := residualCost D hd {0,22} (Or.inr rfl) (by simp [hn,hn'])
    have diff : ({0,22} : Finset (Fin 42)) ≠ {0} := by decide
    simpa only [Finset.mem_insert,
      Finset.mem_singleton,exists_prop,or_and_right,exists_or,exists_eq_left,
      ite_eq_right diff, or_assoc] using cut
  have allVertices (v : Fin 42) :
      {i : Fin C.size | v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard + 16 ≤ C.size := by
    obtain ⟨e,hev⟩ := symmetry.1 v
    obtain ⟨D,sz,compD,reader⟩ := relabel e
    have h := vertex D compD
    let eqi : Fin C.size ≃ Fin D.size := finCongr sz.symm
    have counts := Set.ncard_congr' (S := {i : Fin C.size | v ∈ C.leftVars i ∨ v ∈ C.rightVars i})
      (T := {i : Fin D.size | (0 : Fin 42) ∈ D.leftVars i ∨ (0 : Fin 42) ∈ D.rightVars i})
      (eqi.subtypeEquiv (by intro i; change _ ↔ ((_ ∈ _ ) ∨ (_ ∈ _)); rw [← hev]; exact or_congr (reader i v).1.symm (reader i v).2.symm))
    omega
  have allPairs (p l : Fin 42) (hp : p.val < 21) (hl : 21 ≤ l.val) (hn : ¬ G.Adj p l) :
      {i : Fin C.size | p ∈ C.leftVars i ∨ p ∈ C.rightVars i ∨ l ∈ C.leftVars i ∨ l ∈ C.rightVars i}.ncard + 14 ≤ C.size := by
    obtain ⟨e,ep,el⟩ := symmetry.2 p l hp hl hn
    obtain ⟨D,sz,compD,reader⟩ := relabel e
    have h := nonedge D compD
    let eqi : Fin C.size ≃ Fin D.size := finCongr sz.symm
    have counts := Set.ncard_congr' (S := {i : Fin C.size | p ∈ C.leftVars i ∨ p ∈ C.rightVars i ∨ l ∈ C.leftVars i ∨ l ∈ C.rightVars i})
      (T := {i : Fin D.size | (0 : Fin 42) ∈ D.leftVars i ∨ (0 : Fin 42) ∈ D.rightVars i ∨ (22 : Fin 42) ∈ D.leftVars i ∨ (22 : Fin 42) ∈ D.rightVars i})
      (eqi.subtypeEquiv (by intro i; change _ ↔ (_ ∨ _ ∨ _ ∨ _); rw [← ep,← el]; exact or_congr (reader i p).1.symm (or_congr (reader i p).2.symm (or_congr (reader i l).1.symm (reader i l).2.symm))))
    omega
  refine ⟨?_,allVertices,allPairs⟩
  obtain ⟨v,twice⟩ := existsTwice C.size bound C.leftVars C.rightVars sides distinct
  have cost := allVertices v
  by_contra! small
  have eq : C.size = 18 := by omega
  apply readTwo C wf comp out sing sides eq
  intro w
  have cap := allVertices w
  omega
