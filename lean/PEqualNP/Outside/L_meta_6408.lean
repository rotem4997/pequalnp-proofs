import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6408

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev FF : Type := Fin 40 × Fin 13 → Bool

def ev (l : List FF) (p : Fin 40 × Fin 13) : Bool := l.all fun f => f p

def cF : FF := fun _ => false

def isOr (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem isOr_iff (g : Gate) : isOr g = true ↔ g.op = GateOp.or := by
  unfold isOr
  cases g.op <;> simp

theorem card_fin (l : List Gate) [DecidablePred fun g : Gate => g.op = GateOp.or] :
    (Finset.univ.filter fun i : Fin l.length => (l.get i).op = GateOp.or).card = l.countP isOr := by
  induction l with
  | nil => simp
  | cons g l ih =>
    have h := Fin.card_filter_univ_succ (fun i : Fin (l.length + 1) => ((g :: l).get i).op = GateOp.or)
    have h2 : (Finset.univ.filter fun i : Fin (g :: l).length => ((g :: l).get i).op = GateOp.or).card =
        (Finset.univ.filter fun i : Fin (l.length + 1) => ((g :: l).get i).op = GateOp.or).card := rfl
    rw [h2, h, List.countP_cons]
    have h3 : (Finset.univ.filter fun x : Fin l.length => ((g :: l).get x.succ).op = GateOp.or).card =
        l.countP isOr := ih
    rw [h3]
    by_cases hg : g.op = GateOp.or
    · have : isOr g = true := (isOr_iff g).mpr hg
      simp [hg, this]
    · have : isOr g = false := by
        rw [Bool.eq_false_iff]
        exact fun h => hg ((isOr_iff g).mp h)
      simp [hg, this]

theorem card_eq (l : List Gate) :
    {i : Fin l.length | (l.get i).op = GateOp.or}.ncard = l.countP isOr := by
  classical
  have hs : {i : Fin l.length | (l.get i).op = GateOp.or} =
      ↑(Finset.univ.filter fun i : Fin l.length => (l.get i).op = GateOp.or) := by
    ext i
    simp
  rw [hs, Set.ncard_coe_finset]
  exact card_fin l

theorem getD_map_ev (W : List (List FF)) (p : Fin 40 × Fin 13) (i : ℕ) :
    (W.map (fun l => ev l p)).getD i false = ev (W.getD i [cF]) p := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> simp [ev, cF]

theorem mem_getD (W : List (List FF)) (S : List FF) (hc : cF ∈ S)
    (hW : ∀ l ∈ W, ∀ f ∈ l, f ∈ S) (i : ℕ) : ∀ f ∈ W.getD i [cF], f ∈ S := by
  intro f hf
  rw [List.getD_eq_getElem?_getD] at hf
  cases hi : W[i]? with
  | none =>
    rw [hi] at hf
    simp at hf
    rw [hf]
    exact hc
  | some l =>
    rw [hi] at hf
    exact hW l (List.mem_of_getElem? hi) f hf

def Good (B Q : List FF) : Prop :=
  ∀ i (hi : i < Q.length), ∃ l1 l2 : List FF,
    (∀ f ∈ l1 ++ l2, f ∈ B ++ Q.take i) ∧ Q[i] = fun p => ev l1 p || ev l2 p

def Inv (x3 : List FF) (gs : List Gate) : Prop :=
  ∃ (Q : List FF) (W : List (List FF)), Good (cF :: x3) Q ∧ Q.length = gs.countP isOr ∧
    (∀ l ∈ W, ∀ f ∈ l, f ∈ (cF :: x3) ++ Q) ∧
    ∀ p, gs.foldl stp (x3.map fun f => f p) = W.map (fun l => ev l p)

theorem or_pick (W : List (List FF)) (S : List FF) (hc : cF ∈ S)
    (hW : ∀ l ∈ W, ∀ f ∈ l, f ∈ S) : ∀ (ins : List ℕ), ins.length ≤ 2 →
    ∃ l1 l2 : List FF, (∀ f ∈ l1 ++ l2, f ∈ S) ∧
      ∀ p, (ins.map fun i => ev (W.getD i [cF]) p).any id = (ev l1 p || ev l2 p) := by
  intro ins hlen
  match ins, hlen with
  | [], _ =>
    refine ⟨[cF], [cF], ?_, ?_⟩
    · intro f hf
      simp at hf
      rw [hf]
      exact hc
    · intro p
      simp [ev, cF]
  | [i], _ =>
    refine ⟨W.getD i [cF], W.getD i [cF], ?_, ?_⟩
    · intro f hf
      rcases List.mem_append.mp hf with h | h <;> exact mem_getD W S hc hW i f h
    · intro p
      simp
  | [i, j], _ =>
    refine ⟨W.getD i [cF], W.getD j [cF], ?_, ?_⟩
    · intro f hf
      rcases List.mem_append.mp hf with h | h
      · exact mem_getD W S hc hW i f h
      · exact mem_getD W S hc hW j f h
    · intro p
      simp
  | _ :: _ :: _ :: _, h3 =>
    simp at h3

theorem step_inv (x3 : List FF) (gs : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (h : Inv x3 gs) : Inv x3 (gs ++ [g]) := by
  obtain ⟨Q, W, hG, hQ, hW, hF⟩ := h
  have hc : cF ∈ (cF :: x3) ++ Q := by simp
  rcases hop with hop | hop
  · refine ⟨Q, W ++ [g.inputs.flatMap fun i => W.getD i [cF]], hG, ?_, ?_, ?_⟩
    · rw [List.countP_append, hQ]
      simp [isOr, hop]
    · intro l hl f hf
      rcases List.mem_append.mp hl with hl | hl
      · exact hW l hl f hf
      · simp only [List.mem_singleton] at hl
        subst hl
        obtain ⟨i, _, hfi⟩ := List.mem_flatMap.mp hf
        exact mem_getD W _ hc hW i f hfi
    · intro p
      rw [List.foldl_append, hF p]
      simp only [List.foldl_cons, List.foldl_nil, stp, List.map_append, List.map_cons,
        List.map_nil, hop, GateOp.eval, getD_map_ev]
      simp [ev, List.all_flatMap, List.all_map]
  · obtain ⟨l1, l2, hl, hval⟩ := or_pick W _ hc hW g.inputs hlen
    refine ⟨Q ++ [fun p => ev l1 p || ev l2 p], W ++ [[fun p => ev l1 p || ev l2 p]],
      ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [List.length_append, List.length_singleton] at hi
      by_cases hiQ : i < Q.length
      · obtain ⟨m1, m2, hm, he⟩ := hG i hiQ
        refine ⟨m1, m2, ?_, ?_⟩
        · rw [List.take_append_of_le_length (by omega)]
          exact hm
        · rw [List.getElem_append_left hiQ]
          exact he
      · have hiE : i = Q.length := by omega
        subst hiE
        refine ⟨l1, l2, ?_, ?_⟩
        · rw [List.take_append_of_le_length (le_refl _), List.take_length]
          exact hl
        · simp
    · rw [List.countP_append, List.length_append, hQ]
      simp [isOr, hop]
    · intro l hl2 f hf
      rcases List.mem_append.mp hl2 with hl2 | hl2
      · have h5 := hW l hl2 f hf
        simp only [List.mem_append] at h5 ⊢
        tauto
      · simp only [List.mem_singleton] at hl2
        subst hl2
        simp only [List.mem_singleton] at hf
        subst hf
        simp
    · intro p
      rw [List.foldl_append, hF p]
      simp only [List.foldl_cons, List.foldl_nil, stp, List.map_append, List.map_cons,
        List.map_nil, hop, GateOp.eval, getD_map_ev, hval]
      simp [ev]

theorem main (x3 : List FF) (x4 : Circuit) (hM : Monotone2 x4) :
    ∃ (x6 : List FF) (x7 : List FF),
      (∀ (x8 : Fin x6.length), ∃ (x9 : List FF) (x10 : List FF),
        (∀ x11 ∈ x9 ++ x10, x11 ∈ cF :: x3 ++ List.take (↑x8) x6) ∧
          x6.get x8 = fun x11 => ev x9 x11 || ev x10 x11) ∧
      x6.length = {x8 : Fin x4.gates.length | (x4.gates.get x8).op = GateOp.or}.ncard ∧
      (∀ x8 ∈ x7, x8 ∈ cF :: x3 ++ x6) ∧
      ∀ (x8 : Fin 40 × Fin 13), ev x7 x8 = x4.eval (List.map (fun (x9 : FF) => x9 x8) x3) := by
  have hinv : ∀ gs : List Gate, (∀ g ∈ gs, g ∈ x4.gates) → Inv x3 gs := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil =>
      intro _
      refine ⟨[], x3.map (fun f => [f]), ?_, rfl, ?_, ?_⟩
      · intro i hi
        simp at hi
      · intro l hl f hf
        simp only [List.mem_map] at hl
        obtain ⟨f2, hf2, rfl⟩ := hl
        simp only [List.mem_singleton] at hf
        subst hf
        simp [hf2]
      · intro p
        simp [ev]
    | append_singleton gs g ih =>
      intro hmem
      have hg := hM g (hmem g (by simp))
      have hop := hg.1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      exact step_inv x3 gs g hop hg.2 (ih (fun g2 hg2 => hmem g2 (by simp [hg2])))
  obtain ⟨Q, W, hG, hQ, hW, hF⟩ := hinv x4.gates (fun g hg => hg)
  have hc : cF ∈ (cF :: x3) ++ Q := by simp
  refine ⟨Q, W.getD x4.output [cF], ?_, ?_, ?_, ?_⟩
  · intro i
    exact hG i.1 i.2
  · rw [hQ, card_eq]
  · exact mem_getD W _ hc hW x4.output
  · intro p
    have h1 : x4.wires (x3.map fun f => f p) = W.map (fun l => ev l p) := hF p
    have h2 : x4.eval (x3.map fun f => f p) = (x4.wires (x3.map fun f => f p)).getD x4.output false := rfl
    rw [h2, h1, getD_map_ev]

end PEqualNP.Outside.L_meta_6408

theorem PEqualNP.Outside.L_meta_6408 : let x1 : Type := Fin (40 : ℕ) × Fin (13 : ℕ) → Bool; have x2 : List x1 → Fin (40 : ℕ) × Fin (13 : ℕ) → Bool := fun (x2 : List x1) (x3 : Fin (40 : ℕ) × Fin (13 : ℕ)) => x2.all fun (x4 : x1) => x4 x3; ∀ (x3 : List x1) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → ∃ (x6 : List x1) (x7 : List x1), (∀ (x8 : Fin x6.length), ∃ (x9 : List x1) (x10 : List x1), (∀ x11 ∈ x9 ++ x10, x11 ∈ (fun (x13 : Fin (40 : ℕ) × Fin (13 : ℕ)) => Bool.false) :: x3 ++ List.take (↑x8) x6) ∧ x6.get x8 = fun (x11 : Fin (40 : ℕ) × Fin (13 : ℕ)) => x2 x9 x11 || x2 x10 x11) ∧ x6.length = {x8 : Fin x4.gates.length | (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard ∧ (∀ x8 ∈ x7, x8 ∈ (fun (x10 : Fin (40 : ℕ) × Fin (13 : ℕ)) => Bool.false) :: x3 ++ x6) ∧ ∀ (x8 : Fin (40 : ℕ) × Fin (13 : ℕ)), x2 x7 x8 = x4.eval (List.map (fun (x9 : x1) => x9 x8) x3) := by
  intro x1 x2 x3 x4 hM
  exact PEqualNP.Outside.L_meta_6408.main x3 x4 hM
