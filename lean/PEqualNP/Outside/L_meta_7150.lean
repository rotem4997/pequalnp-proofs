import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7150

abbrev G : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x1 : ℕ) => (x1 / (16 : ℕ), x1 % (16 : ℕ))) [(9 : ℕ), (10 : ℕ), (20 : ℕ), (24 : ℕ), (37 : ℕ), (42 : ℕ), (54 : ℕ), (55 : ℕ), (72 : ℕ), (74 : ℕ), (88 : ℕ), (89 : ℕ), (103 : ℕ), (106 : ℕ), (121 : ℕ), (137 : ℕ)])

abbrev L : List (Fin 11 × Fin 11) :=
  [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10),
   (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

theorem hE : G.edgeFinset = (L.map (fun p => s(p.1, p.2))).toFinset := by
  ext e
  refine Sym2.ind (fun a b => ?_) e
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  revert a b
  decide

theorem hLnd : (L.map (fun p => s(p.1, p.2))).Nodup := by decide

theorem edge_card (S : Finset (Fin 11)) :
    (S.sym2 ∩ G.edgeFinset).card = L.countP (fun p => decide (p.1 ∈ S) && decide (p.2 ∈ S)) := by
  have hset : S.sym2 ∩ G.edgeFinset =
      ((L.filter (fun p => decide (p.1 ∈ S) && decide (p.2 ∈ S))).map
        (fun p => s(p.1, p.2))).toFinset := by
    rw [hE]
    ext e
    simp only [Finset.mem_inter, List.mem_toFinset, List.mem_map, List.mem_filter,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, p, hp, rfl⟩
      exact ⟨p, ⟨hp, Finset.mk_mem_sym2_iff.mp h1⟩, rfl⟩
    · rintro ⟨p, ⟨hp, h1⟩, rfl⟩
      exact ⟨Finset.mk_mem_sym2_iff.mpr h1, p, hp, rfl⟩
  rw [hset, List.toFinset_card_of_nodup (((List.filter_sublist).map _).nodup hLnd),
    List.length_map, List.countP_eq_length_filter]

theorem card_eq (S : Finset (Fin 11)) :
    S.card = (List.finRange 11).countP (fun i => decide (i ∈ S)) := by
  have h : S = ((List.finRange 11).filter (fun i => decide (i ∈ S))).toFinset := by
    ext i; simp
  rw [List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange 11).filter _), ← h]

abbrev Pr (f : Fin 11 → Bool) : Prop :=
  (List.finRange 11).countP f ≤ 4 + List.countP
    (fun (t : ℕ) => decide (t ≤ L.countP (fun p => f p.1 && f p.2))) [1, 2, 3, 5, 8, 12, 16]

set_option maxRecDepth 100000 in
theorem allB : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
    Pr ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10] := by
  decide

theorem key (f : Fin 11 → Bool) : Pr f := by
  have hf : f = ![f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10] := by
    funext i; fin_cases i <;> rfl
  rw [hf]
  exact allB _ _ _ _ _ _ _ _ _ _ _

theorem main (S : Finset (Fin 11)) :
    S.card ≤ (4 : ℕ) + List.countP (fun (x3 : ℕ) => Decidable.decide (x3 ≤ (S.sym2 ∩ G.edgeFinset).card))
      [(1 : ℕ), (2 : ℕ), (3 : ℕ), (5 : ℕ), (8 : ℕ), (12 : ℕ), (16 : ℕ)] := by
  rw [card_eq S, edge_card S]
  exact key (fun i => decide (i ∈ S))

end PEqualNP.Outside.L_meta_7150

theorem PEqualNP.Outside.L_meta_7150 : let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x1 : ℕ) => (x1 / (16 : ℕ), x1 % (16 : ℕ))) [(9 : ℕ), (10 : ℕ), (20 : ℕ), (24 : ℕ), (37 : ℕ), (42 : ℕ), (54 : ℕ), (55 : ℕ), (72 : ℕ), (74 : ℕ), (88 : ℕ), (89 : ℕ), (103 : ℕ), (106 : ℕ), (121 : ℕ), (137 : ℕ)]); ∀ (x2 : Finset (Fin (11 : ℕ))), x2.card ≤ (4 : ℕ) + List.countP (fun (x3 : ℕ) => Decidable.decide (x3 ≤ (x2.sym2 ∩ x1.edgeFinset).card)) [(1 : ℕ), (2 : ℕ), (3 : ℕ), (5 : ℕ), (8 : ℕ), (12 : ℕ), (16 : ℕ)] := by
  intro x1 S
  exact PEqualNP.Outside.L_meta_7150.main S
