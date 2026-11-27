import Mathlib.Data.Finset.Card
import Mathlib.Order.Minimal
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- False certificates combine by family union at AND and by pairwise set union at OR.
-- The two output wires must collectively generate each required minimal vertex cover.
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_4221_719
    (compile : ∀ (N : ℕ), let avail := fun (S : List (Set (Finset (Fin N)))) =>
        (∅ : Set (Finset (Fin N))) :: ({∅} : Set (Finset (Fin N))) ::
        (List.ofFn (fun i : Fin N => ({ {i} } : Set (Finset (Fin N)))) ++ S)
      let prog := fun (S : List (Set (Finset (Fin N)))) => ∀ j : Fin S.length,
        ∃ a ∈ avail (S.take j.val), ∃ b ∈ avail (S.take j.val),
          S.get j = a ∪ b ∨ S.get j = {u | ∃ x ∈ a, ∃ y ∈ b, u = x ∪ y}
      ∀ (C : Circuit) (ws : List ℕ), Monotone2 C → ws.length ≤ 2 →
      ∃ S : List (Set (Finset (Fin N))), S.length ≤ C.size ∧ prog S ∧
        ∃ F ∈ avail S, ∃ G ∈ avail S, ∀ x : Fin N → Bool,
          GateOp.and.eval (ws.map (fun i => (C.wires (List.ofFn x)).getD i false)) = false ↔
            ∃ z ∈ F ∪ G, ∀ i ∈ z, x i = false)
    (covers : let I := fun (p l : Fin 13) => (p.val + l.val) % 13 ∈ [0,1,3,9]
      let left := fun (p : Fin 13) => Fin.castAdd 13 p
      let right := fun (l : Fin 13) => Fin.natAdd 13 l
      let missing := fun (f : Fin 13 → Fin 26) (z : Finset (Fin 26)) =>
        (Finset.univ.filter (fun i => f i ∉ z) : Finset (Fin 13))
      let cover := fun (z : Finset (Fin 26)) => ∀ p l, I p l → left p ∈ z ∨ right l ∈ z
      let avoid := fun (U : Finset (Fin 13)) => Finset.univ.filter (fun l => ∀ p ∈ U, ¬I p l)
      ∀ H : Set (Finset (Fin 26)),
      let rejects := fun (P L : Finset (Fin 13)) => ∃ z ∈ H,
        (∀ p ∈ P, left p ∉ z) ∧ (∀ l ∈ L, right l ∉ z)
      (∀ p l, I p l → ¬rejects {p} {l}) →
      (∀ U, U.card ≤ 3 → rejects U (avoid U) ∧ rejects (avoid U) U) → (∀ z ∈ H, cover z) ∧ ∀ z : Finset (Fin 26), Minimal cover z →
        ((missing left z).card ≤ 3 ∨
         (missing right z).card ≤ 3) → z ∈ H)
    (plane : let I := fun (p l : Fin 13) => (p.val + l.val) % 13 ∈ [0,1,3,9]
      let left := fun (p : Fin 13) => Fin.castAdd 13 p
      let right := fun (l : Fin 13) => Fin.natAdd 13 l
      let missing := fun (f : Fin 13 → Fin 26) (z : Finset (Fin 26)) =>
        (Finset.univ.filter (fun i => f i ∉ z) : Finset (Fin 13))
      let cover := fun (z : Finset (Fin 26)) => ∀ p l, I p l → left p ∈ z ∨ right l ∈ z

      ∀ z : Finset (Fin 26), cover z → ((missing left z).card ≤ 3 ∨
         (missing right z).card ≤ 3))
    (count : let avail := fun (S : List (Set (Finset (Fin 26)))) =>
        (∅ : Set (Finset (Fin 26))) :: ({∅} : Set (Finset (Fin 26))) ::
        (List.ofFn (fun i : Fin 26 => ({ {i} } : Set (Finset (Fin 26)))) ++ S)
      let prog := fun (S : List (Set (Finset (Fin 26)))) => ∀ j : Fin S.length,
        ∃ a ∈ avail (S.take j.val), ∃ b ∈ avail (S.take j.val),
          S.get j = a ∪ b ∨ S.get j = {u | ∃ x ∈ a, ∃ y ∈ b, u = x ∪ y}
      let I := fun (p l : Fin 13) => (p.val + l.val) % 13 ∈ [0,1,3,9]
      let left := fun (p : Fin 13) => Fin.castAdd 13 p
      let right := fun (l : Fin 13) => Fin.natAdd 13 l
      let cover := fun (z : Finset (Fin 26)) => ∀ p l, I p l → left p ∈ z ∨ right l ∈ z
      ∀ S : List (Set (Finset (Fin 26))), prog S →
        ∀ F ∈ avail S, ∀ G ∈ avail S, let H := F ∪ G
        ((∀ z ∈ H, cover z) ∧ ∀ z : Finset (Fin 26), Minimal cover z →
        z ∈ H) → 63 ≤ S.length) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2.length ≤ (2 : ℕ) →       (∃ x5 ∈ x2, (26 : ℕ) ≤ x5) →         (let x6 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x6 x7 : Fin (13 : ℕ)) => (↑x6 + ↑x7) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];           have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x7 x8 : Finset (Fin (13 : ℕ))) (x9 : Fin (26 : ℕ)) => if ↑x9 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x9 ∈ x7) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x9 ∈ x8);           have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x8 : Finset (Fin (13 : ℕ))) => {x9 : Fin (13 : ℕ) | ∀ x10 ∈ x8, ¬x6 x10 x9};           have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x11 : ℕ) => (x1.wires (List.ofFn (x7 x9 x10))).getD x11 Bool.false) x2);           (∀ (x10 x11 : Fin (13 : ℕ)), x6 x10 x11 → x9 {x10} {x11} = Bool.true) ∧ ∀ (x10 : Finset (Fin (13 : ℕ))), x10.card ≤ (3 : ℕ) → x9 x10 (x8 x10) = Bool.false ∧ x9 (x8 x10) x10 = Bool.false) →           (63 : ℕ) ≤ x1.size := by
  classical
  intro C ws mono arity _ tested
  let I := fun (p l : Fin 13) => (p.val+l.val)%13 ∈ [0,1,3,9]
  let avoid := fun (U : Finset (Fin 13)) => Finset.univ.filter (fun l => ∀ p ∈ U, ¬ I p l)
  let row := fun (P L : Finset (Fin 13)) (i : Fin 26) =>
    if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ P) else decide (Fin.ofNat 13 i.val ∈ L)
  let out := fun (P L : Finset (Fin 13)) => GateOp.and.eval
    (ws.map fun i => (C.wires (List.ofFn (row P L))).getD i false)
  change (∀ p l, I p l → out {p} {l} = true) ∧
    (∀ U, U.card ≤ 3 → out U (avoid U) = false ∧ out (avoid U) U = false) at tested
  obtain ⟨S,len,prog,F,hF,G,hG,sem⟩ := compile 26 C ws mono arity
  have atL (P L) (p : Fin 13) : row P L (Fin.castAdd 13 p) = decide (p ∈ P) := by
    have eq : Fin.ofNat 13 p.val = p := Fin.ext (Nat.mod_eq_of_lt p.isLt)
    simpa only [row,Fin.coe_castAdd,p.isLt,if_true,eq]
  have atR (P L) (l : Fin 13) : row P L (Fin.natAdd 13 l) = decide (l ∈ L) := by
    have eq : Fin.ofNat 13 (13+l.val) = l := by apply Fin.ext; simp [Fin.ofNat,Nat.mod_eq_of_lt l.isLt]
    have big : ¬13 + l.val < 13 := by omega
    simp only [row,Fin.coe_natAdd,big,if_false,eq]
  have bridge (P L) : out P L = false ↔ ∃ z ∈ F ∪ G,
      (∀ p ∈ P, Fin.castAdd 13 p ∉ z) ∧ (∀ l ∈ L, Fin.natAdd 13 l ∉ z) := by
    rw [show (out P L = false) ↔ _ from sem (row P L)]
    constructor
    · rintro ⟨z,hz,off⟩
      refine ⟨z,hz,?_,?_⟩
      · intro p hp hm
        simpa [atL,hp] using off _ hm
      · intro l hl hm
        have h := off _ hm
        rw [atR,decide_eq_true hl] at h
        exact Bool.noConfusion h
    · rintro ⟨z,hz,pa,li⟩
      refine ⟨z,hz,?_⟩
      intro i
      refine Fin.addCases (m := 13) (n := 13) (motive := fun i => i ∈ z → row P L i = false) ?_ ?_ i
      · intro p hp
        rw [atL]
        exact decide_eq_false (fun h => pa p h hp)
      · intro l hl
        rw [atR]
        exact decide_eq_false (fun h => li l h hl)
  have pos (p l) (edge : I p l) : ¬ ∃ z ∈ F ∪ G,
      (∀ i ∈ ({p} : Finset _), Fin.castAdd 13 i ∉ z) ∧ (∀ i ∈ ({l} : Finset _), Fin.natAdd 13 i ∉ z) := by
    intro h
    have bad := (bridge {p} {l}).mpr h
    rw [tested.1 p l edge] at bad
    exact Bool.noConfusion bad
  obtain ⟨sound,needed⟩ := covers (F ∪ G) pos (fun U hu =>
    ⟨(bridge _ _).mp (tested.2 U hu).1,(bridge _ _).mp (tested.2 U hu).2⟩)
  exact (count S prog F hF G hG ⟨sound,fun z hz => needed z hz (plane z hz.prop)⟩).trans len
