import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5494

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [5, 6]⟩, ⟨.or, [8, 7]⟩, ⟨.and, [0, 9]⟩,
    ⟨.or, [1, 2]⟩, ⟨.and, [11, 4]⟩, ⟨.or, [10, 12]⟩], 13⟩

lemma upper : RepSizeAtMost (fun u v : Fin 4 => (286 : ℕ).testBit (4 * u.val + v.val)) 6 := by
  refine ⟨witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def step (x : List Bool) (g : Gate) : List Bool :=
  x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]

lemma read_step (x : List Bool) (g : Gate) (i : ℕ) :
    (step x g).getD i false = if i = x.length then
      g.op.eval (g.inputs.map fun j => x.getD j false) else x.getD i false := by
  unfold step
  split_ifs with he
  · subst i
    rw [List.getD_append_right _ _ _ _ le_rfl]
    simp
  · by_cases h : i < x.length
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma gate_mono (x y : List Bool) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (h : ∀ j ∈ g.inputs, x.getD j false ≤ y.getD j false) :
    g.op.eval (g.inputs.map fun i => x.getD i false) ≤
      g.op.eval (g.inputs.map fun i => y.getD i false) := by
  rcases (show g.op = .and ∨ g.op = .or from hg) with hop | hop
  · rw [hop]
    simp only [GateOp.eval, Bool.le_iff_imp, List.all_eq_true, List.forall_mem_map, id_eq] at *
    intro hx i hi
    exact (Bool.le_iff_imp.mp (h i hi)) (hx i hi)
  · rw [hop]
    simp only [GateOp.eval, Bool.le_iff_imp, List.any_eq_true, List.mem_map, id_eq] at *
    rintro ⟨_, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨_, ⟨i, hi, rfl⟩, Bool.le_iff_imp.mp (h i hi) hx⟩

lemma cone (gs : List Gate) (n out : ℕ)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∃ S : Finset ℕ, S.card ≤ gs.length + 1 ∧ ∀ x y : List Bool,
      x.length = n → y.length = n →
      (∀ i ∈ S, x.getD i false ≤ y.getD i false) →
      (gs.foldl step x).getD out false ≤ (gs.foldl step y).getD out false := by
  induction gs generalizing n with
  | nil =>
    exact ⟨{out}, by simp, fun x y _ _ h => h out (by simp)⟩
  | cons g gs ih =>
    obtain ⟨S, hc, hS⟩ := ih (n+1) (fun j hj => hg j (List.mem_cons_of_mem _ hj))
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    let T := if n ∈ S then S.erase n ∪ g.inputs.toFinset else S
    refine ⟨T, ?_, ?_⟩
    · dsimp [T]
      split_ifs with hn
      · have h₁ := Finset.card_union_le (S.erase n) g.inputs.toFinset
        have h₂ := Finset.card_erase_of_mem hn
        have h₃ := g.inputs.toFinset_card_le
        have h₄ := Finset.card_pos.mpr ⟨n, hn⟩
        omega
      · omega
    · intro x y hx hy h
      apply hS (step x g) (step y g) (by simp [step, hx]) (by simp [step, hy])
      intro i hi
      rw [read_step, read_step, hx, hy]
      split_ifs with he
      · subst i
        exact gate_mono x y g hop (fun j hj => h j (by simp [T, hi, hj]))
      · apply h
        by_cases hn : n ∈ S <;> simp [T, hn, hi, he]

lemma separation : ∀ i : Fin 8, i.val ≠ 3 → ∃ u v a b : Fin 4,
    (286 : ℕ).testBit (4*u.val+v.val) = true ∧
    (286 : ℕ).testBit (4*a.val+b.val) = false ∧
    ∀ j : Fin 8, j ≠ i → (oneEach u v).getD j.val false ≤ (oneEach a b).getD j.val false := by
  decide

lemma lower : ¬ RepSizeAtMost (fun u v : Fin 4 => (286 : ℕ).testBit (4*u.val+v.val)) 5 := by
  rintro ⟨C, hm, hs, hr⟩
  obtain ⟨S, hc, hS⟩ := cone C.gates 8 C.output hm
  let needed : Finset ℕ := {0,1,2,4,5,6,7}
  have hsub : needed ⊆ S := by
    intro i hi
    have hi8 : i < 8 := by simp [needed] at hi; omega
    have hi3 : i ≠ 3 := by simp [needed] at hi; omega
    by_contra hmiss
    obtain ⟨u,v,a,b,hu,ha,hj⟩ := separation ⟨i,hi8⟩ hi3
    have leval := hS (oneEach u v) (oneEach a b) (by simp [oneEach]) (by simp [oneEach]) (by
      intro j hjs
      have hne : j ≠ i := by rintro rfl; exact hmiss hjs
      by_cases h8 : j < 8
      · exact hj ⟨j,h8⟩ (fun h => hne (congrArg Fin.val h))
      · rw [List.getD_eq_default _ _ (by simp [oneEach]; omega)]
        exact Bool.false_le _)
    change C.eval (oneEach u v) ≤ C.eval (oneEach a b) at leval
    rw [hr, hr] at leval
    change (286 : ℕ).testBit (4*u.val+v.val) ≤ (286 : ℕ).testBit (4*a.val+b.val) at leval
    rw [hu, ha] at leval
    contradiction
  have hcard : needed.card = 7 := by decide
  have := Finset.card_le_card hsub
  change C.gates.length ≤ 5 at hs
  omega

end PEqualNP.Outside.L_meta_5494


theorem PEqualNP.Outside.L_meta_5494 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (286 : ℕ).testBit (4 * u.val + v.val)) 6 ∧
    ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (286 : ℕ).testBit (4 * u.val + v.val)) 5 :=
  ⟨PEqualNP.Outside.L_meta_5494.upper, PEqualNP.Outside.L_meta_5494.lower⟩
