import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_698

open PEqualNP.MetaComplexity

-- One evaluation step: the gate adds one wire.
def bstp (w : List Bool) (g : BinaryGate) : List Bool :=
  w ++ [g.op (w.getD g.left false) (w.getD g.right false)]

theorem wires_eq (C : BinaryCircuit) (x : List Bool) : C.wires x = C.gates.foldl bstp x := rfl

theorem foldl_length (gs : List BinaryGate) : ∀ W : List Bool,
    (gs.foldl bstp W).length = W.length + gs.length := by
  induction gs with
  | nil => intro W; simp
  | cons g gs ih =>
    intro W
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp [bstp]
    omega

theorem foldl_prefix (gs : List BinaryGate) : ∀ (W : List Bool) (i : ℕ), i < W.length →
    (gs.foldl bstp W).getD i false = W.getD i false := by
  induction gs with
  | nil => intro W i _; rfl
  | cons g gs ih =>
    intro W i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by simp [bstp]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem getD_ge (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem getD_snoc_eq (W : List Bool) (v : Bool) : (W ++ [v]).getD W.length false = v := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (h : i < m) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

theorem split_at {α : Type} : ∀ (l : List α) (j : ℕ) (g : α), l[j]? = some g →
    ∃ pre post : List α, l = pre ++ g :: post ∧ pre.length = j := by
  intro l
  induction l with
  | nil => intro j g h; simp at h
  | cons x xs ih =>
    intro j g h
    cases j with
    | zero =>
      simp at h
      exact ⟨[], xs, by simp [h], rfl⟩
    | succ j =>
      simp at h
      obtain ⟨pre, post, h1, h2⟩ := ih j g h
      exact ⟨x :: pre, post, by simp [h1], by simp [h2]⟩

-- The value of a gate whose two operands are earlier wires, read off the final wires.
theorem gval (gs : List BinaryGate) (W : List Bool) (j : ℕ) (G : BinaryGate)
    (hj : gs[j]? = some G) (hl : G.left < W.length + j) (hr : G.right < W.length + j) :
    (gs.foldl bstp W).getD (W.length + j) false
      = G.op ((gs.foldl bstp W).getD G.left false) ((gs.foldl bstp W).getD G.right false) := by
  obtain ⟨pre, post, h1, h2⟩ := split_at gs j G hj
  subst h1
  have hlen : (pre.foldl bstp W).length = W.length + j := by rw [foldl_length, h2]
  simp only [List.foldl_append, List.foldl_cons]
  have e : ∀ i, i < W.length + j →
      (post.foldl bstp (bstp (pre.foldl bstp W) G)).getD i false
        = (pre.foldl bstp W).getD i false := by
    intro i hi
    rw [foldl_prefix post _ i (by simp [bstp, hlen]; omega)]
    exact List.getD_append _ _ _ _ (by omega)
  rw [e _ hl, e _ hr, foldl_prefix post _ (W.length + j) (by simp [bstp, hlen])]
  rw [← hlen]
  exact getD_snoc_eq _ _

-- Two runs agree outside the set `B` of wires, when every gate outside `B` is one whose final
-- values are known to agree (`S`) or reads no wire of `B`.
theorem gen (B S : ℕ → Prop) : ∀ (gs : List BinaryGate) (W1 W2 : List Bool),
    W1.length = W2.length →
    (∀ i, i < W1.length → ¬ B i → W1.getD i false = W2.getD i false) →
    (∀ i, S i → (gs.foldl bstp W1).getD i false = (gs.foldl bstp W2).getD i false) →
    (∀ p G, gs[p]? = some G → B (W1.length + p) ∨ S (W1.length + p) ∨
      ((¬ B G.left ∨ W1.length + p ≤ G.left) ∧ (¬ B G.right ∨ W1.length + p ≤ G.right))) →
    ∀ i, ¬ B i → (gs.foldl bstp W1).getD i false = (gs.foldl bstp W2).getD i false := by
  intro gs
  induction gs with
  | nil =>
    intro W1 W2 hlen hag _ _ i hi
    by_cases h : i < W1.length
    · exact hag i h hi
    · simp only [List.foldl_nil]
      rw [getD_ge _ _ (by omega), getD_ge _ _ (by omega)]
  | cons G gs ih =>
    intro W1 W2 hlen hag hS hg
    simp only [List.foldl_cons] at hS ⊢
    have hl1 : (bstp W1 G).length = W1.length + 1 := by simp [bstp]
    have hl2 : (bstp W2 G).length = W2.length + 1 := by simp [bstp]
    apply ih (bstp W1 G) (bstp W2 G) (by omega)
    · intro i hi hB
      rw [hl1] at hi
      by_cases h : i < W1.length
      · have e1 : (bstp W1 G).getD i false = W1.getD i false := List.getD_append _ _ _ _ h
        have e2 : (bstp W2 G).getD i false = W2.getD i false :=
          List.getD_append _ _ _ _ (hlen ▸ h)
        rw [e1, e2]
        exact hag i h hB
      · have hi' : i = W1.length := by omega
        subst hi'
        have c := hg 0 G (by simp)
        simp only [Nat.add_zero] at c
        rcases c with c | c | ⟨cl, cr⟩
        · exact absurd c hB
        · have f1 := foldl_prefix gs (bstp W1 G) W1.length (by omega)
          have f2 := foldl_prefix gs (bstp W2 G) W1.length (by omega)
          rw [← f1, ← f2]
          exact hS _ c
        · have opd : ∀ t, (¬ B t ∨ W1.length ≤ t) → W1.getD t false = W2.getD t false := by
            intro t ht
            by_cases h3 : t < W1.length
            · rcases ht with ht | ht
              · exact hag t h3 ht
              · omega
            · rw [getD_ge _ _ (by omega), getD_ge _ _ (by omega)]
          have e1 : (bstp W1 G).getD W1.length false
              = G.op (W1.getD G.left false) (W1.getD G.right false) := getD_snoc_eq _ _
          have e2 : (bstp W2 G).getD W1.length false
              = G.op (W2.getD G.left false) (W2.getD G.right false) := by
            rw [hlen]
            exact getD_snoc_eq _ _
          rw [e1, e2, opd _ cl, opd _ cr]
    · exact hS
    · intro p G' hp
      have c := hg (p + 1) G' (by simpa using hp)
      rw [hl1]
      have e : W1.length + 1 + p = W1.length + (p + 1) := by omega
      rw [e]
      exact c

-- Inputs that differ only at `v` and `u`.
theorem inp_eq {n : ℕ} (x : Fin n → Bool) (v u : Fin n) (a b a' b' : Bool) (i : ℕ)
    (h1 : a = a' ∨ i ≠ v.val) (h2 : b = b' ∨ i ≠ u.val) :
    (List.ofFn (Function.update (Function.update x v a) u b)).getD i false
      = (List.ofFn (Function.update (Function.update x v a') u b')).getD i false := by
  by_cases hi : i < n
  · rw [getD_ofFn _ i hi, getD_ofFn _ i hi]
    have h1' : a = a' ∨ (⟨i, hi⟩ : Fin n) ≠ v := by
      rcases h1 with h | h
      · exact Or.inl h
      · exact Or.inr (fun e => h (congrArg Fin.val e))
    have h2' : b = b' ∨ (⟨i, hi⟩ : Fin n) ≠ u := by
      rcases h2 with h | h
      · exact Or.inl h
      · exact Or.inr (fun e => h (congrArg Fin.val e))
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; omega)]

-- Changing the input `c`, whose only reader is gate `h`, whose wire is read only by gate `k`,
-- changes no wire below `k` other than `c` and the wire of `h`.
theorem indep (n : ℕ) (D : BinaryCircuit) (I1 I2 : List Bool) (hl1 : I1.length = n)
    (hl2 : I2.length = n) (c : ℕ) (hI : ∀ i, i ≠ c → I1.getD i false = I2.getD i false)
    (h k : ℕ)
    (rc : ∀ j G, D.gates[j]? = some G → (G.left = c ∨ G.right = c) → j = h)
    (rh : ∀ j G, D.gates[j]? = some G → (G.left = n + h ∨ G.right = n + h) → h < j → j = k)
    (w : ℕ) (hw1 : w ≠ c) (hw2 : w ≠ n + h) (hw3 : w < n + k) :
    (D.gates.foldl bstp I1).getD w false = (D.gates.foldl bstp I2).getD w false := by
  apply gen (fun i => i = c ∨ i = n + h ∨ n + k ≤ i) (fun _ => False) D.gates I1 I2
    (by omega)
  · intro i _ hB
    exact hI i (fun e => hB (Or.inl e))
  · intro i hi
    exact hi.elim
  · intro p G hp
    rw [hl1]
    by_cases c1 : k ≤ p
    · exact Or.inl (Or.inr (Or.inr (by omega)))
    by_cases c2 : p = h
    · exact Or.inl (Or.inr (Or.inl (by omega)))
    refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · by_cases c3 : n + p ≤ G.left
      · exact Or.inr c3
      · left
        rintro (e | e | e)
        · exact c2 (rc p G hp (Or.inl e))
        · have := rh p G hp (Or.inl e) (by omega)
          omega
        · omega
    · by_cases c3 : n + p ≤ G.right
      · exact Or.inr c3
      · left
        rintro (e | e | e)
        · exact c2 (rc p G hp (Or.inr e))
        · have := rh p G hp (Or.inr e) (by omega)
          omega
        · omega
  · rintro (e | e | e)
    · exact hw1 e
    · exact hw2 e
    · omega

-- If the wire of gate `k` agrees in two runs that differ only at the inputs `cv` and `cu`,
-- every wire agrees except those two inputs and the wires of their readers `g` and `h`.
theorem flip (n : ℕ) (D : BinaryCircuit) (I1 I2 : List Bool) (hl1 : I1.length = n)
    (hl2 : I2.length = n) (cv cu g h k : ℕ)
    (hI : ∀ i, i ≠ cv → i ≠ cu → I1.getD i false = I2.getD i false)
    (rv : ∀ j G, D.gates[j]? = some G → (G.left = cv ∨ G.right = cv) → j = g)
    (ru : ∀ j G, D.gates[j]? = some G → (G.left = cu ∨ G.right = cu) → j = h)
    (rg : ∀ j G, D.gates[j]? = some G → (G.left = n + g ∨ G.right = n + g) → g < j → j = k)
    (rh : ∀ j G, D.gates[j]? = some G → (G.left = n + h ∨ G.right = n + h) → h < j → j = k)
    (hk : (D.gates.foldl bstp I1).getD (n + k) false = (D.gates.foldl bstp I2).getD (n + k) false)
    (w : ℕ) (hw1 : w ≠ cv) (hw2 : w ≠ cu) (hw3 : w ≠ n + g) (hw4 : w ≠ n + h) :
    (D.gates.foldl bstp I1).getD w false = (D.gates.foldl bstp I2).getD w false := by
  apply gen (fun i => i = cv ∨ i = cu ∨ i = n + g ∨ i = n + h) (fun i => i = n + k) D.gates I1 I2
    (by omega)
  · intro i _ hB
    exact hI i (fun e => hB (Or.inl e)) (fun e => hB (Or.inr (Or.inl e)))
  · intro i hi
    rw [hi]
    exact hk
  · intro p G hp
    rw [hl1]
    by_cases c1 : p = g
    · exact Or.inl (Or.inr (Or.inr (Or.inl (by omega))))
    by_cases c2 : p = h
    · exact Or.inl (Or.inr (Or.inr (Or.inr (by omega))))
    by_cases c3 : p = k
    · exact Or.inr (Or.inl (by omega))
    refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · by_cases c4 : n + p ≤ G.left
      · exact Or.inr c4
      · left
        rintro (e | e | e | e)
        · exact c1 (rv p G hp (Or.inl e))
        · exact c2 (ru p G hp (Or.inl e))
        · exact c3 (rg p G hp (Or.inl e) (by omega))
        · exact c3 (rh p G hp (Or.inl e) (by omega))
    · by_cases c4 : n + p ≤ G.right
      · exact Or.inr c4
      · left
        rintro (e | e | e | e)
        · exact c1 (rv p G hp (Or.inr e))
        · exact c2 (ru p G hp (Or.inr e))
        · exact c3 (rg p G hp (Or.inr e) (by omega))
        · exact c3 (rh p G hp (Or.inr e) (by omega))
  · rintro (e | e | e | e)
    · exact hw1 e
    · exact hw2 e
    · exact hw3 e
    · exact hw4 e

-- The wires of the circuit when the inputs `v` and `u` are set to `a` and `b`.
def run {n : ℕ} (D : BinaryCircuit) (x : Fin n → Bool) (v u : Fin n) (a b : Bool) : List Bool :=
  D.gates.foldl bstp (List.ofFn (Function.update (Function.update x v a) u b))

theorem xor_flip (op : Bool → Bool → Bool)
    (hop : (op false false = false ∧ op false true = true ∧ op true false = true ∧
        op true true = false) ∨
      (op false false = true ∧ op false true = false ∧ op true false = false ∧
        op true true = true)) (p q : Bool) : op p q = op (!p) (!q) := by
  rcases hop with ⟨t1, t2, t3, t4⟩ | ⟨t1, t2, t3, t4⟩ <;> cases p <;> cases q <;> simp_all

theorem ne_not (p q : Bool) (h : ¬ p = q) : q = !p := by
  cases p <;> cases q <;> simp_all

end PEqualNP.Outside.L_meta_698

open PEqualNP.Outside.L_meta_698 PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_698 : ∀ (n : ℕ) (D : PEqualNP.MetaComplexity.BinaryCircuit) (v u : Fin n) (g h k : ℕ), v ≠ u → g ≠ h → (∀ j : ℕ, (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[j]? = some G ∧ (G.left = v.val ∨ G.right = v.val)) ↔ j = g) → (∀ j : ℕ, (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[j]? = some G ∧ (G.left = u.val ∨ G.right = u.val)) ↔ j = h) → (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[g]? = some G ∧ ¬ (G.left = v.val ∧ G.right = v.val)) → (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[h]? = some G ∧ ¬ (G.left = u.val ∧ G.right = u.val)) → (∀ j : ℕ, (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[j]? = some G ∧ (G.left = n + g ∨ G.right = n + g) ∧ g < j) ↔ j = k) → (∀ j : ℕ, (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[j]? = some G ∧ (G.left = n + h ∨ G.right = n + h) ∧ h < j) ↔ j = k) → (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[k]? = some G ∧ ((G.op false false = false ∧ G.op false true = true ∧ G.op true false = true ∧ G.op true true = false) ∨ (G.op false false = true ∧ G.op false true = false ∧ G.op true false = false ∧ G.op true true = true))) → D.output ≠ v.val → D.output ≠ u.val → D.output ≠ n + g → D.output ≠ n + h → ∀ (x : Fin n → Bool) (f : Bool → Bool → Bool), (∀ a b : Bool, f a b = D.eval (List.ofFn (Function.update (Function.update x v a) u b))) → (f false false = f true true ∨ (∀ a b : Bool, f a b = f (!a) b) ∨ (∀ a b : Bool, f a b = f a (!b))) := by
  intro n D v u g h k _ hgh hRv hRu _ _ hRg hRh hK ho1 ho2 ho3 ho4 x f hf
  have hvl := v.isLt
  have hul := u.isLt
  obtain ⟨Gk, hk, hop⟩ := hK
  obtain ⟨G1, hk1, hrg, hgk⟩ := (hRg k).mpr rfl
  obtain ⟨G2, hk2, hrh, hhk⟩ := (hRh k).mpr rfl
  have e1 : G1 = Gk := by
    rw [hk] at hk1
    exact (Option.some.inj hk1).symm
  have e2 : G2 = Gk := by
    rw [hk] at hk2
    exact (Option.some.inj hk2).symm
  rw [e1] at hrg
  rw [e2] at hrh
  have rv : ∀ j G, D.gates[j]? = some G → (G.left = v.val ∨ G.right = v.val) → j = g :=
    fun j G hj hr => (hRv j).mp ⟨G, hj, hr⟩
  have ru : ∀ j G, D.gates[j]? = some G → (G.left = u.val ∨ G.right = u.val) → j = h :=
    fun j G hj hr => (hRu j).mp ⟨G, hj, hr⟩
  have rg : ∀ j G, D.gates[j]? = some G → (G.left = n + g ∨ G.right = n + g) → g < j → j = k :=
    fun j G hj hr hlt => (hRg j).mp ⟨G, hj, hr, hlt⟩
  have rh : ∀ j G, D.gates[j]? = some G → (G.left = n + h ∨ G.right = n + h) → h < j → j = k :=
    fun j G hj hr hlt => (hRh j).mp ⟨G, hj, hr, hlt⟩
  have hLR : (Gk.left = n + g ∧ Gk.right = n + h) ∨ (Gk.left = n + h ∧ Gk.right = n + g) := by
    rcases hrg with e | e <;> rcases hrh with e' | e'
    · omega
    · exact Or.inl ⟨e, e'⟩
    · exact Or.inr ⟨e', e⟩
    · omega
  have hfR : ∀ a b, f a b = (run D x v u a b).getD D.output false := by
    intro a b
    rw [hf]
    rfl
  have A1 : ∀ a b b', (run D x v u a b).getD (n + g) false
      = (run D x v u a b').getD (n + g) false := by
    intro a b b'
    exact indep n D _ _ (by simp) (by simp) u.val
      (fun i hi => inp_eq x v u a b a b' i (Or.inl rfl) (Or.inr hi)) h k ru rh (n + g)
      (by omega) (by omega) (by omega)
  have A2 : ∀ a a' b, (run D x v u a b).getD (n + h) false
      = (run D x v u a' b).getD (n + h) false := by
    intro a a' b
    exact indep n D _ _ (by simp) (by simp) v.val
      (fun i hi => inp_eq x v u a b a' b i (Or.inr hi) (Or.inl rfl)) g k rv rg (n + h)
      (by omega) (by omega) (by omega)
  have kv : ∀ a b, (run D x v u a b).getD (n + k) false
      = Gk.op ((run D x v u a b).getD Gk.left false) ((run D x v u a b).getD Gk.right false) := by
    intro a b
    have := gval D.gates (List.ofFn (Function.update (Function.update x v a) u b)) k Gk hk
      (by simp only [List.length_ofFn]; rcases hLR with ⟨e, e'⟩ | ⟨e, e'⟩ <;> omega)
      (by simp only [List.length_ofFn]; rcases hLR with ⟨e, e'⟩ | ⟨e, e'⟩ <;> omega)
    simp only [List.length_ofFn] at this
    exact this
  have FL : ∀ a b a' b', (run D x v u a b).getD (n + k) false
      = (run D x v u a' b').getD (n + k) false → f a b = f a' b' := by
    intro a b a' b' hkv
    rw [hfR, hfR]
    exact flip n D _ _ (by simp) (by simp) v.val u.val g h k
      (fun i h1 h2 => inp_eq x v u a b a' b' i (Or.inr h1) (Or.inr h2)) rv ru rg rh hkv
      D.output ho1 ho2 ho3 ho4
  by_cases c1 : (run D x v u false false).getD (n + g) false
      = (run D x v u true false).getD (n + g) false
  · right
    left
    intro a b
    apply FL
    rw [kv, kv]
    have eg : (run D x v u a b).getD (n + g) false = (run D x v u (!a) b).getD (n + g) false := by
      rw [A1 a b false, A1 (!a) b false]
      cases a
      · exact c1
      · exact c1.symm
    have eh := A2 a (!a) b
    rcases hLR with ⟨e, e'⟩ | ⟨e, e'⟩ <;> rw [e, e', eg, eh]
  · by_cases c2 : (run D x v u false false).getD (n + h) false
        = (run D x v u false true).getD (n + h) false
    · right
      right
      intro a b
      apply FL
      rw [kv, kv]
      have eg := A1 a b (!b)
      have eh : (run D x v u a b).getD (n + h) false
          = (run D x v u a (!b)).getD (n + h) false := by
        rw [A2 a false b, A2 a false (!b)]
        cases b
        · exact c2
        · exact c2.symm
      rcases hLR with ⟨e, e'⟩ | ⟨e, e'⟩ <;> rw [e, e', eg, eh]
    · left
      apply FL
      rw [kv, kv]
      have eg : (run D x v u true true).getD (n + g) false
          = !(run D x v u false false).getD (n + g) false := by
        rw [A1 true true false]
        exact ne_not _ _ c1
      have eh : (run D x v u true true).getD (n + h) false
          = !(run D x v u false false).getD (n + h) false := by
        rw [A2 true false true]
        exact ne_not _ _ c2
      rcases hLR with ⟨e, e'⟩ | ⟨e, e'⟩ <;> rw [e, e', eg, eh] <;> exact xor_flip Gk.op hop _ _
