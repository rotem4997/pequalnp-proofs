import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18351

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem W_inp (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (W gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_snoc, List.getD_append _ _ _ _ (by rw [W_len]; omega)]; exact ih

theorem W_oob (gs : List Gate) (x : List Bool) (i : ℕ) (hi : x.length + gs.length ≤ i) :
    (W gs x).getD i false = false := by
  apply List.getD_eq_default; rw [W_len]; exact hi

theorem W_spec (gs : List Gate) (x : List Bool) : ∀ (k : ℕ) (g : Gate), gs[k]? = some g →
    (W gs x).getD (x.length + k) false =
      g.op.eval (g.inputs.map fun i =>
        if i < x.length + k then (W gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro k g h; simp at h
  | append_singleton gs a ih =>
    intro k g h
    rw [W_snoc]
    rcases Nat.lt_or_ge k gs.length with hk | hk
    · rw [List.getElem?_append_left hk] at h
      rw [List.getD_append _ _ _ _ (by rw [W_len]; omega), ih k g h]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < x.length + k
      · simp only [hi, ite_true]
        rw [List.getD_append _ _ _ _ (by rw [W_len]; omega)]
      · simp only [hi, ite_false]
    · rcases Nat.lt_or_ge k (gs.length + 1) with hk1 | hk1
      · have hk2 : k = gs.length := by omega
        subst hk2
        have hag : a = g := by simpa using h
        subst hag
        rw [List.getD_append_right _ _ _ _ (by rw [W_len]), W_len]
        simp only [Nat.sub_self, List.getD_cons_zero]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < x.length + gs.length
        · simp only [hi, ite_true]
          rw [List.getD_append _ _ _ _ (by rw [W_len]; omega)]
        · simp only [hi, ite_false]
          exact W_oob gs x i (by omega)
      · rw [List.getElem?_eq_none (by simp; omega)] at h
        cases h

def sh (p : ℕ) (i : ℕ) : ℕ := if p < i then i - 1 else i

def up (p : ℕ) (m : ℕ) : ℕ := if m < p then m else m + 1

def del (G : List Gate) (j : ℕ) (T : Gate → Gate) : List Gate :=
  G.take j ++ (G.drop (j + 1)).map T

theorem del_len (G : List Gate) (j : ℕ) (T : Gate → Gate) (hj : j < G.length) :
    (del G j T).length + 1 = G.length := by
  simp [del]; omega

theorem del_lt (G : List Gate) (j : ℕ) (T : Gate → Gate) (k : ℕ) (g : Gate) (hj : j < G.length)
    (hk : k < j) (h : (del G j T)[k]? = some g) : G[k]? = some g := by
  unfold del at h
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_take] at h
  simpa [hk] using h

theorem del_ge (G : List Gate) (j : ℕ) (T : Gate → Gate) (k : ℕ) (g : Gate) (hj : j < G.length)
    (hk : j ≤ k) (h : (del G j T)[k]? = some g) : ∃ g0, G[k + 1]? = some g0 ∧ g = T g0 := by
  unfold del at h
  rw [List.getElem?_append_right (by simp; omega)] at h
  simp only [List.length_take, List.getElem?_map, List.getElem?_drop] at h
  have e : j + 1 + (k - min j G.length) = k + 1 := by
    rw [Nat.min_eq_left (by omega)]; omega
  rw [e] at h
  cases hg : G[k + 1]? with
  | none => rw [hg] at h; simp at h
  | some g0 => rw [hg] at h; exact ⟨g0, rfl, by simpa using h.symm⟩

theorem sim (G : List Gate) (j : ℕ) (T : Gate → Gate) (x : List Bool) (n : ℕ) (hx : x.length = n)
    (hj : j < G.length)
    (hT : ∀ (k : ℕ) (g : Gate), j ≤ k → G[k + 1]? = some g → ∀ ρ ρ' : ℕ → Bool,
      (∀ i, i ≠ n + j → ρ' (sh (n + j) i) = ρ i) →
      ρ (n + j) = (W G x).getD (n + j) false →
      (∀ i, i < n + j → ρ i = (W G x).getD i false) →
      (∀ i, i < n → ρ' i = x.getD i false) →
      (∀ i, n + G.length ≤ i + 1 → ρ' i = false) →
      (T g).op.eval ((T g).inputs.map ρ') = g.op.eval (g.inputs.map ρ)) :
    ∀ m, (W (del G j T) x).getD m false = (W G x).getD (up (n + j) m) false := by
  subst hx
  have hlen := del_len G j T hj
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rcases Nat.lt_or_ge m x.length with hm | hm
  · rw [W_inp _ _ _ hm, show up (x.length + j) m = m by simp only [up]; split_ifs <;> omega,
      W_inp _ _ _ hm]
  · obtain ⟨k, rfl⟩ : ∃ k, m = x.length + k := ⟨m - x.length, by omega⟩
    rcases Nat.lt_or_ge k (del G j T).length with hk | hk
    · have hg : (del G j T)[k]? = some (del G j T)[k] := List.getElem?_eq_getElem hk
      rw [W_spec _ _ k _ hg]
      rcases Nat.lt_or_ge k j with hkj | hkj
      · have hg0 := del_lt G j T k _ hj hkj hg
        rw [show up (x.length + j) (x.length + k) = x.length + k by
          simp only [up]; split_ifs <;> omega, W_spec _ _ k _ hg0]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < x.length + k
        · simp only [hi, ite_true]
          rw [ih i hi, show up (x.length + j) i = i by simp only [up]; split_ifs <;> omega]
        · simp only [hi, ite_false]
      · obtain ⟨g0, hg0, hgT⟩ := del_ge G j T k _ hj hkj hg
        rw [show up (x.length + j) (x.length + k) = x.length + (k + 1) by
          simp only [up]; split_ifs <;> omega, W_spec _ _ (k + 1) _ hg0, hgT]
        apply hT k g0 hkj hg0
        · intro i hi
          by_cases h1 : x.length + j < i
          · have e1 : sh (x.length + j) i = i - 1 := by simp only [sh]; split_ifs; rfl
            rw [e1]
            by_cases h2 : i < x.length + (k + 1)
            · have h3 : i - 1 < x.length + k := by omega
              simp only [h2, h3, ite_true]
              rw [ih (i - 1) h3]
              congr 1
              simp only [up]; split_ifs <;> omega
            · have h3 : ¬ i - 1 < x.length + k := by omega
              simp only [h2, h3, ite_false]
          · have e1 : sh (x.length + j) i = i := by simp only [sh]; split_ifs; rfl
            rw [e1]
            have h2 : i < x.length + (k + 1) := by omega
            have h3 : i < x.length + k := by omega
            simp only [h2, h3, ite_true]
            rw [ih i h3]
            congr 1
            simp only [up]; split_ifs <;> omega
        · have h2 : x.length + j < x.length + (k + 1) := by omega
          simp only [h2, ite_true]
        · intro i hi
          have h2 : i < x.length + (k + 1) := by omega
          simp only [h2, ite_true]
        · intro i hi
          have h3 : i < x.length + k := by omega
          simp only [h3, ite_true]
          exact W_inp _ _ _ hi
        · intro i hi
          have h3 : ¬ i < x.length + k := by omega
          simp only [h3, ite_false]
    · rw [W_oob _ _ _ (by omega), W_oob _ _ _ (by simp only [up]; split_ifs <;> omega)]

def Ts (p t : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map fun i => if i = p then t else sh p i⟩

theorem Ts_eval (p t : ℕ) (g : Gate) (ρ ρ' : ℕ → Bool)
    (h1 : ∀ i, i ≠ p → ρ' (sh p i) = ρ i) (hp : ρ' t = ρ p) :
    (Ts p t g).op.eval ((Ts p t g).inputs.map ρ') = g.op.eval (g.inputs.map ρ) := by
  simp only [Ts, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i = p
  · subst hi; simp only [Function.comp, ite_true]; exact hp
  · simp only [Function.comp, hi, ite_false]; exact h1 i hi

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

def Tt (p : ℕ) : Gate → Gate
  | ⟨GateOp.and, l⟩ => ⟨GateOp.and, (l.filter fun i => decide (i ≠ p)).map (sh p)⟩
  | ⟨GateOp.or, l⟩ => if p ∈ l then ⟨GateOp.and, []⟩ else ⟨GateOp.or, l.map (sh p)⟩
  | ⟨GateOp.not, l⟩ => if l.head? = some p then ⟨GateOp.or, []⟩ else ⟨GateOp.not, l.map (sh p)⟩
  | g => g

theorem all_filter (p : ℕ) (ρ ρ' : ℕ → Bool) (h1 : ∀ i, i ≠ p → ρ' (sh p i) = ρ i)
    (hp : ρ p = true) (l : List ℕ) :
    ((((l.filter fun i => decide (i ≠ p)).map (sh p)).map ρ').all id) = ((l.map ρ).all id) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : a = p
    · have e : ((a :: l).filter fun i => decide (i ≠ p)) = (l.filter fun i => decide (i ≠ p)) := by
        simp [ha]
      rw [e, ih]
      simp [ha, hp]
    · have e : ((a :: l).filter fun i => decide (i ≠ p))
          = a :: (l.filter fun i => decide (i ≠ p)) := by
        simp [ha]
      rw [e]
      simp only [List.map_cons, List.all_cons]
      rw [ih, h1 a ha]

theorem Tt_eval (p : ℕ) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (ρ ρ' : ℕ → Bool)
    (h1 : ∀ i, i ≠ p → ρ' (sh p i) = ρ i) (hp : ρ p = true) :
    (Tt p g).op.eval ((Tt p g).inputs.map ρ') = g.op.eval (g.inputs.map ρ) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | and =>
    simp only [Tt, GateOp.eval]
    exact all_filter p ρ ρ' h1 hp inputs
  | or =>
    by_cases hm : p ∈ inputs
    · simp only [Tt, hm, ite_true, GateOp.eval]
      simp only [List.map_nil, List.all_nil]
      symm
      rw [List.any_eq_true]
      exact ⟨true, List.mem_map.mpr ⟨p, hm, hp⟩, rfl⟩
    · simp only [Tt, hm, ite_false, GateOp.eval, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact h1 i (fun h => hm (h ▸ hi))
  | not =>
    cases inputs with
    | nil => simp [Tt, GateOp.eval]
    | cons a l =>
      by_cases ha : a = p
      · subst ha; simp [Tt, GateOp.eval, hp]
      · simp [Tt, GateOp.eval, ha, h1 a ha]
  | mod m => simp at hop
  | maj => simp at hop

theorem Tt_fan (p : ℕ) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (Tt p g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (Tt p g).inputs.length ≤ 2 := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hl⟩ := h
  cases op with
  | and =>
    refine ⟨by simp [Tt], ?_⟩
    simp only [Tt, List.length_map]
    exact le_trans (List.length_filter_le _ _) hl
  | or =>
    by_cases hm : p ∈ inputs
    · simp [Tt, hm]
    · refine ⟨by simp [Tt, hm], ?_⟩
      simp only [Tt, hm, ite_false, List.length_map]
      exact hl
  | not =>
    by_cases hm : inputs.head? = some p
    · simp [Tt, hm]
    · refine ⟨by simp [Tt, hm], ?_⟩
      simp only [Tt, hm, ite_false, List.length_map]
      exact hl
  | mod m => simp at hop
  | maj => simp at hop

theorem Ts_fan (p t : ℕ) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (Ts p t g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (Ts p t g).inputs.length ≤ 2 := by
  refine ⟨h.1, ?_⟩
  simp only [Ts, List.length_map]
  exact h.2

def FT (G : List Gate) : Prop :=
  ∀ g ∈ G, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def eff (g : Gate) : List ℕ :=
  g.inputs.take (bif g.op.eval [false] then 1 else 2)

/-- A removable gate is constant or agrees with an earlier wire on every input. -/
def Red (n : ℕ) (G : List Gate) (j : ℕ) : Prop :=
  (∃ b : Bool, ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD (n + j) false = b) ∨
  (∃ o, o < n + j ∧ ∀ x : Fin n → Bool,
    (W G (List.ofFn x)).getD (n + j) false = (W G (List.ofFn x)).getD o false)

theorem fin2 (n : ℕ) (h : (Fin n → Bool) → Bool) (G : List Gate) (out : ℕ) (hF : FT G)
    (hf : ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD out false = h x)
    (j : ℕ) (hj : j < G.length) (T : Gate → Gate)
    (hTF : ∀ g ∈ G, (T g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (T g).inputs.length ≤ 2)
    (hT : ∀ (x : Fin n → Bool) (k : ℕ) (g : Gate), j ≤ k → G[k + 1]? = some g →
      ∀ ρ ρ' : ℕ → Bool,
      (∀ i, i ≠ n + j → ρ' (sh (n + j) i) = ρ i) →
      ρ (n + j) = (W G (List.ofFn x)).getD (n + j) false →
      (∀ i, i < n + j → ρ i = (W G (List.ofFn x)).getD i false) →
      (∀ i, i < n → ρ' i = (List.ofFn x).getD i false) →
      (∀ i, n + G.length ≤ i + 1 → ρ' i = false) →
      (T g).op.eval ((T g).inputs.map ρ') = g.op.eval (g.inputs.map ρ))
    (ho : out = n + j → ∃ o, o < n + j ∧
      ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD o false = h x) :
    ∃ (G' : List Gate) (out' : ℕ), FT G' ∧ G'.length + 1 = G.length ∧
      (∀ x : Fin n → Bool, (W G' (List.ofFn x)).getD out' false = h x) ∧
      ∀ (x : Fin n → Bool) (m : ℕ), m < n + j →
        (W G' (List.ofFn x)).getD m false = (W G (List.ofFn x)).getD m false := by
  have key : ∀ (x : Fin n → Bool) (m : ℕ),
      (W (del G j T) (List.ofFn x)).getD m false
        = (W G (List.ofFn x)).getD (up (n + j) m) false := by
    intro x
    exact sim G j T (List.ofFn x) n (by simp) hj (fun k g hk hg => hT x k g hk hg)
  have hlen := del_len G j T hj
  have hFT : FT (del G j T) := by
    intro g hg
    unfold del at hg
    rcases List.mem_append.mp hg with h1 | h1
    · exact hF g (List.mem_of_mem_take h1)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h1
      exact hTF g0 (List.mem_of_mem_drop hg0)
  have hlow : ∀ (x : Fin n → Bool) (m : ℕ), m < n + j →
      (W (del G j T) (List.ofFn x)).getD m false = (W G (List.ofFn x)).getD m false := by
    intro x m hm
    rw [key x m, show up (n + j) m = m by simp [up, hm]]
  by_cases hout : out = n + j
  · obtain ⟨o, hon, hox⟩ := ho hout
    exact ⟨del G j T, o, hFT, hlen, fun x => by rw [hlow x o hon]; exact hox x, hlow⟩
  · refine ⟨del G j T, sh (n + j) out, hFT, hlen, ?_, hlow⟩
    intro x
    rw [key x, ← hf x]
    congr 1
    simp only [up, sh]
    split_ifs <;> omega

theorem sdl (n : ℕ) (h : (Fin n → Bool) → Bool) (hnc : ∃ x y : Fin n → Bool, h x ≠ h y)
    (G : List Gate) (out : ℕ) (hF : FT G)
    (hf : ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD out false = h x)
    (j : ℕ) (hj : j < G.length) (hR : Red n G j) :
    ∃ (G' : List Gate) (out' : ℕ), FT G' ∧ G'.length + 1 = G.length ∧
      (∀ x : Fin n → Bool, (W G' (List.ofFn x)).getD out' false = h x) ∧
      ∀ (x : Fin n → Bool) (m : ℕ), m < n + j →
        (W G' (List.ofFn x)).getD m false = (W G (List.ofFn x)).getD m false := by
  rcases hR with ⟨b, hb⟩ | ⟨o, hoj, hoe⟩
  · have ho : out = n + j → ∃ o, o < n + j ∧
        ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD o false = h x := by
      intro hout
      exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      rw [← hf x, ← hf y, hout, hb x, hb y]
    cases b with
    | false =>
      refine fin2 n h G out hF hf j hj (Ts (n + j) (n + G.length))
        (fun g hg => Ts_fan _ _ g (hF g hg)) ?_ ho
      intro x k g _ _ ρ ρ' h1 h2 h5 h3 h4
      apply Ts_eval _ _ g ρ ρ' h1
      rw [h2, hb x]
      exact h4 _ (by omega)
    | true =>
      refine fin2 n h G out hF hf j hj (Tt (n + j))
        (fun g hg => Tt_fan _ g (hF g hg)) ?_ ho
      intro x k g _ hg ρ ρ' h1 h2 h5 h3 h4
      exact Tt_eval _ g (hF g (List.mem_of_getElem? hg)).1 ρ ρ' h1 (h2.trans (hb x))
  · refine fin2 n h G out hF hf j hj (Ts (n + j) o)
      (fun g hg => Ts_fan _ _ g (hF g hg)) ?_ ?_
    · intro x k g _ _ ρ ρ' h1 h2 h5 h3 h4
      apply Ts_eval _ _ g ρ ρ' h1
      have e : sh (n + j) o = o := by
        simp only [sh]; split_ifs <;> omega
      have a1 := h1 o (by omega)
      rw [e] at a1
      rw [a1, h5 o hoj, h2]
      exact (hoe x).symm
    · intro hout
      exact ⟨o, hoj, fun x => by rw [← hoe x, ← hout]; exact hf x⟩

/-- Delete the designated gates in descending order so earlier gate indices stay valid. -/
theorem iter (n : ℕ) (h : (Fin n → Bool) → Bool) (hnc : ∃ x y : Fin n → Bool, h x ≠ h y) :
    ∀ (k : ℕ) (S : Finset ℕ), S.card = k → ∀ (G : List Gate) (out : ℕ), FT G →
      (∀ x : Fin n → Bool, (W G (List.ofFn x)).getD out false = h x) →
      (∀ j ∈ S, j < G.length ∧ Red n G j) →
      ∃ (G' : List Gate) (out' : ℕ), FT G' ∧ G'.length + k = G.length ∧
        ∀ x : Fin n → Bool, (W G' (List.ofFn x)).getD out' false = h x := by
  intro k
  induction k with
  | zero =>
    intro S _ G out hF hf _
    exact ⟨G, out, hF, rfl, hf⟩
  | succ k ih =>
    intro S hS G out hF hf hR
    have hne : S.Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨hj, hRj⟩ := hR (S.max' hne) (S.max'_mem hne)
    obtain ⟨G1, out1, hF1, hl1, hf1, hlow⟩ := sdl n h hnc G out hF hf (S.max' hne) hj hRj
    have hR1 : ∀ i ∈ S.erase (S.max' hne), i < G1.length ∧ Red n G1 i := by
      intro i hi
      have hlt : i < S.max' hne := Finset.lt_max'_of_mem_erase_max' S hne hi
      obtain ⟨_, hRi⟩ := hR i (Finset.mem_of_mem_erase hi)
      refine ⟨by omega, ?_⟩
      rcases hRi with ⟨b, hb⟩ | ⟨o, ho, hoe⟩
      · exact Or.inl ⟨b, fun x => by rw [hlow x _ (by omega)]; exact hb x⟩
      · exact Or.inr ⟨o, ho, fun x => by
          rw [hlow x _ (by omega), hlow x _ (by omega)]; exact hoe x⟩
    obtain ⟨G2, out2, hF2, hl2, hf2⟩ := ih (S.erase (S.max' hne))
      (by rw [Finset.card_erase_of_mem (S.max'_mem hne)]; omega) G1 out1 hF1 hf1 hR1
    exact ⟨G2, out2, hF2, by omega, hf2⟩

theorem gl0 (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (q : ℕ) (c : Bool) (hq : q ∈ eff g) :
    (∃ b : Bool, ∀ ρ : ℕ → Bool, ρ q = c → g.op.eval (g.inputs.map ρ) = b) ∨
    (∃ w : ℕ, ∀ ρ : ℕ → Bool, ρ q = c → g.op.eval (g.inputs.map ρ) = ρ w) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | and =>
    rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [eff, GateOp.eval] at hq
    · simp [eff, GateOp.eval] at hq
      subst hq
      exact Or.inl ⟨c, fun ρ hρ => by simp [GateOp.eval, hρ]⟩
    · simp [eff, GateOp.eval] at hq
      cases c with
      | false =>
        exact Or.inl ⟨false, fun ρ hρ => by
          rcases hq with rfl | rfl <;> simp [GateOp.eval, hρ]⟩
      | true =>
        rcases hq with rfl | rfl
        · exact Or.inr ⟨b, fun ρ hρ => by simp [GateOp.eval, hρ]⟩
        · exact Or.inr ⟨a, fun ρ hρ => by simp [GateOp.eval, hρ]⟩
    · simp at hlen
  | or =>
    rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [eff, GateOp.eval] at hq
    · simp [eff, GateOp.eval] at hq
      subst hq
      exact Or.inl ⟨c, fun ρ hρ => by simp [GateOp.eval, hρ]⟩
    · simp [eff, GateOp.eval] at hq
      cases c with
      | true =>
        exact Or.inl ⟨true, fun ρ hρ => by
          rcases hq with rfl | rfl <;> simp [GateOp.eval, hρ]⟩
      | false =>
        rcases hq with rfl | rfl
        · exact Or.inr ⟨b, fun ρ hρ => by simp [GateOp.eval, hρ]⟩
        · exact Or.inr ⟨a, fun ρ hρ => by simp [GateOp.eval, hρ]⟩
    · simp at hlen
  | not =>
    rcases inputs with _ | ⟨a, l⟩
    · simp [eff, GateOp.eval] at hq
    · simp [eff, GateOp.eval] at hq
      subst hq
      exact Or.inl ⟨!c, fun ρ hρ => by simp [GateOp.eval, hρ]⟩
  | mod m => simp at hop
  | maj => simp at hop

theorem gl (n : ℕ) (G : List Gate) (k : ℕ) (g : Gate) (hg : G[k]? = some g)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (q : ℕ) (c : Bool) (hq : q ∈ eff g)
    (hc : ∀ x : Fin n → Bool,
      (if q < n + k then (W G (List.ofFn x)).getD q false else false) = c) :
    Red n G k := by
  have key : ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD (n + k) false =
      g.op.eval (g.inputs.map fun i =>
        if i < n + k then (W G (List.ofFn x)).getD i false else false) := by
    intro x
    have e := W_spec G (List.ofFn x) k g hg
    rw [List.length_ofFn] at e
    exact e
  rcases gl0 g hop hlen q c hq with ⟨b, hb⟩ | ⟨w, hw⟩
  · exact Or.inl ⟨b, fun x => by
      rw [key x]
      exact hb (fun i => if i < n + k then (W G (List.ofFn x)).getD i false else false) (hc x)⟩
  · by_cases hwk : w < n + k
    · exact Or.inr ⟨w, hwk, fun x => by
        rw [key x,
          hw (fun i => if i < n + k then (W G (List.ofFn x)).getD i false else false) (hc x)]
        exact ite_eq_left hwk⟩
    · exact Or.inl ⟨false, fun x => by
        rw [key x,
          hw (fun i => if i < n + k then (W G (List.ofFn x)).getD i false else false) (hc x)]
        exact ite_eq_right hwk⟩

/-- Inserting one constant at the front shifts generated wires by one. -/
private def pinIndex (n v i : ℕ) : ℕ :=
  if i = v then n else if i < n then i else i + 1

private def pinGate (n v : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (pinIndex n v)⟩

private theorem pinIndex_generated {n v i : ℕ} (hv : v < n) (hi : n ≤ i) :
    pinIndex n v i = i + 1 := by
  simp [pinIndex, show i ≠ v by omega, show ¬i < n by omega]

private theorem append_value (a : List Bool) (d : Bool) :
    (a ++ [d]).getD a.length false = d := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

private theorem pin_fold (G : List Gate) (n v : ℕ) (hv : v < n) :
    ∀ old new : List Bool, n ≤ old.length → new.length = old.length + 1 →
    (∀ i, new.getD (pinIndex n v i) false = old.getD i false) →
    ∀ i, (W (G.map (pinGate n v)) new).getD (pinIndex n v i) false =
      (W G old).getD i false := by
  induction G with
  | nil => intro old new _ _ h i; exact h i
  | cons g G ih =>
    intro old new hOld hNew h i
    let d := g.op.eval (g.inputs.map fun j => old.getD j false)
    have hd : (pinGate n v g).op.eval
        ((pinGate n v g).inputs.map fun j => new.getD j false) = d := by
      change g.op.eval ((g.inputs.map (pinIndex n v)).map _) = _
      rw [List.map_map]
      congr 1
      exact List.map_congr_left fun j _ => h j
    change (W (G.map (pinGate n v))
      (new ++ [(pinGate n v g).op.eval ((pinGate n v g).inputs.map fun j => new.getD j false)])).getD
      (pinIndex n v i) false = (W G (old ++ [d])).getD i false
    rw [hd]
    apply ih (old ++ [d]) (new ++ [d]) (by simp; omega) (by simp; omega) _ i
    intro j
    rcases lt_trichotomy j old.length with hj | rfl | hj
    · have hm : pinIndex n v j < new.length := by
        simp only [pinIndex]; split_ifs <;> omega
      rw [List.getD_append _ _ _ _ hm, List.getD_append _ _ _ _ hj]
      exact h j
    · rw [pinIndex_generated hv hOld, ← hNew, append_value, append_value]
    · have hm : pinIndex n v j = j + 1 := pinIndex_generated hv (by omega)
      rw [hm, List.getD_eq_default, List.getD_eq_default]
      all_goals simp; omega

private def pinConstant (b : Bool) : Gate :=
  ⟨if b then .and else .or, []⟩

private theorem pinConstant_eval (b : Bool) :
    (pinConstant b).op.eval [] = b := by
  cases b <;> rfl

private def pinList (n : ℕ) (v : Fin n) (b : Bool) (G : List Gate) : List Gate :=
  pinConstant b :: G.map (pinGate n v.val)

private theorem pin_sim (n : ℕ) (v : Fin n) (b : Bool) (G : List Gate)
    (x : Fin n → Bool) (i : ℕ) :
    (W (pinList n v b G) (List.ofFn x)).getD (pinIndex n v.val i) false =
    (W G (List.ofFn (Function.update x v b))).getD i false := by
  have hpre : W (pinList n v b G) (List.ofFn x) =
      W (G.map (pinGate n v.val)) (List.ofFn x ++ [b]) := by
    simp [W, pinList, show (pinConstant b).inputs = [] by rfl, pinConstant_eval]
  rw [hpre]
  apply pin_fold G n v.val v.isLt _ _ (by simp) (by simp) _ i
  intro j
  by_cases hj : j < n
  · rw [ofFn_getD _ _ hj]
    by_cases h : j = v.val
    · simp only [pinIndex, h, ite_true, Function.update_self]
      simpa only [List.length_ofFn] using append_value (List.ofFn x) b
    · have e : (⟨j, hj⟩ : Fin n) ≠ v := fun e => h (congrArg Fin.val e)
      simp only [pinIndex, h, hj, ite_false, ite_true, Function.update_of_ne e]
      rw [List.getD_append _ _ _ _ (by simpa using hj), ofFn_getD _ _ hj]
  · rw [pinIndex_generated v.isLt (by omega), List.getD_eq_default, List.getD_eq_default]
    all_goals simp; omega

private theorem pin_fan (n : ℕ) (v : Fin n) (b : Bool) (G : List Gate) (h : FT G) :
    FT (pinList n v b G) := by
  intro g hg
  simp only [pinList, List.mem_cons, List.mem_map] at hg
  rcases hg with rfl | ⟨g, hg, rfl⟩
  · cases b <;> simp [pinConstant]
  · simpa [pinGate] using h g hg

private theorem reader_mem (g : Gate) (q : ℕ) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2)
    (h : (g.op ≠ .not ∧ q ∈ g.inputs) ∨ (g.op = .not ∧ g.inputs.head? = some q)) :
    q ∈ eff g := by
  rcases h with ⟨hne, hm⟩ | ⟨he, hm⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with ha | ho | hn
    · simpa [eff, ha, GateOp.eval, List.take_of_length_le hlen] using hm
    · simpa [eff, ho, GateOp.eval, List.take_of_length_le hlen] using hm
    · exact (hne hn).elim
  · cases hi : g.inputs with
    | nil => simp [hi] at hm
    | cons a l => simpa [eff, he, GateOp.eval, hi] using (by simpa [hi] using hm : a = q).symm

private theorem pinGate_eff (n v : ℕ) (g : Gate) :
    eff (pinGate n v g) = (eff g).map (pinIndex n v) := by
  simp [eff, pinGate, List.map_take]

end PEqualNP.Outside.L_meta_18351

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_18351

/-- Pinning an input permits deleting a constant gate and a distinct effective reader. -/
theorem PEqualNP.Outside.L_meta_18351
    (n : ℕ) (C : Circuit) (v : Fin n) (b c : Bool) (j : Fin C.gates.length) :
    FanInTwo C →
    (∃ y : Fin n → Bool, C.eval (List.ofFn (Function.update y v b)) = false) →
    (∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD (n + j.val) false = c) →
    (∃ k : Fin C.gates.length, k ≠ j ∧
      ((C.gates.get k).op ≠ .not ∧ n + j.val ∈ (C.gates.get k).inputs ∨
       (C.gates.get k).op = .not ∧ (C.gates.get k).inputs.head? = some (n + j.val))) →
    ∃ D : Circuit, FanInTwo D ∧ D.size + 2 ≤ C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v b)) := by
  intro hF hFalse hConst hReader
  obtain ⟨k, hkj, hReader⟩ := hReader
  have hjk : j.val ≠ k.val := fun e => hkj (Fin.ext e.symm)
  have hj := j.isLt
  have hk := k.isLt
  let f (x : Fin n → Bool) := C.eval (List.ofFn (Function.update x v b))
  by_cases ht : ∃ x, f x = true
  · obtain ⟨x, hx⟩ := ht
    obtain ⟨y, hy⟩ := hFalse
    change f y = false at hy
    have hnc : ∃ x y, f x ≠ f y := ⟨x, y, by rw [hx, hy]; decide⟩
    let G := pinList n v b C.gates
    have hLen : G.length = C.gates.length + 1 := by simp [G, pinList]
    have sim (i : ℕ) (x : Fin n → Bool) :
        (W G (List.ofFn x)).getD (pinIndex n v.val i) false =
          (C.wires (List.ofFn (Function.update x v b))).getD i false :=
      pin_sim n v b C.gates x i
    have hc (x : Fin n → Bool) :
        (W G (List.ofFn x)).getD (n + j.val + 1) false = c := by
      rw [← pinIndex_generated v.isLt (by omega : n ≤ n + j.val), sim, hConst]
    have h0 : Red n G 0 := by
      refine Or.inl ⟨b, fun x => ?_⟩
      have e := W_spec G (List.ofFn x) 0 (pinConstant b) (by simp [G, pinList])
      simpa [show (pinConstant b).inputs = [] by rfl, pinConstant_eval] using e
    let g := C.gates.get k
    have hg : C.gates[k.val]? = some g := List.getElem?_eq_getElem hk
    have hGg : G[k.val + 1]? = some (pinGate n v.val g) := by
      change (C.gates.map (pinGate n v.val))[k.val]? = some (pinGate n v.val g)
      rw [List.getElem?_map, hg]
      rfl
    have hfg := hF g (List.mem_of_getElem? hg)
    have hread : n + j.val ∈ eff g := reader_mem g _ hfg.1 hfg.2 hReader
    have hr : Red n G (k.val + 1) := by
      apply gl n G (k.val + 1) (pinGate n v.val g) hGg
        (by simpa [pinGate] using hfg.1) (by simpa [pinGate] using hfg.2)
        (n + j.val + 1) (if j.val < k.val then c else false)
      · rw [pinGate_eff, ← pinIndex_generated v.isLt (by omega : n ≤ n + j.val)]
        exact List.mem_map_of_mem hread
      · intro x
        -- A forward reference reads the default false before the producer exists.
        by_cases h : j.val < k.val
        · rw [ite_eq_left h, ite_eq_left (by omega), hc]
        · rw [ite_eq_right h, ite_eq_right (by omega)]
    -- The prepended constant is one of the three gates removed.
    let S : Finset ℕ := {0, j.val + 1, k.val + 1}
    have hS : S.card = 3 := by
      simp [S, Finset.card_insert_of_notMem, hjk]
    have hRed : ∀ i ∈ S, i < G.length ∧ Red n G i := by
      intro i hi
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact ⟨by omega, h0⟩
      · exact ⟨by omega, Or.inl ⟨c, fun x => by simpa [Nat.add_assoc] using hc x⟩⟩
      · exact ⟨by omega, hr⟩
    obtain ⟨G', out', hF', hLen', hEval'⟩ := iter n f hnc 3 S hS G (pinIndex n v.val C.output)
      (pin_fan n v b C.gates hF) (fun x => sim C.output x) hRed
    exact ⟨⟨G', out'⟩, hF', by change G'.length + 2 ≤ C.gates.length; omega, hEval'⟩
  · refine ⟨⟨[], n⟩, by simp [FanInTwo], ?_, fun x => ?_⟩
    · change 0 + 2 ≤ C.gates.length
      omega
    · have hf : f x = false := by
        cases e : f x with
        | false => rfl
        | true => exact (ht ⟨x, e⟩).elim
      change (List.ofFn x).getD n false = f x
      rw [hf, List.getD_eq_default]
      simp
