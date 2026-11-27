import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_7941

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def D (m : Finset ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun d g => d ++ [g.lineDegree d]) ((List.range 26).map fun i => if i ∈ m then 1 else 0)

theorem getD_app_lt {α : Type} (l l' : List α) (d : α) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_len {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem D_snoc (m : Finset ℕ) (gs : List Gate) (g : Gate) :
    D m (gs ++ [g]) = D m gs ++ [g.lineDegree (D m gs)] := by
  simp [D, List.foldl_append]

theorem W_len (gs : List Gate) : ∀ x : List Bool, (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => intro x; simp [W]
  | append_singleton gs g ih =>
    intro x
    rw [W_snoc]
    simp only [List.length_append, List.length_singleton, ih]
    omega

theorem D_len (m : Finset ℕ) (gs : List Gate) : (D m gs).length = 26 + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [D]
  | append_singleton gs g ih =>
    rw [D_snoc]
    simp only [List.length_append, List.length_singleton, ih]
    omega

theorem D0 (m : Finset ℕ) (i : ℕ) (hi : i < 26) :
    (D m []).getD i 0 = if i ∈ m then 1 else 0 := by
  simp [D, List.getD_eq_getElem?_getD, hi]

def Q (f l : ℕ) (v : List Bool → Bool) : Prop :=
  l ≤ f ∧ (f = 0 → ∀ x : List Bool, x.length = 26 → v x = true) ∧
  (1 ≤ l → f ≤ 1 → ∃ a : Fin 13, ∀ x : List Bool, x.length = 26 →
    x.getD (13 + (a : ℕ)) false = true → v x = true) ∧
  (2 ≤ l → f ≤ 2 → ∃ a b : Fin 13, ∀ x : List Bool, x.length = 26 →
    x.getD (13 + (a : ℕ)) false = true → x.getD (13 + (b : ℕ)) false = true → v x = true)

theorem Q_congr {f l : ℕ} {v v' : List Bool → Bool} (h : Q f l v)
    (e : ∀ x : List Bool, x.length = 26 → v x = v' x) : Q f l v' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, fun hf x hx => by rw [← e x hx]; exact h2 hf x hx, ?_, ?_⟩
  · intro hl hf
    obtain ⟨a, ha⟩ := h3 hl hf
    exact ⟨a, fun x hx h => by rw [← e x hx]; exact ha x hx h⟩
  · intro hl hf
    obtain ⟨a, b, hab⟩ := h4 hl hf
    exact ⟨a, b, fun x hx h h2 => by rw [← e x hx]; exact hab x hx h h2⟩

theorem Q_and2 {fa la fb lb : ℕ} {va vb : List Bool → Bool} (ha : Q fa la va) (hb : Q fb lb vb) :
    Q (fa + fb) (la + lb) (fun x => va x && vb x) := by
  obtain ⟨a1, a2, a3, a4⟩ := ha
  obtain ⟨b1, b2, b3, b4⟩ := hb
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro h x hx
    simp [a2 (by omega) x hx, b2 (by omega) x hx]
  · intro hl hf
    by_cases h : 1 ≤ la
    · obtain ⟨a, ha⟩ := a3 h (by omega)
      exact ⟨a, fun x hx h1 => by simp [ha x hx h1, b2 (by omega) x hx]⟩
    · obtain ⟨a, ha⟩ := b3 (by omega) (by omega)
      exact ⟨a, fun x hx h1 => by simp [ha x hx h1, a2 (by omega) x hx]⟩
  · intro hl hf
    by_cases h : 2 ≤ la
    · obtain ⟨a, b, hab⟩ := a4 h (by omega)
      exact ⟨a, b, fun x hx h1 h2 => by simp [hab x hx h1 h2, b2 (by omega) x hx]⟩
    · by_cases h3 : 2 ≤ lb
      · obtain ⟨a, b, hab⟩ := b4 h3 (by omega)
        exact ⟨a, b, fun x hx h1 h2 => by simp [hab x hx h1 h2, a2 (by omega) x hx]⟩
      · obtain ⟨a, ha⟩ := a3 (by omega) (by omega)
        obtain ⟨b, hb⟩ := b3 (by omega) (by omega)
        exact ⟨a, b, fun x hx h1 h2 => by simp [ha x hx h1, hb x hx h2]⟩

theorem Q_or2 {fa la fb lb : ℕ} {va vb : List Bool → Bool} (ha : Q fa la va) (hb : Q fb lb vb) :
    Q (max fa fb) (max la lb) (fun x => va x || vb x) := by
  obtain ⟨a1, a2, a3, a4⟩ := ha
  obtain ⟨b1, b2, b3, b4⟩ := hb
  have ma : fa ≤ max fa fb := le_max_left _ _
  have mb : fb ≤ max fa fb := le_max_right _ _
  refine ⟨max_le_max a1 b1, ?_, ?_, ?_⟩
  · intro h x hx
    simp [a2 (by omega) x hx]
  · intro hl hf
    rcases le_max_iff.mp hl with h | h
    · obtain ⟨a, ha⟩ := a3 h (by omega)
      exact ⟨a, fun x hx h1 => by simp [ha x hx h1]⟩
    · obtain ⟨a, ha⟩ := b3 h (by omega)
      exact ⟨a, fun x hx h1 => by simp [ha x hx h1]⟩
  · intro hl hf
    rcases le_max_iff.mp hl with h | h
    · obtain ⟨a, b, hab⟩ := a4 h (by omega)
      exact ⟨a, b, fun x hx h1 h2 => by simp [hab x hx h1 h2]⟩
    · obtain ⟨a, b, hab⟩ := b4 h (by omega)
      exact ⟨a, b, fun x hx h1 h2 => by simp [hab x hx h1 h2]⟩

theorem gate (dF dL : List ℕ) (V : List Bool → ℕ → Bool) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (hIH : ∀ i ∈ g.inputs, Q (dF.getD i 0) (dL.getD i 0) (fun x => V x i))
    (hsat : ∃ x0 : List Bool, x0.length = 26 ∧ g.op.eval (g.inputs.map (V x0)) = true) :
    Q (g.lineDegree dF) (g.lineDegree dL) (fun x => g.op.eval (g.inputs.map (V x))) := by
  obtain ⟨op, ins⟩ := g
  dsimp only at hop hlen hIH hsat ⊢
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · refine ⟨by simp [Gate.lineDegree], fun _ x _ => by simp [GateOp.eval],
        fun h _ => by simp [Gate.lineDegree] at h, fun h _ => by simp [Gate.lineDegree] at h⟩
    · have e1 : ∀ d : List ℕ, Gate.lineDegree ⟨GateOp.and, [a]⟩ d = d.getD a 0 := by
        intro d; simp [Gate.lineDegree]
      rw [e1, e1]
      exact Q_congr (hIH a (by simp)) (fun x _ => by simp [GateOp.eval])
    · have e1 : ∀ d : List ℕ, Gate.lineDegree ⟨GateOp.and, [a, b]⟩ d = d.getD a 0 + d.getD b 0 := by
        intro d; simp [Gate.lineDegree]
      rw [e1, e1]
      exact Q_congr (Q_and2 (hIH a (by simp)) (hIH b (by simp))) (fun x _ => by simp [GateOp.eval])
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · obtain ⟨x, _, hv⟩ := hsat
      simp [GateOp.eval] at hv
    · have e1 : ∀ d : List ℕ, Gate.lineDegree ⟨GateOp.or, [a]⟩ d = d.getD a 0 := by
        intro d; simp [Gate.lineDegree]
      rw [e1, e1]
      exact Q_congr (hIH a (by simp)) (fun x _ => by simp [GateOp.eval])
    · have e1 : ∀ d : List ℕ, Gate.lineDegree ⟨GateOp.or, [a, b]⟩ d = max (d.getD a 0) (d.getD b 0) := by
        intro d; simp [Gate.lineDegree]
      rw [e1, e1]
      exact Q_congr (Q_or2 (hIH a (by simp)) (hIH b (by simp))) (fun x _ => by simp [GateOp.eval])
    · simp at hlen

theorem main : ∀ gs : List Gate,
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < 26 + j) →
    (∀ j < gs.length, ∃ x : List Bool, x.length = 26 ∧ (W gs x).getD (26 + j) false = true) →
    ∀ i < 26 + gs.length, Q ((D (Finset.range 26) gs).getD i 0) ((D (Finset.Ico 13 26) gs).getD i 0)
      (fun x => (W gs x).getD i false) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ _ _ i hi
    simp only [List.length_nil, Nat.add_zero] at hi
    rw [D0 _ i hi, D0 _ i hi]
    have hr : i ∈ Finset.range 26 := Finset.mem_range.mpr hi
    rw [if_pos hr]
    by_cases h13 : 13 ≤ i
    · rw [if_pos (Finset.mem_Ico.mpr ⟨h13, hi⟩)]
      refine ⟨le_refl _, fun h => absurd h (by norm_num),
        fun _ _ => ⟨⟨i - 13, by omega⟩, fun x _ hx => ?_⟩, fun h _ => absurd h (by norm_num)⟩
      have e : 13 + (i - 13) = i := by omega
      show x.getD i false = true
      rw [← e]
      exact hx
    · rw [if_neg (fun h => h13 (Finset.mem_Ico.mp h).1)]
      exact ⟨by norm_num, fun h => absurd h (by norm_num), fun h _ => absurd h (by norm_num),
        fun h _ => absurd h (by norm_num)⟩
  | append_singleton gs g ih =>
    intro hok hrb hsat i hi
    have hok2 : ∀ g2 ∈ gs, (g2.op = GateOp.and ∨ g2.op = GateOp.or) ∧ g2.inputs.length ≤ 2 :=
      fun g2 hg2 => hok g2 (List.mem_append_left _ hg2)
    have hgd : ∀ j < gs.length, (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ :=
      fun j hj => getD_app_lt _ _ _ _ hj
    have hrb2 : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < 26 + j := by
      intro j hj i hi
      rw [← hgd j hj] at hi
      exact hrb j (by simp; omega) i hi
    have hWlt : ∀ x : List Bool, x.length = 26 → ∀ i < 26 + gs.length,
        (W (gs ++ [g]) x).getD i false = (W gs x).getD i false := by
      intro x hx i hi
      rw [W_snoc]
      exact getD_app_lt _ _ _ _ (by rw [W_len, hx]; exact hi)
    have hsat2 : ∀ j < gs.length, ∃ x : List Bool, x.length = 26 ∧ (W gs x).getD (26 + j) false = true := by
      intro j hj
      obtain ⟨x, hx, hv⟩ := hsat j (by simp; omega)
      exact ⟨x, hx, by rw [← hWlt x hx _ (by omega)]; exact hv⟩
    have IH := ih hok2 hrb2 hsat2
    have hDlt : ∀ m, ∀ i < 26 + gs.length, (D m (gs ++ [g])).getD i 0 = (D m gs).getD i 0 := by
      intro m i hi
      rw [D_snoc]
      exact getD_app_lt _ _ _ _ (by rw [D_len]; exact hi)
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < 26 + gs.length
    · rw [hDlt _ i hlt, hDlt _ i hlt]
      exact Q_congr (IH i hlt) (fun x hx => (hWlt x hx i hlt).symm)
    · have hk : i = 26 + gs.length := by omega
      subst hk
      have hDk : ∀ m, (D m (gs ++ [g])).getD (26 + gs.length) 0 = g.lineDegree (D m gs) := by
        intro m
        rw [D_snoc, ← D_len m gs]
        exact getD_app_len _ _ _
      have hWk : ∀ x : List Bool, x.length = 26 → (W (gs ++ [g]) x).getD (26 + gs.length) false =
          g.op.eval (g.inputs.map fun i => (W gs x).getD i false) := by
        intro x hx
        rw [W_snoc, show 26 + gs.length = (W gs x).length by rw [W_len, hx]]
        exact getD_app_len _ _ _
      rw [hDk, hDk]
      have hgg : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := getD_app_len _ _ _
      have hin : ∀ i ∈ g.inputs, i < 26 + gs.length := by
        intro i hi
        exact hrb gs.length (by simp) i (by rw [hgg]; exact hi)
      have hg : g ∈ gs ++ [g] := by simp
      refine Q_congr (gate (D _ gs) (D _ gs) (fun x i => (W gs x).getD i false) g (hok g hg).1
        (hok g hg).2 (fun i hi => IH i (hin i hi)) ?_) (fun x hx => (hWk x hx).symm)
      obtain ⟨x, hx, hv⟩ := hsat gs.length (by simp)
      exact ⟨x, hx, by rw [← hWk x hx]; exact hv⟩

end PEqualNP.Outside.L_meta_7941

theorem PEqualNP.Outside.L_meta_7941 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 → (∀ x4 < x1.size, ∃ (x6 : List Bool), x6.length = (26 : ℕ) ∧ (x1.wires x6).getD ((26 : ℕ) + x4) Bool.false = Bool.true) → (2 : ℕ) ≤ x1.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) → x1.lineDeg (26 : ℕ) (Finset.range (26 : ℕ)) ≤ (2 : ℕ) → ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), ∀ (x9 : List Bool), x9.length = (26 : ℕ) → x9.getD ((13 : ℕ) + ↑x7) Bool.false = Bool.true → x9.getD ((13 : ℕ) + ↑x8) Bool.false = Bool.true → x1.eval x9 = Bool.true := by
  intro C hm hrb hsat hL hF
  have hok : ∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hm g hg
    refine ⟨?_, h2⟩
    simpa [Set.mem_insert_iff] using h1
  have hlt : C.output < 26 + C.gates.length := by
    by_contra hc
    push_neg at hc
    have h0 : C.lineDeg 26 (Finset.Ico 13 26) = 0 := by
      show (PEqualNP.Outside.L_meta_7941.D (Finset.Ico 13 26) C.gates).getD C.output 0 = 0
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none
        (by rw [PEqualNP.Outside.L_meta_7941.D_len]; omega)]
      rfl
    omega
  have hQ := PEqualNP.Outside.L_meta_7941.main C.gates hok hrb hsat C.output hlt
  obtain ⟨a, b, hab⟩ := hQ.2.2.2 hL hF
  exact ⟨a, b, fun x hx h1 h2 => hab x hx h1 h2⟩
