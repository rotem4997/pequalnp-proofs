import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17177_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- Whether the gate is a NOT gate. -/
def isNot (g : Gate) : Bool :=
  match g.op with
  | GateOp.not => true
  | _ => false

/-- The wires a gate really reads: the first one for NOT, all of them otherwise. -/
def eff (g : Gate) : List ℕ := if isNot g = true then g.inputs.take 1 else g.inputs

/-- Wire values. The gate list is reversed (last gate first), the input is a function. -/
def val (n : ℕ) (x : ℕ → Bool) : List Gate → ℕ → Bool
  | [], w => if w < n then x w else false
  | g :: rg, w =>
    if w = n + rg.length then g.op.eval (g.inputs.map (fun i => val n x rg i)) else val n x rg w

/-- The wires reachable from a set of wires through gate inputs. -/
def dep (n : ℕ) : List Gate → Finset ℕ → Finset ℕ
  | [], T => T.filter (fun i => i < n)
  | g :: rg, T =>
    if n + rg.length ∈ T then
      insert (n + rg.length) (dep n rg (T.erase (n + rg.length) ∪ (eff g).toFinset))
    else dep n rg T

/-- The wires of the NOT gates. -/
def notW (n : ℕ) : List Gate → Finset ℕ
  | [] => ∅
  | g :: rg => if isNot g = true then insert (n + rg.length) (notW n rg) else notW n rg

theorem notW_range (n : ℕ) (rg : List Gate) : ∀ v ∈ notW n rg, n ≤ v ∧ v < n + rg.length := by
  induction rg with
  | nil => intro v hv; simp [notW] at hv
  | cons g rg ih =>
    intro v hv
    simp only [notW] at hv
    split at hv
    · rcases Finset.mem_insert.mp hv with rfl | h
      · simp
      · have := ih v h
        simp only [List.length_cons]; omega
    · have := ih v hv
      simp only [List.length_cons]; omega

theorem dep_le (n : ℕ) (rg : List Gate) :
    ∀ T : Finset ℕ, ∀ v ∈ dep n rg T, ∃ w ∈ T, v ≤ w ∧ w < n + rg.length := by
  induction rg with
  | nil =>
    intro T v hv
    simp only [dep, Finset.mem_filter] at hv
    exact ⟨v, hv.1, le_refl _, by simpa using hv.2⟩
  | cons g rg ih =>
    intro T v hv
    simp only [dep] at hv
    by_cases h0 : n + rg.length ∈ T
    · rw [ite_eq_left h0] at hv
      rcases Finset.mem_insert.mp hv with rfl | h
      · exact ⟨_, h0, le_refl _, by simp⟩
      · obtain ⟨w, hw, hvw, hwl⟩ := ih _ v h
        exact ⟨n + rg.length, h0, by omega, by simp⟩
    · rw [ite_eq_right h0] at hv
      obtain ⟨w, hw, hvw, hwl⟩ := ih _ v hv
      exact ⟨w, hw, hvw, by simp only [List.length_cons]; omega⟩

theorem dep_lt (n : ℕ) (rg : List Gate) (T : Finset ℕ) (v : ℕ) (hv : v ∈ dep n rg T) :
    v < n + rg.length := by
  obtain ⟨w, _, h1, h2⟩ := dep_le n rg T v hv
  omega

theorem eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ i ∈ eff g, f i = f' i) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  obtain ⟨op, ins⟩ := g
  by_cases hn : isNot ⟨op, ins⟩ = true
  · cases op <;> simp [isNot] at hn
    cases ins with
    | nil => rfl
    | cons a l =>
      have := h a (by simp [eff, isNot])
      simp [GateOp.eval, this]
  · have h' : ins.map f = ins.map f' :=
      List.map_congr_left (fun i hi => h i (by simpa [eff, hn] using hi))
    show op.eval (ins.map f) = op.eval (ins.map f')
    rw [h']

theorem val_congr (n : ℕ) (x y : ℕ → Bool) (rg : List Gate) :
    ∀ T : Finset ℕ, (∀ i ∈ dep n rg T, i < n → x i = y i) →
      ∀ w ∈ T, val n x rg w = val n y rg w := by
  induction rg with
  | nil =>
    intro T h w hw
    simp only [val]
    by_cases hlt : w < n
    · rw [ite_eq_left hlt, ite_eq_left hlt]
      exact h w (by simp [dep, hw, hlt]) hlt
    · rw [ite_eq_right hlt, ite_eq_right hlt]
  | cons g rg ih =>
    intro T h w hw
    simp only [dep] at h
    by_cases h0 : n + rg.length ∈ T
    · rw [ite_eq_left h0] at h
      have ih' := ih (T.erase (n + rg.length) ∪ (eff g).toFinset)
        (fun i hi => h i (Finset.mem_insert_of_mem hi))
      simp only [val]
      by_cases hw0 : w = n + rg.length
      · rw [ite_eq_left hw0, ite_eq_left hw0]
        exact eval_congr g _ _ (fun i hi => ih' i (by simp [hi]))
      · rw [ite_eq_right hw0, ite_eq_right hw0]
        exact ih' w (by simp [hw, hw0])
    · rw [ite_eq_right h0] at h
      have hw0 : w ≠ n + rg.length := fun e => h0 (e ▸ hw)
      simp only [val, ite_eq_right hw0]
      exact ih T h w hw

theorem eval_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (f f' : ℕ → Bool)
    (h : ∀ i ∈ g.inputs, f i = true → f' i = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  obtain ⟨op, ins⟩ := g
  simp only at hop h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    intro H i hi
    exact h i hi (H i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    rintro ⟨i, hi, H⟩
    exact ⟨i, hi, h i hi H⟩

theorem isNot_iff (g : Gate) : isNot g = true ↔ g.op = GateOp.not := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp [isNot]

theorem val_mono (n : ℕ) (x y : ℕ → Bool) (hxy : ∀ i, x i = true → y i = true) (rg : List Gate)
    (hops : ∀ g ∈ rg, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    ∀ T : Finset ℕ, (∀ v ∈ dep n rg T, v ∈ notW n rg → val n x rg v = val n y rg v) →
      ∀ w ∈ T, val n x rg w = true → val n y rg w = true := by
  induction rg with
  | nil =>
    intro T _ w _
    simp only [val]
    by_cases hlt : w < n
    · rw [ite_eq_left hlt, ite_eq_left hlt]; exact hxy w
    · rw [ite_eq_right hlt, ite_eq_right hlt]; exact id
  | cons g rg ih =>
    intro T H w hw
    have ih := ih (fun g' hg' => hops g' (List.mem_cons_of_mem _ hg'))
    have hg := hops g (by simp)
    have hsub : ∀ v, v ∈ notW n rg → v ∈ notW n (g :: rg) := by
      intro v hv
      simp only [notW]
      split
      · exact Finset.mem_insert_of_mem hv
      · exact hv
    by_cases h0 : n + rg.length ∈ T
    · have hD : dep n (g :: rg) T
          = insert (n + rg.length) (dep n rg (T.erase (n + rg.length) ∪ (eff g).toFinset)) := by
        simp only [dep, ite_eq_left h0]
      have ih' := ih (T.erase (n + rg.length) ∪ (eff g).toFinset) (fun v hv hv' => by
        have hlt := dep_lt n rg _ v hv
        have e := H v (by rw [hD]; exact Finset.mem_insert_of_mem hv) (hsub v hv')
        simpa only [val, ite_eq_right (Nat.ne_of_lt hlt)] using e)
      by_cases hw0 : w = n + rg.length
      · subst hw0
        rcases hg with hg | hg | hg
        · simp only [val, ite_true]
          refine eval_mono g (Or.inl hg) _ _ (fun i hi => ih' i ?_)
          have : isNot g = false := by
            cases h : isNot g
            · rfl
            · rw [isNot_iff, hg] at h; cases h
          simp [eff, this, hi]
        · simp only [val, ite_true]
          refine eval_mono g (Or.inr hg) _ _ (fun i hi => ih' i ?_)
          have : isNot g = false := by
            cases h : isNot g
            · rfl
            · rw [isNot_iff, hg] at h; cases h
          simp [eff, this, hi]
        · have e := H (n + rg.length) (by rw [hD]; exact Finset.mem_insert_self _ _)
            (by simp [notW, (isNot_iff g).mpr hg])
          rw [e]; exact id
      · simp only [val, ite_eq_right hw0]
        exact ih' w (by simp [hw, hw0])
    · have hD : dep n (g :: rg) T = dep n rg T := by simp only [dep, ite_eq_right h0]
      have hw0 : w ≠ n + rg.length := fun e => h0 (e ▸ hw)
      simp only [val, ite_eq_right hw0]
      refine ih T (fun v hv hv' => ?_) w hw
      have hlt := dep_lt n rg _ v hv
      have e := H v (by rw [hD]; exact hv) (hsub v hv')
      simpa only [val, ite_eq_right (Nat.ne_of_lt hlt)] using e

theorem getD_snoc (L : List Bool) (a : Bool) (w : ℕ) :
    (L ++ [a]).getD w false = if w = L.length then a else L.getD w false := by
  rcases lt_trichotomy w L.length with h | h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, Nat.ne_of_lt h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · have h1 : ¬ w = L.length := by omega
    have h2 : L.length ≤ w := by omega
    have h3 : (L ++ [a]).length ≤ w := by simp; omega
    simp [List.getD_eq_getElem?_getD, h1, List.getElem?_eq_none h2, List.getElem?_eq_none h3]

/-- The input with wires `a` and `b` on. -/
def pt (a b : ℕ) : ℕ → Bool := fun i => decide (i = a) || decide (i = b)

theorem oneEach_getD (N : ℕ) (u v : Fin N) :
    (fun i => (oneEach u v).getD i false) = pt u.val (N + v.val) := by
  funext i
  unfold oneEach pt
  by_cases h : i < N
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h)]
    have h1 : i ≠ N + v.val := by omega
    simp [h, h1, Fin.ext_iff]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simpa using h)]
    have h1 : i ≠ u.val := by have := u.isLt; omega
    by_cases h2 : i - N < N
    · simp [h2, h1, Fin.ext_iff]; omega
    · have h3 : i ≠ N + v.val := by have := v.isLt; omega
      simp [h2, h1, h3]

theorem cnt (N : ℕ) (D : Finset ℕ) (f : Fin N → ℕ) (hf : Function.Injective f)
    (h : ∀ a a' : Fin N, f a ∉ D → f a' ∉ D → a = a') :
    N ≤ ((Finset.univ.image f) ∩ D).card + 1 := by
  have h1 : (Finset.univ.image f).card = N := by
    rw [Finset.card_image_of_injective _ hf]; simp
  have h2 : ((Finset.univ.image f) \ D).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_univ, true_and] at hi hj
    obtain ⟨⟨a, rfl⟩, ha⟩ := hi
    obtain ⟨⟨b, rfl⟩, hb⟩ := hj
    rw [h a b ha hb]
  have h3 := Finset.card_sdiff_add_card_inter (Finset.univ.image f) D
  omega

theorem cnt0 (N : ℕ) (D : Finset ℕ) (f : Fin N → ℕ) (hf : Function.Injective f)
    (h : ∀ a : Fin N, f a ∈ D) :
    N ≤ ((Finset.univ.image f) ∩ D).card := by
  have h1 : (Finset.univ.image f).card = N := by
    rw [Finset.card_image_of_injective _ hf]; simp
  have h2 : (Finset.univ.image f) ∩ D = Finset.univ.image f := by
    rw [Finset.inter_eq_left]
    intro i hi
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hi
    obtain ⟨a, rfl⟩ := hi
    exact h a
  rw [h2, h1]

theorem supp_ge (N : ℕ) (D : Finset ℕ) :
    ((Finset.univ.image (fun a : Fin N => a.val)) ∩ D).card
      + ((Finset.univ.image (fun a : Fin N => N + a.val)) ∩ D).card
      ≤ (D.filter (fun i => i < N + N)).card := by
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_image, Finset.mem_univ,
      true_and, Finset.mem_filter] at hi ⊢
    rcases hi with ⟨⟨a, rfl⟩, h⟩ | ⟨⟨a, rfl⟩, h⟩
    · exact ⟨h, by have := a.isLt; omega⟩
    · exact ⟨h, by have := a.isLt; omega⟩
  · rw [Finset.disjoint_left]
    intro i hi hj
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and] at hi hj
    obtain ⟨⟨a, rfl⟩, _⟩ := hi
    obtain ⟨⟨b, hb⟩, _⟩ := hj
    have := a.isLt
    omega

theorem dep_count (n : ℕ) (rg : List Gate) (hfan : ∀ g ∈ rg, g.inputs.length ≤ 2) :
    ∀ T : Finset ℕ, ((dep n rg T).filter (fun i => i < n)).card + (dep n rg T ∩ notW n rg).card
      ≤ T.card + ((dep n rg T).filter (fun i => n ≤ i)).card := by
  induction rg with
  | nil =>
    intro T
    simp only [dep, notW, Finset.inter_empty, Finset.card_empty, Nat.add_zero]
    exact le_trans (Finset.card_le_card (Finset.filter_subset _ _))
      (le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (Nat.le_add_right _ _))
  | cons g rg ih =>
    intro T
    have ih := ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
    have hg := hfan g (by simp)
    have hnotN : n + rg.length ∉ notW n rg := fun h => by
      have := (notW_range n rg _ h).2
      omega
    by_cases h0 : n + rg.length ∈ T
    · have hD : dep n (g :: rg) T
          = insert (n + rg.length) (dep n rg (T.erase (n + rg.length) ∪ (eff g).toFinset)) := by
        simp only [dep, ite_eq_left h0]
      have ihT := ih (T.erase (n + rg.length) ∪ (eff g).toFinset)
      have hT'card : (T.erase (n + rg.length) ∪ (eff g).toFinset).card + 1
          ≤ T.card + (eff g).length := by
        have h1 := Finset.card_union_le (T.erase (n + rg.length)) (eff g).toFinset
        have h2 := Finset.card_erase_of_mem h0
        have h3 := List.toFinset_card_le (eff g)
        have h4 : 0 < T.card := Finset.card_pos.mpr ⟨_, h0⟩
        omega
      generalize T.erase (n + rg.length) ∪ (eff g).toFinset = T' at hD ihT hT'card
      have hnot0 : n + rg.length ∉ dep n rg T' := fun h => by
        have := dep_lt n rg _ _ h
        omega
      have e1 : (insert (n + rg.length) (dep n rg T')).filter (fun i => i < n)
          = (dep n rg T').filter (fun i => i < n) := by
        rw [Finset.filter_insert, ite_eq_right (by omega)]
      have e2 : ((insert (n + rg.length) (dep n rg T')).filter (fun i => n ≤ i)).card
          = ((dep n rg T').filter (fun i => n ≤ i)).card + 1 := by
        rw [Finset.filter_insert, ite_eq_left (by omega),
          Finset.card_insert_of_notMem (by simp [hnot0])]
      rw [hD, e1, e2]
      by_cases hn : isNot g = true
      · have e3 : notW n (g :: rg) = insert (n + rg.length) (notW n rg) := by
          simp only [notW, ite_eq_left hn]
        have e4 : (insert (n + rg.length) (dep n rg T')
            ∩ insert (n + rg.length) (notW n rg)).card = (dep n rg T' ∩ notW n rg).card + 1 := by
          rw [← Finset.insert_inter_distrib, Finset.card_insert_of_notMem (by simp [hnot0])]
        have e5 : (eff g).length ≤ 1 := by
          simp only [eff, ite_eq_left hn, List.length_take]
          omega
        rw [e3, e4]
        omega
      · have e3 : notW n (g :: rg) = notW n rg := by
          simp only [notW, ite_eq_right hn]
        have e4 : insert (n + rg.length) (dep n rg T') ∩ notW n rg
            = dep n rg T' ∩ notW n rg := by
          rw [Finset.insert_inter_of_notMem hnotN]
        have e5 : (eff g).length ≤ 2 := by
          simp only [eff, ite_eq_right hn]
          exact hg
        rw [e3, e4]
        omega
    · have hD : dep n (g :: rg) T = dep n rg T := by simp only [dep, ite_eq_right h0]
      have e : dep n rg T ∩ notW n (g :: rg) = dep n rg T ∩ notW n rg := by
        ext v
        simp only [Finset.mem_inter, notW]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          split at h2
          · rcases Finset.mem_insert.mp h2 with rfl | h
            · exact absurd (dep_lt n rg _ _ h1) (by omega)
            · exact h
          · exact h2
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          split
          · exact Finset.mem_insert_of_mem h2
          · exact h2
      rw [hD, e]
      exact ih T

theorem cone_le (n : ℕ) (rg : List Gate) (T : Finset ℕ) :
    ((dep n rg T).filter (fun i => n ≤ i)).card ≤ rg.length := by
  have h : (dep n rg T).filter (fun i => n ≤ i) ⊆ Finset.Ico n (n + rg.length) := by
    intro i hi
    simp only [Finset.mem_filter] at hi
    have := dep_lt n rg T i hi.1
    simp only [Finset.mem_Ico]
    omega
  have h2 := Finset.card_le_card h
  simp only [Nat.card_Ico] at h2
  omega

theorem wires_val (n : ℕ) (X : List Bool) (hX : X.length = n) (rg : List Gate) :
    (rg.reverse.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      X).length = n + rg.length ∧
    ∀ w, (rg.reverse.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      X).getD w false = val n (fun i => X.getD i false) rg w := by
  induction rg with
  | nil =>
    refine ⟨by simpa using hX, fun w => ?_⟩
    simp only [List.reverse_nil, List.foldl_nil, val]
    by_cases h : w < n
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]
      exact List.getD_eq_default _ _ (by omega)
  | cons g rg ih =>
    obtain ⟨ihl, ihv⟩ := ih
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by simp only [List.length_append, List.length_cons, List.length_nil, ihl]; omega,
      fun w => ?_⟩
    rw [getD_snoc, ihl]
    simp only [val, ihv]

theorem eval_val (C : Circuit) (X : List Bool) :
    C.eval X = val X.length (fun i => X.getD i false) C.gates.reverse C.output := by
  have h := (wires_val X.length X rfl C.gates.reverse).2 C.output
  rw [List.reverse_reverse] at h
  exact h

theorem rep_val (N : ℕ) (A : Fin N → Fin N → Bool) (C : Circuit) (hR : Represents A C)
    (u v : Fin N) : val (N + N) (pt u.val (N + v.val)) C.gates.reverse C.output = A u v := by
  have h := hR u v
  rw [eval_val, oneEach_getD] at h
  have hl : (oneEach u v).length = N + N := by simp [oneEach]
  rw [hl] at h
  exact h

theorem key (n : ℕ) (rg : List Gate)
    (hops : ∀ g ∈ rg, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) (o : ℕ)
    (x1 x0 x2 : ℕ → Bool)
    (h1 : ∀ i ∈ dep n rg {o}, i < n → x1 i = x0 i)
    (h2 : ∀ i, x0 i = true → x2 i = true)
    (h3 : ∀ v ∈ dep n rg {o}, v ∈ notW n rg → val n x0 rg v = val n x2 rg v) :
    val n x1 rg o = true → val n x2 rg o = true := by
  intro h
  rw [val_congr n x1 x0 rg {o} h1 o (Finset.mem_singleton_self o)] at h
  exact val_mono n x0 x2 h2 rg hops {o} h3 o (Finset.mem_singleton_self o) h

theorem short (N : ℕ) (hN : 2 ≤ N) (A : Fin N → Fin N → Bool) (C : Circuit) (hC : FanInTwo C)
    (hR : Represents A C)
    (hrow : ∀ a a' : Fin N, a ≠ a' → ∃ v, A a v ≠ A a' v)
    (hcol : ∀ b b' : Fin N, b ≠ b' → ∃ u, A u b ≠ A u b')
    (hM : ∀ a : Fin N, ∃ u v, A a v = true ∧ A u v = false) :
    2 * N - 2 ≤ C.size := by
  have hval := rep_val N A C hR
  have hops : ∀ g ∈ C.gates.reverse, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    intro g hg
    have := (hC g (List.mem_reverse.mp hg)).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  have hfan : ∀ g ∈ C.gates.reverse, g.inputs.length ≤ 2 :=
    fun g hg => (hC g (List.mem_reverse.mp hg)).2
  have hsize : C.gates.reverse.length = C.size := by simp [Circuit.size]
  generalize C.gates.reverse = rg at hval hops hfan hsize
  generalize C.output = o at hval
  have hF2 := dep_count (N + N) rg hfan {o}
  have hcone := cone_le (N + N) rg {o}
  have hsupp := supp_ge N (dep (N + N) rg {o})
  rw [Finset.card_singleton] at hF2
  have hinj1 : Function.Injective (fun a : Fin N => a.val) := fun a b h => Fin.ext h
  have hinj2 : Function.Injective (fun a : Fin N => N + a.val) :=
    fun a b h => Fin.ext (by simpa using h)
  have hrowD : ∀ a a' : Fin N, a.val ∉ dep (N + N) rg {o} → a'.val ∉ dep (N + N) rg {o}
      → a = a' := by
    intro a a' ha ha'
    by_contra hne
    obtain ⟨v, hv⟩ := hrow a a' hne
    apply hv
    rw [← hval, ← hval]
    refine val_congr _ _ _ rg {o} (fun i hi _ => ?_) o (Finset.mem_singleton_self o)
    have h1 : i ≠ a.val := fun e => ha (e ▸ hi)
    have h2 : i ≠ a'.val := fun e => ha' (e ▸ hi)
    simp [pt, h1, h2]
  have hcolD : ∀ b b' : Fin N, N + b.val ∉ dep (N + N) rg {o} → N + b'.val ∉ dep (N + N) rg {o}
      → b = b' := by
    intro b b' hb hb'
    by_contra hne
    obtain ⟨u, hu⟩ := hcol b b' hne
    apply hu
    rw [← hval, ← hval]
    refine val_congr _ _ _ rg {o} (fun i hi _ => ?_) o (Finset.mem_singleton_self o)
    have h1 : i ≠ N + b.val := fun e => hb (e ▸ hi)
    have h2 : i ≠ N + b'.val := fun e => hb' (e ▸ hi)
    simp [pt, h1, h2]
  have hc := cnt N (dep (N + N) rg {o}) _ hinj2 hcolD
  by_cases hnn : dep (N + N) rg {o} ∩ notW (N + N) rg = ∅
  · have hall : ∀ a : Fin N, a.val ∈ dep (N + N) rg {o} := by
      intro a
      by_contra ha
      obtain ⟨u, v, hA1, hA2⟩ := hM a
      have hk := key (N + N) rg hops o (pt a.val (N + v.val)) (pt (N + v.val) (N + v.val))
        (pt u.val (N + v.val))
        (fun i hi _ => by
          have h1 : i ≠ a.val := fun e => ha (e ▸ hi)
          simp [pt, h1])
        (fun i => by
          simp only [pt, Bool.or_self, Bool.or_eq_true]
          exact fun h => Or.inr h)
        (fun w hw hw' => by
          have : w ∈ dep (N + N) rg {o} ∩ notW (N + N) rg := Finset.mem_inter.mpr ⟨hw, hw'⟩
          rw [hnn] at this
          simp at this)
      rw [hval, hval] at hk
      have := hk hA1
      rw [hA2] at this
      exact Bool.false_ne_true this
    have hr := cnt0 N (dep (N + N) rg {o}) _ hinj1 hall
    rw [hnn, Finset.card_empty] at hF2
    omega
  · have hr := cnt N (dep (N + N) rg {o}) _ hinj1 hrowD
    have hpos : 0 < (dep (N + N) rg {o} ∩ notW (N + N) rg).card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hnn)
    omega

theorem exists_ne (N : ℕ) (hN : 2 ≤ N) (a : Fin N) : ∃ u : Fin N, u ≠ a := by
  by_cases h : a.val = 0
  · exact ⟨⟨1, by omega⟩, fun e => by rw [Fin.ext_iff] at e; simp only at e; omega⟩
  · exact ⟨⟨0, by omega⟩, fun e => by rw [Fin.ext_iff] at e; simp only at e; omega⟩

theorem main_thm : ∀ (N : ℕ), 2 ≤ N → ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents (fun u v : Fin N => decide (u ≠ v)) C → 2 * N - 2 ≤ C.size := by
  intro N hN C hC hR
  refine short N hN _ C hC hR ?_ ?_ ?_
  · intro a a' h
    exact ⟨a, by simp [Ne.symm h]⟩
  · intro b b' h
    exact ⟨b, by simp [h]⟩
  · intro a
    obtain ⟨u, hu⟩ := exists_ne N hN a
    exact ⟨u, u, by simp [Ne.symm hu], by simp⟩

end PEqualNP.Outside.L_meta_17177_aux

theorem PEqualNP.Outside.L_meta_17177 : ∀ (N : ℕ), 2 ≤ N → ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents (fun u v : Fin N => decide (u ≠ v)) C → 2 * N - 2 ≤ C.size := by
  exact PEqualNP.Outside.L_meta_17177_aux.main_thm
