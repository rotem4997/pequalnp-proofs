import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3716

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadK

def fd {α : Type} (st : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [st w g]) w

theorem fd_snoc {α : Type} (st : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    fd st (gs ++ [g]) w = fd st gs w ++ [st (fd st gs w) g] := by
  simp [fd, List.foldl_append]

theorem fd_len {α : Type} (st : List α → Gate → α) (gs : List Gate) :
    ∀ w : List α, (fd st gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [fd]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [st w g])
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem fd_keep {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) :
    ∀ (w : List α) (i : ℕ), i < w.length → (fd st gs w).getD i d = w.getD i d := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [st w g]) i (by simp; omega)
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem fd_take {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k i : ℕ) (hi : i < X.length + k) (hk : k ≤ gs.length) :
    (fd st gs X).getD i d = (fd st (gs.take k) X).getD i d := by
  have h1 : fd st gs X = fd st (gs.drop k) (fd st (gs.take k) X) := by
    unfold fd
    rw [← List.foldl_append, List.take_append_drop]
  rw [h1]
  exact fd_keep st d _ _ i (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; exact hi)

theorem fd_gate {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k : ℕ) (hk : k < gs.length) :
    (fd st gs X).getD (X.length + k) d = st (fd st (gs.take k) X) gs[k] := by
  rw [fd_take st d gs X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, fd_snoc]
  have hl : (fd st (gs.take k) X).length = X.length + k := by
    rw [fd_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [← hl]
  simp [List.getD_eq_getElem?_getD]

def stB (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def val (gs : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (fd stB gs (List.ofFn x)).getD w false

theorem eval_eq (C : Circuit) {n : ℕ} (x : Fin n → Bool) :
    circuitFun n C x = val C.gates C.output x := rfl

theorem iv_eq (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gs.length)
    (i : ℕ) : (fd stB (gs.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gs i x = true := by
  by_cases hi : i < n + k
  · rw [val, fd_take stB false gs (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.and) :
    val gs (n + k) x = true ↔ ∀ i ∈ gs[k].inputs, i < n + k ∧ val gs i x = true := by
  have := fd_gate stB false gs (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this]
  show (gs[k].op.eval _) = true ↔ _
  rw [hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gs x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gs x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.or) :
    val gs (n + k) x = true ↔ ∃ i ∈ gs[k].inputs, i < n + k ∧ val gs i x = true := by
  have := fd_gate stB false gs (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this]
  show (gs[k].op.eval _) = true ↔ _
  rw [hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gs x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gs x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gs w x = x ⟨w, hw⟩ := by
  rw [val, fd_keep stB false gs _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gs.length ≤ w) : val gs w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [fd_len]; simpa using hw)]

def Legal (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def RB (n : ℕ) (gs : List Gate) : Prop :=
  ∀ k g, gs[k]? = some g → ∀ i ∈ g.inputs, i < n + k

theorem val_mono (gs : List Gate) {n : ℕ} (legal : Legal gs)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
    ∀ w, val gs w x = true → val gs w x' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input gs _ w hwn] at h ⊢
      exact hx _ h
    · by_cases hbig : n + gs.length ≤ w
      · rw [val_big gs x w hbig] at h
        exact Bool.noConfusion h
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hi : k < gs.length := by omega
        rcases (legal gs[k] (List.getElem_mem hi)).1 with ha | ho
        · apply (val_and gs x' k hi ha).2
          intro j hj
          obtain ⟨hjlt, hjv⟩ := (val_and gs x k hi ha).1 h j hj
          exact ⟨hjlt, ih j (by omega) hjv⟩
        · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gs x k hi ho).1 h
          exact (val_or gs x' k hi ho).2 ⟨j, hj, hjlt, ih j (by omega) hv⟩

def stL2 (op : GateOp) (ins : List (Bool × Bool)) : Bool × Bool :=
  match op with
  | GateOp.or => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
      (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

def stL (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  stL2 g.op (g.inputs.map fun i => w.getD i (false, false))

def ini (isL : ℕ → Bool) (xs : List Bool) : List (Bool × Bool) :=
  (xs.zipIdx).map fun (b, i) => if isL i then (false, b) else (b, false)

def lpv (gs : List Gate) (isL : ℕ → Bool) (xs : List Bool) (w : ℕ) : Bool × Bool :=
  (fd stL gs (ini isL xs)).getD w (false, false)

theorem lp_eq (C : Circuit) (isL : ℕ → Bool) (xs : List Bool) (w : ℕ) :
    (linearParts C isL xs).getD w (false, false) = lpv C.gates isL xs w := rfl

theorem ini_len (isL : ℕ → Bool) (xs : List Bool) : (ini isL xs).length = xs.length := by
  simp [ini]

theorem lp_input (gs : List Gate) (isL : ℕ → Bool) (xs : List Bool) (w : ℕ)
    (hw : w < xs.length) :
    lpv gs isL xs w = if isL w then (false, xs.getD w false) else (xs.getD w false, false) := by
  rw [lpv, fd_keep stL (false, false) gs _ w (by rw [ini_len]; exact hw)]
  simp [ini, List.getD_eq_getElem?_getD, hw]

theorem lp_big (gs : List Gate) (isL : ℕ → Bool) (xs : List Bool) (w : ℕ)
    (hw : xs.length + gs.length ≤ w) : lpv gs isL xs w = (false, false) := by
  rw [lpv, List.getD_eq_default _ _ (by rw [fd_len, ini_len]; exact hw)]

theorem lp_gate (gs : List Gate) (isL : ℕ → Bool) (xs : List Bool) (k : ℕ)
    (hk : k < gs.length) (hin : ∀ i ∈ gs[k].inputs, i < xs.length + k) :
    lpv gs isL xs (xs.length + k) = stL2 gs[k].op (gs[k].inputs.map (lpv gs isL xs)) := by
  have h := fd_gate stL (false, false) gs (ini isL xs) k hk
  rw [ini_len] at h
  rw [lpv, h]
  show stL2 gs[k].op _ = _
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [lpv]
  exact (fd_take stL (false, false) gs (ini isL xs) k i (by rw [ini_len]; exact hin i hi)
    (Nat.le_of_lt hk)).symm

theorem len2 {α : Type} (l : List α) (h : l.length ≤ 2) :
    l = [] ∨ (∃ a, l = [a]) ∨ ∃ a b, l = [a, b] := by
  match l, h with
  | [], _ => exact Or.inl rfl
  | [a], _ => exact Or.inr (Or.inl ⟨a, rfl⟩)
  | [a, b], _ => exact Or.inr (Or.inr ⟨a, b, rfl⟩)
  | _ :: _ :: _ :: _, h => simp at h

def sib (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (g : Gate) (slot : ℕ) : Prop :=
  g.op = GateOp.or ∨ (g.op = GateOp.and ∧
    ∀ m u, g.inputs[m]? = some u → m ≠ slot → val gs u x = true)

def Dn (gs : List Gate) (o : ℕ) {n : ℕ} (x : Fin n → Bool) : ℕ → ℕ → Prop
  | 0, w => w = o
  | t + 1, w => w = o ∨ ∃ k g slot, gs[k]? = some g ∧ g.inputs[slot]? = some w ∧
      sib gs x g slot ∧ Dn gs o x t (n + k)

def D (gs : List Gate) (o : ℕ) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Prop :=
  ∃ t, Dn gs o x t w

theorem Dn_succ (gs : List Gate) (o : ℕ) {n : ℕ} (x : Fin n → Bool) (t w : ℕ) :
    Dn gs o x (t + 1) w ↔ (w = o ∨ ∃ k g slot, gs[k]? = some g ∧ g.inputs[slot]? = some w ∧
      sib gs x g slot ∧ Dn gs o x t (n + k)) := Iff.rfl

theorem D_out (gs : List Gate) (o : ℕ) {n : ℕ} (x : Fin n → Bool) : D gs o x o := ⟨0, rfl⟩

theorem D_step (gs : List Gate) (o : ℕ) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (g : Gate)
    (slot w : ℕ) (hg : gs[k]? = some g) (hs : g.inputs[slot]? = some w)
    (hsib : sib gs x g slot) (hd : D gs o x (n + k)) : D gs o x w := by
  obtain ⟨t, ht⟩ := hd
  exact ⟨t + 1, Or.inr ⟨k, g, slot, hg, hs, hsib, ht⟩⟩

theorem sib_mono (gs : List Gate) {n : ℕ} (legal : Legal gs)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) (g : Gate) (slot : ℕ) :
    sib gs x g slot → sib gs x' g slot := by
  rintro (h | ⟨h, hall⟩)
  · exact Or.inl h
  · exact Or.inr ⟨h, fun m u hm hms => val_mono gs legal x x' hx u (hall m u hm hms)⟩

theorem Dn_mono (gs : List Gate) (o : ℕ) {n : ℕ} (legal : Legal gs)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
    ∀ t w, Dn gs o x t w → Dn gs o x' t w := by
  intro t
  induction t with
  | zero => intro w h; exact h
  | succ t ih =>
    intro w h
    rcases (Dn_succ gs o x t w).1 h with h | ⟨k, g, slot, hg, hs, hsib, hd⟩
    · exact Or.inl h
    · exact Or.inr ⟨k, g, slot, hg, hs, sib_mono gs legal x x' hx g slot hsib, ih _ hd⟩

theorem D_mono (gs : List Gate) (o : ℕ) {n : ℕ} (legal : Legal gs)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) (w : ℕ) :
    D gs o x w → D gs o x' w := by
  rintro ⟨t, ht⟩
  exact ⟨t, Dn_mono gs o legal x x' hx t w ht⟩

theorem snd (gs : List Gate) (o : ℕ) {n : ℕ} (legal : Legal gs) (hrb : RB n gs)
    (x z : Fin n → Bool) (hx : ∀ v, x v = true → z v = true) :
    ∀ t w, Dn gs o x t w → val gs w z = true → val gs o z = true := by
  intro t
  induction t with
  | zero => intro w h hv; rw [← (show w = o from h)]; exact hv
  | succ t ih =>
    intro w h hv
    rcases (Dn_succ gs o x t w).1 h with h | ⟨k, g, slot, hg, hs, hsib, hd⟩
    · rw [← h]; exact hv
    · apply ih (n + k) hd
      obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 hg
      have hwm : w ∈ gs[k].inputs := List.mem_of_getElem? hs
      rcases hsib with hor | ⟨hand, hall⟩
      · exact (val_or gs z k hk hor).2 ⟨w, hwm, hrb k _ hg w hwm, hv⟩
      · apply (val_and gs z k hk hand).2
        intro i hi
        obtain ⟨m, hm⟩ := List.getElem?_of_mem hi
        refine ⟨hrb k _ hg i hi, ?_⟩
        by_cases hms : m = slot
        · subst hms
          rw [hs] at hm
          cases hm
          exact hv
        · exact val_mono gs legal x z hx i (hall m i hm hms)

def sg (n : ℕ) (p : ℕ) : Fin n → Bool := fun i => decide (i.val = p)

def off (n : ℕ) (isL : ℕ → Bool) (R : ℕ → ℕ → Bool) (l : ℕ) : Fin n → Bool :=
  fun i => !isL i.val && !R i.val l

theorem sg_le_off (n : ℕ) (isL : ℕ → Bool) (R : ℕ → ℕ → Bool) (r l : ℕ)
    (hp : isL r = false) (hr : R r l = false) :
    ∀ v, sg n r v = true → off n isL R l v = true := by
  intro v hv
  have hv' : v.val = r := by simpa [sg] using hv
  simp [off, hv', hp, hr]

def Tg {n : ℕ} (isL : ℕ → Bool) (R : ℕ → ℕ → Bool) (G H : (Fin n → Bool) → Prop)
    (p l : ℕ) : Prop :=
  ¬ G (off n isL R l) ∧
  (∃ r1 r2, r1 ≠ r2 ∧ isL r1 = false ∧ isL r2 = false ∧ G (sg n r1) ∧ G (sg n r2)) ∧
  isL p = false ∧ H (sg n p) ∧ ∀ r, isL r = false → H (sg n r) → r = p

theorem Tg_inj {n : ℕ} (isL : ℕ → Bool) (R : ℕ → ℕ → Bool)
    (h4 : ∀ a a' b b', R a b = true → R a' b = true → R a b' = true → R a' b' = true →
      a ≠ a' → b = b')
    (G H : (Fin n → Bool) → Prop)
    (hG : ∀ x x' : Fin n → Bool, (∀ v, x v = true → x' v = true) → G x → G x')
    (p l p' l' : ℕ) : Tg isL R G H p l → Tg isL R G H p' l' → p = p' ∧ l = l' := by
  rintro ⟨hn, ⟨r1, r2, hne, h1, h2, g1, g2⟩, hp, hH, hu⟩ ⟨hn', _, hp', hH', hu'⟩
  have e1 : p' = p := hu p' hp' hH'
  have inl : ∀ r l0, isL r = false → G (sg n r) → ¬ G (off n isL R l0) → R r l0 = true := by
    intro r l0 hr hg hng
    by_contra hc
    exact hng (hG _ _ (sg_le_off n isL R r l0 hr (by simpa using hc)) hg)
  exact ⟨e1.symm, h4 r1 r2 l l' (inl r1 l h1 g1 hn) (inl r2 l h2 g2 hn) (inl r1 l' h1 g1 hn')
    (inl r2 l' h2 g2 hn') hne⟩

def T1 (gs : List Gate) (o n : ℕ) (isL : ℕ → Bool) (R : ℕ → ℕ → Bool)
    (k slot p l : ℕ) : Prop :=
  ∃ g u, gs[k]? = some g ∧ g.inputs[slot]? = some u ∧
    Tg (n := n) isL R (fun x => D gs o x u) (fun x => sib gs x g slot ∧ D gs o x (n + k)) p l

def T2 (gs : List Gate) (n : ℕ) (isL : ℕ → Bool) (R : ℕ → ℕ → Bool)
    (k slot p l : ℕ) : Prop :=
  ∃ g a, gs[k]? = some g ∧ g.inputs[slot]? = some a ∧
    Tg (n := n) isL R (fun x => val gs (n + k) x = true) (fun x => val gs a x = true) p l

def TT (gs : List Gate) (o n : ℕ) (isL : ℕ → Bool) (R : ℕ → ℕ → Bool)
    (e : ℕ × ℕ) (t : (ℕ × ℕ) × Bool) : Prop :=
  (t.2 = true ∧ T1 gs o n isL R t.1.1 t.1.2 e.1 e.2) ∨
  (t.2 = false ∧ T2 gs n isL R t.1.1 t.1.2 e.1 e.2)

theorem TT_inj (gs : List Gate) (o n : ℕ) (isL : ℕ → Bool) (R : ℕ → ℕ → Bool)
    (legal : Legal gs)
    (h4 : ∀ a a' b b', R a b = true → R a' b = true → R a b' = true → R a' b' = true →
      a ≠ a' → b = b')
    (e e' : ℕ × ℕ) (t : (ℕ × ℕ) × Bool) :
    TT gs o n isL R e t → TT gs o n isL R e' t → e = e' := by
  rintro (⟨hb, g, u, hg, hu, hT⟩ | ⟨hb, g, u, hg, hu, hT⟩)
    (⟨hb', g', u', hg', hu', hT'⟩ | ⟨hb', g', u', hg', hu', hT'⟩)
  · rw [hg] at hg'; cases hg'
    rw [hu] at hu'; cases hu'
    obtain ⟨h1, h2⟩ := Tg_inj isL R h4 _ _
      (fun x x' hx hd => D_mono gs o legal x x' hx _ hd) _ _ _ _ hT hT'
    exact Prod.ext h1 h2
  · rw [hb] at hb'; cases hb'
  · rw [hb] at hb'; cases hb'
  · rw [hg] at hg'; cases hg'
    rw [hu] at hu'; cases hu'
    obtain ⟨h1, h2⟩ := Tg_inj isL R h4 _ _
      (fun x x' hx hd => val_mono gs legal x x' hx _ hd) _ _ _ _ hT hT'
    exact Prod.ext h1 h2

theorem dc (gs : List Gate) (n : ℕ) (isL : ℕ → Bool) (R : ℕ → ℕ → Bool) (legal : Legal gs)
    (l p : ℕ) (hp : isL p = false) :
    ∀ s r, r ≠ p → isL r = false → val gs s (off n isL R l) = false →
      val gs s (sg n p) = true → val gs s (sg n r) = true →
      ∃ k slot, k < gs.length ∧ slot < 2 ∧ T2 gs n isL R k slot p l := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro r hrp hr hoff hvp hvr
    by_cases hsn : s < n
    · rw [val_input gs _ s hsn] at hvp hvr
      have e1 : s = p := by simpa [sg] using hvp
      have e2 : s = r := by simpa [sg] using hvr
      exact absurd (e2.symm.trans e1) hrp
    · by_cases hbig : n + gs.length ≤ s
      · rw [val_big gs _ s hbig] at hvp
        exact Bool.noConfusion hvp
      · obtain ⟨k, rfl⟩ : ∃ k, s = n + k := ⟨s - n, by omega⟩
        have hi : k < gs.length := by omega
        rcases (legal gs[k] (List.getElem_mem hi)).1 with ha | ho
        · have h1 := (val_and gs _ k hi ha).1 hvp
          have h2 := (val_and gs _ k hi ha).1 hvr
          have h3 : ∃ i ∈ gs[k].inputs, val gs i (off n isL R l) = false := by
            by_contra hc
            have : val gs (n + k) (off n isL R l) = true :=
              (val_and gs _ k hi ha).2 (fun i him => ⟨(h1 i him).1, by
                by_contra hv
                exact hc ⟨i, him, by simpa using hv⟩⟩)
            rw [this] at hoff
            exact Bool.noConfusion hoff
          obtain ⟨i, him, hio⟩ := h3
          exact ih i (h1 i him).1 r hrp hr hio (h1 i him).2 (h2 i him).2
        · obtain ⟨i, him, hlt, hvi⟩ := (val_or gs _ k hi ho).1 hvp
          have hio : val gs i (off n isL R l) = false := by
            by_contra hv
            have : val gs (n + k) (off n isL R l) = true :=
              (val_or gs _ k hi ho).2 ⟨i, him, hlt, by simpa using hv⟩
            rw [this] at hoff
            exact Bool.noConfusion hoff
          by_cases hu : ∀ r', isL r' = false → val gs i (sg n r') = true → r' = p
          · obtain ⟨slot, hslot⟩ := List.getElem?_of_mem him
            have hsl : slot < 2 := by
              have h5 := (List.getElem?_eq_some_iff.1 hslot).1
              have h6 := (legal gs[k] (List.getElem_mem hi)).2
              omega
            refine ⟨k, slot, hi, hsl, gs[k], i, List.getElem?_eq_getElem hi, hslot, ?_,
              ⟨p, r, hrp.symm, hp, hr, hvp, hvr⟩, hp, hvi, hu⟩
            intro hc
            have hc' : val gs (n + k) (off n isL R l) = true := hc
            rw [hoff] at hc'
            exact Bool.noConfusion hc'
          · push Not at hu
            obtain ⟨r', hr', hvr', hne⟩ := hu
            exact ih i hlt r' hne hr' hio hvi hvr'

theorem uc (gs : List Gate) (o n : ℕ) (isL : ℕ → Bool) (R : ℕ → ℕ → Bool) (legal : Legal gs)
    (l p : ℕ) (hp : isL p = false) :
    ∀ t w, Dn gs o (sg n p) t w → ¬ D gs o (off n isL R l) w →
      (∃ r, r ≠ p ∧ isL r = false ∧ D gs o (sg n r) w) →
      ∃ k slot, k < gs.length ∧ slot < 2 ∧
        (T1 gs o n isL R k slot p l ∨ T2 gs n isL R k slot p l) := by
  intro t
  induction t with
  | zero =>
    intro w h hn _
    exact absurd ⟨0, h⟩ hn
  | succ t ih =>
    intro w h hn hex
    obtain ⟨r, hrp, hr, hdr⟩ := hex
    rcases (Dn_succ gs o (sg n p) t w).1 h with h0 | ⟨k, g, slot, hg, hs, hsib, hd⟩
    · exact absurd ⟨0, h0⟩ hn
    · have hk := (List.getElem?_eq_some_iff.1 hg).1
      have hsl : slot < 2 := by
        have h5 := (List.getElem?_eq_some_iff.1 hs).1
        have h6 := (legal g (List.mem_of_getElem? hg)).2
        omega
      by_cases hu : ∀ r', isL r' = false → sib gs (sg n r') g slot →
          D gs o (sg n r') (n + k) → r' = p
      · exact ⟨k, slot, hk, hsl, Or.inl ⟨g, w, hg, hs, hn,
          ⟨p, r, hrp.symm, hp, hr, ⟨t + 1, h⟩, hdr⟩, hp, ⟨hsib, ⟨t, hd⟩⟩,
          fun r' h1 h2 => hu r' h1 h2.1 h2.2⟩⟩
      · push Not at hu
        obtain ⟨r', hr', hsib', hd', hne⟩ := hu
        by_cases hgo : D gs o (off n isL R l) (n + k)
        · have hns : ¬ sib gs (off n isL R l) g slot :=
            fun hc => hn (D_step gs o _ k g slot w hg hs hc hgo)
          rcases hsib with hor | ⟨hand, hall⟩
          · exact absurd (Or.inl hor) hns
          · rcases hsib' with hor' | ⟨_, hall'⟩
            · rw [hand] at hor'; cases hor'
            · have hex2 : ∃ m u, g.inputs[m]? = some u ∧ m ≠ slot ∧
                  val gs u (off n isL R l) = false := by
                by_contra hc
                apply hns
                right
                refine ⟨hand, fun m u hm hms => ?_⟩
                by_contra hv
                exact hc ⟨m, u, hm, hms, by simpa using hv⟩
              obtain ⟨m, u, hm, hms, hvo⟩ := hex2
              obtain ⟨k2, s2, hk2, hs2, hT⟩ := dc gs n isL R legal l p hp u r' hne hr' hvo
                (hall m u hm hms) (hall' m u hm hms)
              exact ⟨k2, s2, hk2, hs2, Or.inr hT⟩
        · exact ih (n + k) hd hgo ⟨r', hne, hr', hd'⟩

theorem lpA (gs : List Gate) (n : ℕ) (isL : ℕ → Bool) (hrb : RB n gs) (legal : Legal gs)
    (xs : List Bool) (hlen : xs.length = n) (p l : ℕ) (hl : isL l = true)
    (hxs : ∀ i < n, xs.getD i false = true ↔ (i = p ∨ i = l)) :
    ∀ w, (lpv gs isL xs w).1 = true → val gs w (sg n p) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [lp_input gs isL xs w (by omega)] at h
      rw [val_input gs _ w hwn]
      by_cases hw : isL w = true
      · simp [hw] at h
      · simp [hw] at h
        rcases (hxs w hwn).1 h with e | e
        · simp [sg, e]
        · rw [e] at hw; exact absurd hl hw
    · by_cases hbig : n + gs.length ≤ w
      · rw [lp_big gs isL xs w (by omega)] at h
        exact Bool.noConfusion h
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < gs.length := by omega
        have hg : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
        have hin := hrb k _ hg
        have hlg := lp_gate gs isL xs k hk (by rw [hlen]; exact hin)
        rw [hlen] at hlg
        rw [hlg] at h
        obtain ⟨hop, hlen2⟩ := legal gs[k] (List.getElem_mem hk)
        rcases hop with ha | ho
        · rw [ha] at h
          apply (val_and gs _ k hk ha).2
          rcases len2 _ hlen2 with h0 | ⟨a, h1⟩ | ⟨a, b, h2⟩
          · intro i hi; rw [h0] at hi; simp at hi
          · rw [h1] at h
            simp [stL2] at h
            intro i hi
            rw [h1] at hi
            have e : i = a := by simpa using hi
            subst e
            have hia : i < n + k := hin i (by rw [h1]; simp)
            exact ⟨hia, ih i hia h⟩
          · rw [h2] at h
            simp [stL2] at h
            intro i hi
            rw [h2] at hi
            have e : i = a ∨ i = b := by simpa using hi
            have hia : a < n + k := hin a (by rw [h2]; simp)
            have hib : b < n + k := hin b (by rw [h2]; simp)
            rcases e with e | e
            · subst e; exact ⟨hia, ih i hia h.1⟩
            · subst e; exact ⟨hib, ih i hib h.2⟩
        · rw [ho] at h
          have h' : (gs[k].inputs.map (lpv gs isL xs)).any (·.1) = true := h
          rw [List.any_eq_true] at h'
          obtain ⟨y, hy, hy1⟩ := h'
          obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
          exact (val_or gs _ k hk ho).2 ⟨i, hi, hin i hi, ih i (hin i hi) hy1⟩

theorem lpB (gs : List Gate) (o n : ℕ) (isL : ℕ → Bool) (hrb : RB n gs) (legal : Legal gs)
    (xs : List Bool) (hlen : xs.length = n) (p l : ℕ) (hp : isL p = false) (hl : isL l = true)
    (hxs : ∀ i < n, xs.getD i false = true ↔ (i = p ∨ i = l)) :
    ∀ w, (lpv gs isL xs w).2 = true → D gs o (sg n p) w → D gs o (sg n p) l := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h hD
    by_cases hwn : w < n
    · rw [lp_input gs isL xs w (by omega)] at h
      by_cases hw : isL w = true
      · simp [hw] at h
        rcases (hxs w hwn).1 h with e | e
        · rw [e, hp] at hw; exact Bool.noConfusion hw
        · rw [← e]; exact hD
      · simp [hw] at h
    · by_cases hbig : n + gs.length ≤ w
      · rw [lp_big gs isL xs w (by omega)] at h
        exact Bool.noConfusion h
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < gs.length := by omega
        have hg : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
        have hin := hrb k _ hg
        have hlg := lp_gate gs isL xs k hk (by rw [hlen]; exact hin)
        rw [hlen] at hlg
        rw [hlg] at h
        obtain ⟨hop, hlen2⟩ := legal gs[k] (List.getElem_mem hk)
        rcases hop with ha | ho
        · rw [ha] at h
          rcases len2 _ hlen2 with h0 | ⟨a, h1⟩ | ⟨a, b, h2⟩
          · rw [h0] at h
            simp [stL2] at h
          · rw [h1] at h
            simp [stL2] at h
            have hia : a < n + k := hin a (by rw [h1]; simp)
            have hDa : D gs o (sg n p) a := by
              refine D_step gs o _ k gs[k] 0 a hg (by rw [h1]; rfl) (Or.inr ⟨ha, ?_⟩) hD
              intro m u hm hms
              rw [h1] at hm
              rcases m with _ | m
              · exact absurd rfl hms
              · simp at hm
            exact ih a hia h hDa
          · rw [h2] at h
            simp [stL2] at h
            have hia : a < n + k := hin a (by rw [h2]; simp)
            have hib : b < n + k := hin b (by rw [h2]; simp)
            rcases h with ⟨ha1, hb2⟩ | ⟨ha2, hb1⟩
            · have hDb : D gs o (sg n p) b := by
                refine D_step gs o _ k gs[k] 1 b hg (by rw [h2]; rfl) (Or.inr ⟨ha, ?_⟩) hD
                intro m u hm hms
                rw [h2] at hm
                rcases m with _ | _ | m
                · have e : a = u := by simpa using hm
                  rw [← e]
                  exact lpA gs n isL hrb legal xs hlen p l hl hxs a ha1
                · exact absurd rfl hms
                · simp at hm
              exact ih b hib hb2 hDb
            · have hDa : D gs o (sg n p) a := by
                refine D_step gs o _ k gs[k] 0 a hg (by rw [h2]; rfl) (Or.inr ⟨ha, ?_⟩) hD
                intro m u hm hms
                rw [h2] at hm
                rcases m with _ | _ | m
                · exact absurd rfl hms
                · have e : b = u := by simpa using hm
                  rw [← e]
                  exact lpA gs n isL hrb legal xs hlen p l hl hxs b hb1
                · simp at hm
              exact ih a hia ha2 hDa
        · rw [ho] at h
          have h' : (gs[k].inputs.map (lpv gs isL xs)).any (·.2) = true := h
          rw [List.any_eq_true] at h'
          obtain ⟨y, hy, hy1⟩ := h'
          obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
          obtain ⟨slot, hslot⟩ := List.getElem?_of_mem hi
          exact ih i (hin i hi) hy1 (D_step gs o _ k gs[k] slot i hg hslot (Or.inl ho) hD)

theorem card_rel {α β : Type} (A : Finset α) (B : Finset β) (r : α → β → Prop)
    (h1 : ∀ a ∈ A, ∃ b ∈ B, r a b) (h2 : ∀ a a' b, r a b → r a' b → a = a') :
    A.card ≤ B.card := by
  classical
  rw [← Finset.card_attach]
  apply Finset.card_le_card_of_injOn (fun a : {x // x ∈ A} => Classical.choose (h1 a.1 a.2))
  · intro a _
    exact (Classical.choose_spec (h1 a.1 a.2)).1
  · intro a _ a' _ hab
    have ha := (Classical.choose_spec (h1 a.1 a.2)).2
    have ha' := (Classical.choose_spec (h1 a'.1 a'.2)).2
    simp only at hab
    rw [hab] at ha
    exact Subtype.ext (h2 _ _ _ ha ha')

theorem gen (n : ℕ) (C : Circuit) (isL : ℕ → Bool) (R : ℕ → ℕ → Bool)
    (hmono : AndOrFanInTwo C) (hrb0 : ReadsBack n C)
    (hstart : ∀ l, l < n → isL l = true → ¬ D C.gates C.output (off n isL R l) l)
    (hR : ∀ a b, R a b = true → isL a = false ∧ isL b = true)
    (h4 : ∀ a a' b b', R a b = true → R a' b = true → R a b' = true → R a' b' = true →
      a ≠ a' → b = b')
    (S : Finset (ℕ × ℕ))
    (hS : ∀ e ∈ S, R e.1 e.2 = true ∧ e.2 < n ∧ ∃ xs : List Bool, xs.length = n ∧
      (∀ i < n, xs.getD i false = true ↔ (i = e.1 ∨ i = e.2)) ∧
      ((linearParts C isL xs).getD C.output (false, false)).2 = true) :
    S.card ≤ 4 * C.size + (S.image Prod.snd).card := by
  classical
  have legal : Legal C.gates := fun g hg => ⟨hmono.1 g hg, hmono.2 g hg⟩
  have hrb : RB n C.gates := by
    intro k g hg i hi
    have hk := (List.getElem?_eq_some_iff.1 hg).1
    refine hrb0 k hk i ?_
    simpa [gateAt, List.getD_eq_getElem?_getD, hg] using hi
  have hD : ∀ e ∈ S, D C.gates C.output (sg n e.1) e.2 := by
    intro e he
    obtain ⟨hRe, _, xs, hlen, hxs, hlp⟩ := hS e he
    obtain ⟨h1, h2⟩ := hR _ _ hRe
    rw [lp_eq] at hlp
    exact lpB C.gates C.output n isL hrb legal xs hlen e.1 e.2 h1 h2 hxs C.output hlp
      (D_out C.gates C.output _)
  have hsplit := Finset.card_filter_add_card_filter_not (s := S)
    (fun e => ∃ e' ∈ S, e'.2 = e.2 ∧ e'.1 ≠ e.1)
  have h1 : (S.filter (fun e => ∃ e' ∈ S, e'.2 = e.2 ∧ e'.1 ≠ e.1)).card
      ≤ ((Finset.range C.gates.length ×ˢ Finset.range 2) ×ˢ (Finset.univ : Finset Bool)).card := by
    apply card_rel _ _ (TT C.gates C.output n isL R)
    · intro e he
      obtain ⟨heS, e', he', h2, h1⟩ := Finset.mem_filter.1 he
      obtain ⟨hRe, hen, _⟩ := hS e heS
      obtain ⟨hRe', _, _⟩ := hS e' he'
      obtain ⟨hp, hl⟩ := hR _ _ hRe
      obtain ⟨hp', _⟩ := hR _ _ hRe'
      obtain ⟨t, ht⟩ := hD e heS
      have hst := hstart e.2 hen hl
      have hd' := hD e' he'
      rw [h2] at hd'
      obtain ⟨k, slot, hk, hsl, hT⟩ := uc C.gates C.output n isL R legal e.2 e.1 hp t e.2 ht hst
        ⟨e'.1, h1, hp', hd'⟩
      rcases hT with hT | hT
      · exact ⟨((k, slot), true), by simp [hk, hsl], Or.inl ⟨rfl, hT⟩⟩
      · exact ⟨((k, slot), false), by simp [hk, hsl], Or.inr ⟨rfl, hT⟩⟩
    · intro a a' b hab hab'
      exact TT_inj C.gates C.output n isL R legal h4 a a' b hab hab'
  have h0 : (S.filter (fun e => ¬ ∃ e' ∈ S, e'.2 = e.2 ∧ e'.1 ≠ e.1)).card
      ≤ (S.image Prod.snd).card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro e he
      exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_filter.1 (Finset.mem_coe.1 he)).1)
    · intro e he e' he' hee
      obtain ⟨heS, hne⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 he)
      obtain ⟨heS', _⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 he')
      by_contra hc
      apply hne
      refine ⟨e', heS', hee.symm, fun h => hc (Prod.ext h.symm hee)⟩
  have hcard : ((Finset.range C.gates.length ×ˢ Finset.range 2) ×ˢ
      (Finset.univ : Finset Bool)).card = 4 * C.gates.length := by
    simp [Finset.card_product]; ring
  rw [hcard] at h1
  unfold Circuit.size
  omega

theorem img2 (n : ℕ) (C : Circuit) (isL : ℕ → Bool) (R : ℕ → ℕ → Bool)
    (hmono : AndOrFanInTwo C) (hrb0 : ReadsBack n C)
    (hstart : ∀ l, l < n → isL l = true → ¬ D C.gates C.output (off n isL R l) l)
    (hR : ∀ a b, R a b = true → isL a = false ∧ isL b = true)
    (S : Finset (ℕ × ℕ))
    (hS : ∀ e ∈ S, R e.1 e.2 = true ∧ e.2 < n ∧ ∃ xs : List Bool, xs.length = n ∧
      (∀ i < n, xs.getD i false = true ↔ (i = e.1 ∨ i = e.2)) ∧
      ((linearParts C isL xs).getD C.output (false, false)).2 = true) :
    (S.image Prod.snd).card ≤ 2 * C.size := by
  classical
  have legal : Legal C.gates := fun g hg => ⟨hmono.1 g hg, hmono.2 g hg⟩
  have hrb : RB n C.gates := by
    intro k g hg i hi
    have hk := (List.getElem?_eq_some_iff.1 hg).1
    refine hrb0 k hk i ?_
    simpa [gateAt, List.getD_eq_getElem?_getD, hg] using hi
  have h1 : (S.image Prod.snd).card
      ≤ (Finset.range C.gates.length ×ˢ Finset.range 2).card := by
    apply card_rel _ _ (fun (b : ℕ) (t : ℕ × ℕ) =>
      ∃ g, C.gates[t.1]? = some g ∧ g.inputs[t.2]? = some b)
    · intro b hb
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hb
      obtain ⟨hRe, hen, xs, hlen, hxs, hlp⟩ := hS e he
      obtain ⟨h1, h2⟩ := hR _ _ hRe
      rw [lp_eq] at hlp
      have hd := lpB C.gates C.output n isL hrb legal xs hlen e.1 e.2 h1 h2 hxs C.output hlp
        (D_out C.gates C.output _)
      have hst := hstart e.2 hen h2
      have hne : e.2 ≠ C.output := by
        intro h
        apply hst
        have key : ∀ w : ℕ, w = C.output → D C.gates C.output (off n isL R e.2) w := by
          intro w hw
          subst hw
          exact D_out C.gates C.output _
        exact key e.2 h
      obtain ⟨t, ht⟩ := hd
      cases t with
      | zero => exact absurd ht hne
      | succ t =>
        rcases (Dn_succ C.gates C.output _ t e.2).1 ht with h | ⟨k, g, slot, hg, hs, _, _⟩
        · exact absurd h hne
        · refine ⟨(k, slot), ?_, g, hg, hs⟩
          have hk := (List.getElem?_eq_some_iff.1 hg).1
          have hsl := (List.getElem?_eq_some_iff.1 hs).1
          have hlen2 := (legal g (List.mem_of_getElem? hg)).2
          simp only [Finset.mem_product, Finset.mem_range]
          exact ⟨hk, by omega⟩
    · rintro a a' b ⟨g, hg, hs⟩ ⟨g', hg', hs'⟩
      rw [hg] at hg'
      cases hg'
      rw [hs] at hs'
      cases hs'
      rfl
  rw [Finset.card_product, Finset.card_range, Finset.card_range] at h1
  unfold Circuit.size
  omega

def Rr (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (a b : ℕ) : Bool :=
  decide (∃ p l : Fin N, a = p.val ∧ b = N + l.val ∧ I p l)

theorem Rr_iff (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (a b : ℕ) :
    Rr N I a b = true ↔ ∃ p l : Fin N, a = p.val ∧ b = N + l.val ∧ I p l := by
  unfold Rr
  exact decide_eq_true_iff

def Ey (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) (isL : ℕ → Bool) :
    Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => I e.1 e.2 ∧ lineSingle C (N + N) isL e.1.val (N + e.2.val) = true)

theorem coreL (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2 ≤ q)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l1 : Fin N, I p1 l1 ∧ I p2 l1)
    (hao : AndOrFanInTwo C) (hrb : ReadsBack (N + N) C)
    (hsound : ∀ z : Fin (N + N) → Bool,
      (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N + N) C z = false) :
    (Ey N I C (fun i => decide (N ≤ i))).card ≤ 6 * C.size := by
  have legal : Legal C.gates := fun g hg => ⟨hao.1 g hg, hao.2 g hg⟩
  have hrb' : RB (N + N) C.gates := by
    intro k g hg i hi
    have hk := (List.getElem?_eq_some_iff.1 hg).1
    refine hrb k hk i ?_
    simpa [gateAt, List.getD_eq_getElem?_getD, hg] using hi
  have hstart : ∀ l, l < N + N → (fun i => decide (N ≤ i)) l = true →
      ¬ D C.gates C.output (off (N + N) (fun i => decide (N ≤ i)) (Rr N I) l) l := by
    intro l hln hl
    have hNl : N ≤ l := of_decide_eq_true hl
    let l0 : Fin N := ⟨l - N, by omega⟩
    have hl0 : l = N + l0.val := by dsimp [l0]; omega
    rintro ⟨t, ht⟩
    let z : Fin (N + N) → Bool := fun i =>
      off (N + N) (fun j => decide (N ≤ j)) (Rr N I) l i || decide (i.val = l)
    have hz_true : val C.gates C.output z = true := by
      refine snd C.gates C.output legal hrb' _ z (fun v hv => by simp [z, hv]) t l ht ?_
      rw [val_input C.gates _ l hln]
      simp [z]
    have hz_lines : (Finset.univ.filter (fun r : Fin N => z (Fin.natAdd N r) = true)).card ≤ q := by
      have hsub : Finset.univ.filter (fun r : Fin N => z (Fin.natAdd N r) = true) ⊆ {l0} := by
        intro r hr
        have hzr : z (Fin.natAdd N r) = true := (Finset.mem_filter.1 hr).2
        have hge : N ≤ N + r.val := Nat.le_add_right N r.val
        simp only [z, off, Fin.val_natAdd, decide_eq_true hge, Bool.not_true, Bool.false_and,
          Bool.false_or, decide_eq_true_eq] at hzr
        exact Finset.mem_singleton.2 (Fin.ext (by omega))
      calc (Finset.univ.filter (fun r : Fin N => z (Fin.natAdd N r) = true)).card
          ≤ ({l0} : Finset (Fin N)).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton l0
        _ ≤ q := by omega
    have hz_no : ¬ ∃ p r : Fin N, I p r ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N r) = true := by
      rintro ⟨p, r, hIpr, hzp, hzr⟩
      have hge : N ≤ N + r.val := Nat.le_add_right N r.val
      simp only [z, off, Fin.val_natAdd, decide_eq_true hge, Bool.not_true, Bool.false_and,
        Bool.false_or, decide_eq_true_eq] at hzr
      have hr0 : r = l0 := Fin.ext (by omega)
      subst hr0
      have hlt : ¬ (N ≤ p.val) := by
        have := p.isLt
        omega
      have hne : p.val ≠ l := by
        have := p.isLt
        omega
      simp only [z, off, Fin.val_castAdd, decide_eq_false hlt, Bool.not_false, Bool.true_and,
        decide_eq_false hne, Bool.or_false, Bool.not_eq_true'] at hzp
      have hRr : Rr N I p.val l = true :=
        (Rr_iff N I _ _).2 ⟨p, l0, rfl, hl0, hIpr⟩
      rw [hRr] at hzp
      exact Bool.noConfusion hzp
    have hz_false : val C.gates C.output z = false := hsound z hz_lines hz_no
    rw [hz_true] at hz_false
    exact Bool.noConfusion hz_false
  have hR : ∀ a b, Rr N I a b = true →
      (fun i => decide (N ≤ i)) a = false ∧ (fun i => decide (N ≤ i)) b = true := by
    intro a b h
    obtain ⟨p, l, rfl, rfl, _⟩ := (Rr_iff N I _ _).1 h
    refine ⟨?_, ?_⟩
    · show decide (N ≤ p.val) = false
      exact decide_eq_false (by have := p.isLt; omega)
    · show decide (N ≤ N + l.val) = true
      exact decide_eq_true (by omega)
  have h4 : ∀ a a' b b', Rr N I a b = true → Rr N I a' b = true → Rr N I a b' = true →
      Rr N I a' b' = true → a ≠ a' → b = b' := by
    intro a a' b b' h1 h2 h3 h4 hne
    obtain ⟨p, l, rfl, rfl, i1⟩ := (Rr_iff N I _ _).1 h1
    obtain ⟨p', l2, rfl, e2, i2⟩ := (Rr_iff N I _ _).1 h2
    obtain ⟨p3, l', e3, rfl, i3⟩ := (Rr_iff N I _ _).1 h3
    obtain ⟨p4, l4, e4, e5, i4⟩ := (Rr_iff N I _ _).1 h4
    have el2 : l2 = l := Fin.ext (by omega)
    have ep3 : p3 = p := Fin.ext e3.symm
    have ep4 : p4 = p' := Fin.ext e4.symm
    have el4 : l4 = l' := Fin.ext (by omega)
    rw [el2] at i2
    rw [ep3] at i3
    rw [ep4, el4] at i4
    have hpp : p ≠ p' := fun h => hne (by rw [h])
    obtain ⟨l0, _, hu⟩ := huniq p p' hpp
    have ea := hu l ⟨i1, i2⟩
    have eb := hu l' ⟨i3, i4⟩
    rw [ea, eb]
  have hS : ∀ e ∈ (Ey N I C (fun i => decide (N ≤ i))).image (fun e => (e.1.val, N + e.2.val)),
      Rr N I e.1 e.2 = true ∧ e.2 < N + N ∧ ∃ xs : List Bool,
      xs.length = N + N ∧
      (∀ i < N + N, xs.getD i false = true ↔ (i = e.1 ∨ i = e.2)) ∧
      ((linearParts C (fun i => decide (N ≤ i)) xs).getD C.output (false, false)).2 = true := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨_, hI, hls⟩ := Finset.mem_filter.1 he0
    refine ⟨(Rr_iff N I _ _).2 ⟨e0.1, e0.2, rfl, rfl, hI⟩, ?_,
      (List.range (N + N)).map (fun i => i == e0.1.val || i == N + e0.2.val), by simp, ?_, hls⟩
    · show N + e0.2.val < N + N
      have := e0.2.isLt
      omega
    · intro i hi
      simp [List.getD_eq_getElem?_getD, hi]
  have hx := gen (N + N) C (fun i => decide (N ≤ i)) (Rr N I) hao hrb hstart hR h4 _ hS
  have ix := img2 (N + N) C (fun i => decide (N ≤ i)) (Rr N I) hao hrb hstart hR _ hS
  have cx : ((Ey N I C (fun i => decide (N ≤ i))).image (fun e => (e.1.val, N + e.2.val))).card
      = (Ey N I C (fun i => decide (N ≤ i))).card := by
    apply Finset.card_image_of_injective
    intro e e' h
    have h1 := (Prod.ext_iff.1 h).1
    have h2 := (Prod.ext_iff.1 h).2
    exact Prod.ext (Fin.ext h1) (Fin.ext (by simpa using h2))
  omega

/-! ## Part 2: Point-single incidences under soundness up to `q` lines -/

theorem point_deg (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hLine : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l1 : Fin N, I p1 l1 ∧ I p2 l1)
    (p : Fin N) : (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  let Lp : Finset (Fin N) := Finset.univ.filter (fun l => I p l)
  let Pl : Fin N → Finset (Fin N) := fun l => (Finset.univ.filter (fun p' => I p' l)).erase p
  have hdisj : Set.PairwiseDisjoint (Lp : Set (Fin N)) Pl := by
    intro l1 hl1 l2 hl2 hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p' hp1 hp2
    have h1 : p' ≠ p ∧ I p' l1 := by
      have := Finset.mem_erase.1 hp1
      exact ⟨this.1, (Finset.mem_filter.1 this.2).2⟩
    have h2 : I p' l2 := (Finset.mem_filter.1 (Finset.mem_erase.1 hp2).2).2
    have hpl1 : I p l1 := (Finset.mem_filter.1 hl1).2
    have hpl2 : I p l2 := (Finset.mem_filter.1 hl2).2
    obtain ⟨l0, _, hu⟩ := huniq p p' h1.1.symm
    exact hne ((hu l1 ⟨hpl1, h1.2⟩).trans (hu l2 ⟨hpl2, h2⟩).symm)
  have heq : Lp.biUnion Pl = Finset.univ.erase p := by
    ext p'
    simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
      and_true, true_and, Lp, Pl]
    constructor
    · rintro ⟨_, _, hne, _⟩
      exact hne
    · intro hne
      obtain ⟨l0, ⟨hpl, hp'l⟩, _⟩ := huniq p p' hne.symm
      exact ⟨l0, hpl, hne, hp'l⟩
  have hcard1 : (Lp.biUnion Pl).card = N - 1 := by
    rw [heq, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin]
  have hcard2 : (Lp.biUnion Pl).card = Lp.card * q := by
    rw [Finset.card_biUnion hdisj]
    have hPl : ∀ l ∈ Lp, (Pl l).card = q := by
      intro l hl
      have hpl : p ∈ Finset.univ.filter (fun p' => I p' l) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ p, (Finset.mem_filter.1 hl).2⟩
      rw [Finset.card_erase_of_mem hpl, hLine l]
      omega
    rw [Finset.sum_congr rfl hPl, Finset.sum_const, smul_eq_mul]
  have hmul : Lp.card * q = (q + 1) * q := by
    have : N - 1 = (q + 1) * q := by rw [hN]; ring_nf; omega
    omega
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) hmul

def lineSet (N : ℕ) (S : Finset (Fin N)) : Fin (N + N) → Bool :=
  fun i => decide (∃ r ∈ S, i.val = N + r.val)

theorem lineSet_mono (N : ℕ) {S1 S2 : Finset (Fin N)} (hsub : S1 ⊆ S2) :
    ∀ v, lineSet N S1 v = true → lineSet N S2 v = true := by
  intro v hv
  simp only [lineSet, decide_eq_true_eq] at hv ⊢
  obtain ⟨r, hr, hvr⟩ := hv
  exact ⟨r, hsub hr, hvr⟩

theorem lineSet_singleton (N : ℕ) (r : Fin N) :
    lineSet N {r} = sg (N + N) (N + r.val) := by
  funext i
  simp [lineSet, sg]

def pointAndLines (N : ℕ) (p : Fin N) (S : Finset (Fin N)) : Fin (N + N) → Bool :=
  fun i => lineSet N S i || decide (i.val = p.val)

theorem lineSet_le_pointAndLines (N : ℕ) (p : Fin N) (S : Finset (Fin N)) :
    ∀ v, lineSet N S v = true → pointAndLines N p S v = true := by
  intro v hv
  simp [pointAndLines, hv]

theorem pointAndLines_castAdd (N : ℕ) (p p' : Fin N) (S : Finset (Fin N)) :
    pointAndLines N p S (Fin.castAdd N p') = decide (p' = p) := by
  have hno : ¬ ∃ r ∈ S, p'.val = N + r.val := by
    rintro ⟨r, _, h⟩
    have := p'.isLt
    omega
  simp only [pointAndLines, lineSet, Fin.val_castAdd, decide_eq_false hno, Bool.false_or]
  by_cases h : p' = p
  · subst h; simp
  · have hv : p'.val ≠ p.val := fun he => h (Fin.ext he)
    simp [h, hv]

theorem pointAndLines_natAdd (N : ℕ) (p l : Fin N) (S : Finset (Fin N)) :
    pointAndLines N p S (Fin.natAdd N l) = decide (l ∈ S) := by
  have hne : N + l.val ≠ p.val := by
    have := p.isLt
    omega
  simp only [pointAndLines, lineSet, Fin.val_natAdd, decide_eq_false hne, Bool.or_false]
  have hiff : (∃ r ∈ S, N + l.val = N + r.val) ↔ l ∈ S := by
    constructor
    · rintro ⟨r, hr, he⟩
      have : l = r := Fin.ext (by omega)
      rwa [this]
    · intro hl
      exact ⟨l, hl, rfl⟩
  by_cases hl : l ∈ S
  · rw [decide_eq_true (hiff.2 hl), decide_eq_true hl]
  · rw [decide_eq_false (fun h => hl (hiff.1 h)), decide_eq_false hl]

def valSmall (N : ℕ) (I : Fin N → Fin N → Prop) (gs : List Gate) (w : ℕ) (p : Fin N) : Prop :=
  ∃ S : Finset (Fin N), S.card ≤ 1 ∧ (∀ r ∈ S, ¬ I p r) ∧ val gs w (lineSet N S) = true

def dSmall (N : ℕ) (I : Fin N → Fin N → Prop) (gs : List Gate) (o : ℕ) (w : ℕ) (p : Fin N) : Prop :=
  ∃ S : Finset (Fin N), S.card ≤ 1 ∧ (∀ r ∈ S, ¬ I p r) ∧ D gs o (lineSet N S) w

theorem inc_of_not_valSmall (N : ℕ) (I : Fin N → Fin N → Prop) (gs : List Gate)
    (w : ℕ) (p r : Fin N) (hns : ¬ valSmall N I gs w p)
    (hv : val gs w (sg (N + N) (N + r.val)) = true) : I p r := by
  by_contra hni
  apply hns
  refine ⟨{r}, by simp, fun r' hr' => ?_, ?_⟩
  · rw [Finset.mem_singleton.1 hr']; exact hni
  · rwa [lineSet_singleton]

theorem inc_of_not_dSmall (N : ℕ) (I : Fin N → Fin N → Prop) (gs : List Gate) (o : ℕ)
    (w : ℕ) (p r : Fin N) (hns : ¬ dSmall N I gs o w p)
    (hd : D gs o (sg (N + N) (N + r.val)) w) : I p r := by
  by_contra hni
  apply hns
  refine ⟨{r}, by simp, fun r' hr' => ?_, ?_⟩
  · rw [Finset.mem_singleton.1 hr']; exact hni
  · rwa [lineSet_singleton]

theorem eq_point_of_two_lines (N : ℕ) (I : Fin N → Fin N → Prop)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l1 : Fin N, I p1 l1 ∧ I p2 l1)
    (p p' r1 r2 : Fin N) (hne : r1 ≠ r2)
    (h1 : I p r1) (h2 : I p r2) (h3 : I p' r1) (h4 : I p' r2) : p = p' := by
  by_contra hpp
  obtain ⟨l0, _, hu⟩ := huniq p p' hpp
  exact hne ((hu r1 ⟨h1, h3⟩).trans (hu r2 ⟨h2, h4⟩).symm)

def T1q (N : ℕ) (I : Fin N → Fin N → Prop) (gs : List Gate) (o : ℕ)
    (k slot : ℕ) (p l : Fin N) : Prop :=
  ∃ g u, gs[k]? = some g ∧ g.inputs[slot]? = some u ∧
    ¬ dSmall N I gs o u p ∧
    (∃ r1 r2 : Fin N, r1 ≠ r2 ∧
      D gs o (sg (N + N) (N + r1.val)) u ∧ D gs o (sg (N + N) (N + r2.val)) u) ∧
    sib gs (sg (N + N) (N + l.val)) g slot ∧
    D gs o (sg (N + N) (N + l.val)) (N + N + k) ∧
    ∀ r : Fin N, sib gs (sg (N + N) (N + r.val)) g slot →
      D gs o (sg (N + N) (N + r.val)) (N + N + k) → r = l

def T2q (N : ℕ) (I : Fin N → Fin N → Prop) (gs : List Gate)
    (k slot : ℕ) (p l : Fin N) : Prop :=
  ∃ g a, gs[k]? = some g ∧ g.inputs[slot]? = some a ∧
    ¬ valSmall N I gs (N + N + k) p ∧
    (∃ r1 r2 : Fin N, r1 ≠ r2 ∧
      val gs (N + N + k) (sg (N + N) (N + r1.val)) = true ∧
      val gs (N + N + k) (sg (N + N) (N + r2.val)) = true) ∧
    val gs a (sg (N + N) (N + l.val)) = true ∧
    ∀ r : Fin N, val gs a (sg (N + N) (N + r.val)) = true → r = l

def TTq (N : ℕ) (I : Fin N → Fin N → Prop) (gs : List Gate) (o : ℕ)
    (e : Fin N × Fin N) (t : (ℕ × ℕ) × Bool) : Prop :=
  (t.2 = true ∧ T1q N I gs o t.1.1 t.1.2 e.1 e.2) ∨
  (t.2 = false ∧ T2q N I gs t.1.1 t.1.2 e.1 e.2)

theorem TTq_inj (N : ℕ) (I : Fin N → Fin N → Prop) (gs : List Gate) (o : ℕ)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l1 : Fin N, I p1 l1 ∧ I p2 l1)
    (e e' : Fin N × Fin N) (t : (ℕ × ℕ) × Bool) :
    TTq N I gs o e t → TTq N I gs o e' t → e = e' := by
  rintro (⟨hb, g, u, hg, hu, hnd, ⟨r1, r2, hne, hd1, hd2⟩, hsib, hdl, hlu⟩ |
          ⟨hb, g, a, hg, ha, hnv, ⟨r1, r2, hne, hv1, hv2⟩, hvl, hlu⟩)
         (⟨hb', g', u', hg', hu', hnd', _, hsib', hdl', _⟩ |
          ⟨hb', g', a', hg', ha', hnv', _, hvl', _⟩)
  · rw [hg] at hg'; cases hg'
    rw [hu] at hu'; cases hu'
    have hp : e.1 = e'.1 := eq_point_of_two_lines N I huniq e.1 e'.1 r1 r2 hne
      (inc_of_not_dSmall N I gs o u e.1 r1 hnd hd1)
      (inc_of_not_dSmall N I gs o u e.1 r2 hnd hd2)
      (inc_of_not_dSmall N I gs o u e'.1 r1 hnd' hd1)
      (inc_of_not_dSmall N I gs o u e'.1 r2 hnd' hd2)
    have hl : e.2 = e'.2 := (hlu e'.2 hsib' hdl').symm
    exact Prod.ext hp hl
  · rw [hb] at hb'; cases hb'
  · rw [hb] at hb'; cases hb'
  · rw [hg] at hg'; cases hg'
    rw [ha] at ha'; cases ha'
    have hp : e.1 = e'.1 := eq_point_of_two_lines N I huniq e.1 e'.1 r1 r2 hne
      (inc_of_not_valSmall N I gs (N + N + t.1.1) e.1 r1 hnv hv1)
      (inc_of_not_valSmall N I gs (N + N + t.1.1) e.1 r2 hnv hv2)
      (inc_of_not_valSmall N I gs (N + N + t.1.1) e'.1 r1 hnv' hv1)
      (inc_of_not_valSmall N I gs (N + N + t.1.1) e'.1 r2 hnv' hv2)
    have hl : e.2 = e'.2 := (hlu e'.2 hvl').symm
    exact Prod.ext hp hl

def DpPred (N : ℕ) (I : Fin N → Fin N → Prop) (gs : List Gate) (o : ℕ) (p : Fin N)
    (x : ℕ × ℕ) : Prop :=
  ∃ g u, gs[x.1]? = some g ∧ g.inputs[x.2]? = some u ∧
    ¬ dSmall N I gs o u p ∧
    ∃ r1 r2 : Fin N, r1 ≠ r2 ∧
      D gs o (sg (N + N) (N + r1.val)) u ∧ D gs o (sg (N + N) (N + r2.val)) u

def VpPred (N : ℕ) (I : Fin N → Fin N → Prop) (gs : List Gate) (p : Fin N) (k : ℕ) : Prop :=
  ¬ valSmall N I gs (N + N + k) p ∧
  ∃ r1 r2 : Fin N, r1 ≠ r2 ∧
    val gs (N + N + k) (sg (N + N) (N + r1.val)) = true ∧
    val gs (N + N + k) (sg (N + N) (N + r2.val)) = true

def GoodPred (N : ℕ) (I : Fin N → Fin N → Prop) (gs : List Gate) (o : ℕ)
    (e : Fin N × Fin N) : Prop :=
  ∃ k < gs.length, ∃ slot < 2,
    T1q N I gs o k slot e.1 e.2 ∨ T2q N I gs k slot e.1 e.2

theorem coreP_q (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hLine : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l1 : Fin N, I p1 l1 ∧ I p2 l1)
    (hao : AndOrFanInTwo C) (hrb0 : ReadsBack (N + N) C)
    (hsound : ∀ z : Fin (N + N) → Bool,
      (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N + N) C z = false) :
    (Ey N I C (fun i => decide (i < N))).card ≤ 8 * C.size + N := by
  classical
  let gs := C.gates
  let o := C.output
  have legal : Legal gs := fun g hg => ⟨hao.1 g hg, hao.2 g hg⟩
  have hrb : RB (N + N) gs := by
    intro k g hg i hi
    have hk := (List.getElem?_eq_some_iff.1 hg).1
    refine hrb0 k hk i ?_
    simpa [gateAt, List.getD_eq_getElem?_getD, gs, hg] using hi
  let EyP := Ey N I C (fun i => decide (i < N))
  have hD_EyP : ∀ e ∈ EyP, D gs o (sg (N + N) (N + e.2.val)) e.1.val := by
    intro e he
    obtain ⟨_, _, hls⟩ := Finset.mem_filter.1 he
    let xs : List Bool :=
      (List.range (N + N)).map (fun i => i == e.1.val || i == N + e.2.val)
    have hlen : xs.length = N + N := by simp [xs]
    have hxs : ∀ i < N + N, xs.getD i false = true ↔ (i = N + e.2.val ∨ i = e.1.val) := by
      intro i hi
      simp [xs, List.getD_eq_getElem?_getD, hi, or_comm]
    have h1 : (fun i => decide (i < N)) (N + e.2.val) = false :=
      decide_eq_false (by omega)
    have h2 : (fun i => decide (i < N)) e.1.val = true :=
      decide_eq_true e.1.isLt
    have hlp : (lpv gs (fun i => decide (i < N)) xs o).2 = true := hls
    exact lpB gs o (N + N) (fun i => decide (i < N)) hrb legal xs hlen
      (N + e.2.val) e.1.val h1 h2 hxs o hlp (D_out gs o _)
  let Dp : Fin N → Finset (ℕ × ℕ) := fun p =>
    (Finset.range gs.length ×ˢ Finset.range 2).filter (fun x => DpPred N I gs o p x)
  let Vp : Fin N → Finset ℕ := fun p =>
    (Finset.range gs.length).filter (fun k => VpPred N I gs p k)
  let Ep : Fin N → Finset (Fin N) := fun p =>
    Finset.univ.filter (fun l => (p, l) ∈ EyP)
  let GoodE : Finset (Fin N × Fin N) :=
    EyP.filter (GoodPred N I gs o)
  let GoodEp : Fin N → Finset (Fin N) := fun p =>
    Finset.univ.filter (fun l => (p, l) ∈ GoodE)
  -- Per-point bound: (Ep p).card ≤ (GoodEp p).card + (Dp p).card + 2 * (Vp p).card + 1
  have hpoint : ∀ p : Fin N,
      (Ep p).card ≤ (GoodEp p).card + (Dp p).card + 2 * (Vp p).card + 1 := by
    intro p
    by_cases hle1 : (Ep p).card ≤ 1
    · omega
    · by_cases hall : ∀ l ∈ Ep p, l ∈ GoodEp p
      · have hsub : Ep p ⊆ GoodEp p := hall
        have hle := Finset.card_le_card hsub
        omega
      · push Not at hall
        obtain ⟨l, hlEp, hlNotGood⟩ := hall
        have hlNoT : ∀ k < gs.length, ∀ slot < 2,
            ¬ T1q N I gs o k slot p l ∧ ¬ T2q N I gs k slot p l := by
          intro k hk slot hslot
          have hmemEy : (p, l) ∈ EyP := (Finset.mem_filter.1 hlEp).2
          have hnot : ¬ GoodPred N I gs o (p, l) := by
            intro hex
            apply hlNotGood
            exact Finset.mem_filter.2 ⟨Finset.mem_univ l, Finset.mem_filter.2 ⟨hmemEy, hex⟩⟩
          exact ⟨fun h1 => hnot ⟨k, hk, slot, hslot, Or.inl h1⟩,
                 fun h2 => hnot ⟨k, hk, slot, hslot, Or.inr h2⟩⟩
        -- Pick a second line l2 ∈ Ep p with l2 ≠ l
        have hgt1 : 1 < (Ep p).card := by omega
        obtain ⟨l2, hl2Ep, hl2ne⟩ : ∃ l2 ∈ Ep p, l2 ≠ l := by
          obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hgt1
          by_cases hal : a = l
          · exact ⟨b, hb, fun h => hab (hal.trans h.symm)⟩
          · exact ⟨a, ha, hal⟩
        -- Build U_D from Dp p and U_V from Vp p ×ˢ range 2
        let pickD : ℕ × ℕ → Finset (Fin N) := fun x =>
          if h : ∃ g u, gs[x.1]? = some g ∧ g.op = GateOp.and ∧
              g.inputs[1 - x.2]? = some u ∧ valSmall N I gs u p then
            let g := Classical.choose h
            let hg := Classical.choose_spec h
            let u := Classical.choose hg
            let hu := Classical.choose_spec hg
            Classical.choose hu.2.2.2
          else ∅
        have hpickD_card : ∀ x, (pickD x).card ≤ 1 := by
          intro x
          dsimp only [pickD]
          split_ifs with h
          · exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h)).2.2.2).1
          · simp
        have hpickD_noninc : ∀ x, ∀ r ∈ pickD x, ¬ I p r := by
          intro x r hr
          dsimp only [pickD] at hr
          split_ifs at hr with h
          · exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h)).2.2.2).2.1 r hr
          · simp at hr
        have hpickD_val : ∀ k slot g u, gs[k]? = some g → g.op = GateOp.and →
            g.inputs[1 - slot]? = some u → valSmall N I gs u p →
            val gs u (lineSet N (pickD (k, slot))) = true := by
          intro k slot g u hg hop hgm hvs
          have hex : ∃ g' u', gs[k]? = some g' ∧ g'.op = GateOp.and ∧
              g'.inputs[1 - slot]? = some u' ∧ valSmall N I gs u' p :=
            ⟨g, u, hg, hop, hgm, hvs⟩
          simp only [pickD, hex, ↓reduceDIte]
          have hg' := Classical.choose_spec hex
          have hu' := Classical.choose_spec hg'
          have hS := Classical.choose_spec hu'.2.2.2
          have eg : Classical.choose hex = g :=
            Option.some.inj (hu'.1.symm.trans hg)
          have hgm' : g.inputs[1 - slot]? = some (Classical.choose hg') := eg ▸ hu'.2.2.1
          have eu : Classical.choose hg' = u :=
            Option.some.inj (hgm'.symm.trans hgm)
          rw [← eu]
          exact hS.2.2
        let pickV : ℕ × ℕ → Finset (Fin N) := fun x =>
          if h : ∃ g a, gs[x.1]? = some g ∧ g.inputs[x.2]? = some a ∧ valSmall N I gs a p then
            let g := Classical.choose h
            let hg := Classical.choose_spec h
            let a := Classical.choose hg
            let ha := Classical.choose_spec hg
            Classical.choose ha.2.2
          else ∅
        have hpickV_card : ∀ x, (pickV x).card ≤ 1 := by
          intro x
          dsimp only [pickV]
          split_ifs with h
          · exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h)).2.2).1
          · simp
        have hpickV_noninc : ∀ x, ∀ r ∈ pickV x, ¬ I p r := by
          intro x r hr
          dsimp only [pickV] at hr
          split_ifs at hr with h
          · exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h)).2.2).2.1 r hr
          · simp at hr
        have hpickV_val : ∀ k slot g a, gs[k]? = some g → g.inputs[slot]? = some a →
            valSmall N I gs a p → val gs a (lineSet N (pickV (k, slot))) = true := by
          intro k slot g a hg hga hvs
          have hex : ∃ g' a', gs[k]? = some g' ∧ g'.inputs[slot]? = some a' ∧ valSmall N I gs a' p :=
            ⟨g, a, hg, hga, hvs⟩
          simp only [pickV, hex, ↓reduceDIte]
          have hg' := Classical.choose_spec hex
          have ha' := Classical.choose_spec hg'
          have hS := Classical.choose_spec ha'.2.2
          have eg : Classical.choose hex = g :=
            Option.some.inj (ha'.1.symm.trans hg)
          have hga' : g.inputs[slot]? = some (Classical.choose hg') := eg ▸ ha'.2.1
          have ea : Classical.choose hg' = a :=
            Option.some.inj (hga'.symm.trans hga)
          rw [← ea]
          exact hS.2.2
        let UD : Finset (Fin N) := (Dp p).biUnion pickD
        let UV : Finset (Fin N) := (Vp p ×ˢ Finset.range 2).biUnion pickV
        let Ubase : Finset (Fin N) := UD ∪ UV
        have hUD_card : UD.card ≤ (Dp p).card := by
          calc UD.card ≤ ∑ x ∈ Dp p, (pickD x).card := Finset.card_biUnion_le
            _ ≤ ∑ _x ∈ Dp p, 1 := Finset.sum_le_sum (fun x _ => hpickD_card x)
            _ = (Dp p).card := by simp
        have hUV_card : UV.card ≤ 2 * (Vp p).card := by
          calc UV.card ≤ ∑ x ∈ Vp p ×ˢ Finset.range 2, (pickV x).card := Finset.card_biUnion_le
            _ ≤ ∑ _x ∈ Vp p ×ˢ Finset.range 2, 1 := Finset.sum_le_sum (fun x _ => hpickV_card x)
            _ = (Vp p ×ˢ Finset.range 2).card := by simp
            _ = 2 * (Vp p).card := by simp [Finset.card_product, Nat.mul_comm]
        have hUbase_card : Ubase.card ≤ (Dp p).card + 2 * (Vp p).card := by
          calc Ubase.card ≤ UD.card + UV.card := Finset.card_union_le _ _
            _ ≤ (Dp p).card + 2 * (Vp p).card := Nat.add_le_add hUD_card hUV_card
        have hUbase_noninc : ∀ r ∈ Ubase, ¬ I p r := by
          intro r hr
          rcases Finset.mem_union.1 hr with hD | hV
          · obtain ⟨x, _, hx⟩ := Finset.mem_biUnion.1 hD
            exact hpickD_noninc x r hx
          · obtain ⟨x, _, hx⟩ := Finset.mem_biUnion.1 hV
            exact hpickV_noninc x r hx
        -- Sublemma 1: strong induction on s for val gs s (lineSet N Ubase) = true
        have hSub1 : ∀ s, ¬ valSmall N I gs s p →
            val gs s (sg (N + N) (N + l.val)) = true →
            (∃ r : Fin N, r ≠ l ∧ val gs s (sg (N + N) (N + r.val)) = true) →
            val gs s (lineSet N Ubase) = true := by
          intro s
          induction s using Nat.strong_induction_on with
          | ind s ih =>
            intro hns hvl ⟨r, hrl, hvr⟩
            by_cases hsn : s < N + N
            · rw [val_input gs _ s hsn] at hvl hvr
              have e1 : s = N + l.val := by simpa [sg] using hvl
              have e2 : s = N + r.val := by simpa [sg] using hvr
              exact absurd (Fin.ext (by omega : r.val = l.val)) hrl
            · by_cases hbig : N + N + gs.length ≤ s
              · rw [val_big gs _ s hbig] at hvl
                exact Bool.noConfusion hvl
              · obtain ⟨k, rfl⟩ : ∃ k, s = N + N + k := ⟨s - (N + N), by omega⟩
                have hk : k < gs.length := by omega
                have hgk : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
                rcases (legal gs[k] (List.getElem_mem hk)).1 with ha | ho
                · have hkVp : k ∈ Vp p :=
                    Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hns, l, r, hrl.symm, hvl, hvr⟩
                  have h1 := (val_and gs _ k hk ha).1 hvl
                  have h2 := (val_and gs _ k hk ha).1 hvr
                  apply (val_and gs _ k hk ha).2
                  intro a haIn
                  refine ⟨(h1 a haIn).1, ?_⟩
                  by_cases hva : valSmall N I gs a p
                  · obtain ⟨slot, hslot⟩ := List.getElem?_of_mem haIn
                    have hslot2 : slot < 2 := by
                      have hlt := (List.getElem?_eq_some_iff.1 hslot).1
                      have hlen2 := (legal gs[k] (List.mem_of_getElem? hgk)).2
                      omega
                    have hvPick := hpickV_val k slot gs[k] a hgk hslot hva
                    have hsubU : pickV (k, slot) ⊆ Ubase := by
                      intro x hx
                      exact Finset.mem_union_right _ (Finset.mem_biUnion.2
                        ⟨(k, slot), Finset.mem_product.2 ⟨hkVp, Finset.mem_range.2 hslot2⟩, hx⟩)
                    exact val_mono gs legal _ _ (lineSet_mono N hsubU) a hvPick
                  · exact ih a (h1 a haIn).1 hva (h1 a haIn).2 ⟨r, hrl, (h2 a haIn).2⟩
                · obtain ⟨a, haIn, halt, hval⟩ := (val_or gs _ k hk ho).1 hvl
                  have hnsa : ¬ valSmall N I gs a p := by
                    rintro ⟨S, hSc, hSni, hSv⟩
                    exact hns ⟨S, hSc, hSni, (val_or gs _ k hk ho).2 ⟨a, haIn, halt, hSv⟩⟩
                  have hexr : ∃ r' : Fin N, r' ≠ l ∧
                      val gs a (sg (N + N) (N + r'.val)) = true := by
                    by_contra hc
                    push Not at hc
                    obtain ⟨slot, hslot⟩ := List.getElem?_of_mem haIn
                    have hslot2 : slot < 2 := by
                      have hlt := (List.getElem?_eq_some_iff.1 hslot).1
                      have hlen2 := (legal gs[k] (List.mem_of_getElem? hgk)).2
                      omega
                    have hT2 : T2q N I gs k slot p l :=
                      ⟨gs[k], a, hgk, hslot, hns, ⟨l, r, hrl.symm, hvl, hvr⟩, hval,
                        fun r' hvr' => by
                          by_contra hne
                          exact hc r' hne hvr'⟩
                    exact (hlNoT k hk slot hslot2).2 hT2
                  exact (val_or gs _ k hk ho).2 ⟨a, haIn, halt, ih a halt hnsa hval hexr⟩
        -- Sublemma 2: induction on t along Dn chain
        have hSub2 : ∀ t w, Dn gs o (sg (N + N) (N + l.val)) t w →
            (∃ r : Fin N, r ≠ l ∧ D gs o (sg (N + N) (N + r.val)) w) →
            ∃ Stop : Finset (Fin N), Stop.card ≤ 1 ∧ (∀ r' ∈ Stop, ¬ I p r') ∧
              D gs o (lineSet N (Ubase ∪ Stop)) w := by
          intro t
          induction t with
          | zero =>
            intro w hw _
            have hwo : w = o := hw
            subst hwo
            exact ⟨∅, by simp, by simp, D_out gs o _⟩
          | succ t ih =>
            intro w hw ⟨r, hrl, hdr⟩
            by_cases hds : dSmall N I gs o w p
            · obtain ⟨Stop, hSc, hSni, hSd⟩ := hds
              refine ⟨Stop, hSc, hSni, D_mono gs o legal _ _ ?_ w hSd⟩
              exact lineSet_mono N Finset.subset_union_right
            · rcases (Dn_succ gs o (sg (N + N) (N + l.val)) t w).1 hw with hwo |
                ⟨k, g, slot, hg, hslot, hsib, hdn⟩
              · subst hwo
                exact ⟨∅, by simp, by simp, D_out gs o _⟩
              · have hk : k < gs.length := (List.getElem?_eq_some_iff.1 hg).1
                have hslot2 : slot < 2 := by
                  have hlt := (List.getElem?_eq_some_iff.1 hslot).1
                  have hlen2 := (legal g (List.mem_of_getElem? hg)).2
                  omega
                have hexr : ∃ r' : Fin N, r' ≠ l ∧
                    sib gs (sg (N + N) (N + r'.val)) g slot ∧
                    D gs o (sg (N + N) (N + r'.val)) (N + N + k) := by
                  by_contra hc
                  push Not at hc
                  have hT1 : T1q N I gs o k slot p l :=
                    ⟨g, w, hg, hslot, hds, ⟨l, r, hrl.symm, ⟨t + 1, hw⟩, hdr⟩,
                      hsib, ⟨t, hdn⟩, fun r' hs' hd' => by
                        by_contra hne
                        exact hc r' hne hs' hd'⟩
                  exact (hlNoT k hk slot hslot2).1 hT1
                obtain ⟨r', hr'ne, hsib', hdr'⟩ := hexr
                obtain ⟨Stop, hSc, hSni, hDk⟩ := ih (N + N + k) hdn ⟨r', hr'ne, hdr'⟩
                refine ⟨Stop, hSc, hSni, D_step gs o _ k g slot w hg hslot ?_ hDk⟩
                rcases hsib with hor | ⟨hand, hall⟩
                · exact Or.inl hor
                · rcases hsib' with hor' | ⟨_, hall'⟩
                  · rw [hand] at hor'; cases hor'
                  · right
                    refine ⟨hand, fun m u hm hms => ?_⟩
                    have hvl_u : val gs u (sg (N + N) (N + l.val)) = true := hall m u hm hms
                    have hvr'_u : val gs u (sg (N + N) (N + r'.val)) = true := hall' m u hm hms
                    by_cases hvsu : valSmall N I gs u p
                    · have hm2 : m < 2 := by
                        have hlt := (List.getElem?_eq_some_iff.1 hm).1
                        have hlen2 := (legal g (List.mem_of_getElem? hg)).2
                        omega
                      have hmeq : m = 1 - slot := by omega
                      rw [hmeq] at hm
                      have hksDp : (k, slot) ∈ Dp p :=
                        Finset.mem_filter.2 ⟨Finset.mem_product.2
                          ⟨Finset.mem_range.2 hk, Finset.mem_range.2 hslot2⟩,
                          g, w, hg, hslot, hds, l, r, hrl.symm, ⟨t + 1, hw⟩, hdr⟩
                      have hvPick := hpickD_val k slot g u hg hand hm hvsu
                      have hsubU : pickD (k, slot) ⊆ Ubase ∪ Stop := by
                        intro x hx
                        exact Finset.mem_union_left _ (Finset.mem_union_left _
                          (Finset.mem_biUnion.2 ⟨(k, slot), hksDp, hx⟩))
                      exact val_mono gs legal _ _ (lineSet_mono N hsubU) u hvPick
                    · have hvBase := hSub1 u hvsu hvl_u ⟨r', hr'ne, hvr'_u⟩
                      exact val_mono gs legal _ _
                        (lineSet_mono N Finset.subset_union_left) u hvBase
        -- Apply Sublemma 2 at p.val
        have hDl : D gs o (sg (N + N) (N + l.val)) p.val :=
          hD_EyP (p, l) (Finset.mem_filter.1 hlEp).2
        have hDl2 : D gs o (sg (N + N) (N + l2.val)) p.val :=
          hD_EyP (p, l2) (Finset.mem_filter.1 hl2Ep).2
        obtain ⟨t0, ht0⟩ := hDl
        obtain ⟨Stop, hStopCard, hStopNi, hDpU⟩ := hSub2 t0 p.val ht0 ⟨l2, hl2ne, hDl2⟩
        let U : Finset (Fin N) := Ubase ∪ Stop
        have hU_card : U.card ≤ (Dp p).card + 2 * (Vp p).card + 1 := by
          calc U.card ≤ Ubase.card + Stop.card := Finset.card_union_le _ _
            _ ≤ ((Dp p).card + 2 * (Vp p).card) + 1 := Nat.add_le_add hUbase_card hStopCard
        have hU_noninc : ∀ r ∈ U, ¬ I p r := by
          intro r hr
          rcases Finset.mem_union.1 hr with h1 | h2
          · exact hUbase_noninc r h1
          · exact hStopNi r h2
        -- Use snd + hsound to prove q < U.card
        have hq_lt_U : q < U.card := by
          by_contra hle
          have hUq : U.card ≤ q := by omega
          let z := pointAndLines N p U
          obtain ⟨tU, htU⟩ := hDpU
          have hz_true : val gs o z = true := by
            refine snd gs o legal hrb (lineSet N U) z
              (lineSet_le_pointAndLines N p U) tU p.val htU ?_
            have hpLt : p.val < N + N := by have := p.isLt; omega
            rw [val_input gs z p.val hpLt]
            have hfin : (⟨p.val, hpLt⟩ : Fin (N + N)) = Fin.castAdd N p := rfl
            rw [hfin]
            simp [z, pointAndLines_castAdd]
          have hz_lines : (Finset.univ.filter (fun r : Fin N => z (Fin.natAdd N r) = true)).card ≤ q := by
            have heqU : Finset.univ.filter (fun r : Fin N => z (Fin.natAdd N r) = true) = U := by
              ext r
              rw [Finset.mem_filter]
              simp only [Finset.mem_univ, true_and, z, pointAndLines_natAdd, decide_eq_true_eq]
            rw [heqU]
            exact hUq
          have hz_no : ¬ ∃ p' r' : Fin N, I p' r' ∧
              z (Fin.castAdd N p') = true ∧ z (Fin.natAdd N r') = true := by
            rintro ⟨p', r', hIpr, hzp', hzr'⟩
            simp only [z, pointAndLines_castAdd, decide_eq_true_eq] at hzp'
            simp only [z, pointAndLines_natAdd, decide_eq_true_eq] at hzr'
            subst hzp'
            exact hU_noninc r' hzr' hIpr
          have hz_false : val gs o z = false := hsound z hz_lines hz_no
          rw [hz_true] at hz_false
          exact Bool.noConfusion hz_false
        have hEp_le : (Ep p).card ≤ q + 1 := by
          have hsub : Ep p ⊆ Finset.univ.filter (fun r => I p r) := by
            intro r hr
            have hEy := (Finset.mem_filter.1 hr).2
            exact Finset.mem_filter.2 ⟨Finset.mem_univ r, (Finset.mem_filter.1 hEy).2.1⟩
          calc (Ep p).card ≤ (Finset.univ.filter (fun r => I p r)).card := Finset.card_le_card hsub
            _ = q + 1 := point_deg q N I hq hN hLine huniq p
        omega
  -- Global bounds on the three sums
  have hGoodE_card : GoodE.card ≤ 4 * C.size := by
    have hle : GoodE.card ≤
        ((Finset.range gs.length ×ˢ Finset.range 2) ×ˢ (Finset.univ : Finset Bool)).card := by
      apply card_rel _ _ (TTq N I gs o)
      · intro e he
        obtain ⟨_, k, hk, slot, hslot, hT⟩ := Finset.mem_filter.1 he
        rcases hT with h1 | h2
        · exact ⟨((k, slot), true), by simp [hk, hslot], Or.inl ⟨rfl, h1⟩⟩
        · exact ⟨((k, slot), false), by simp [hk, hslot], Or.inr ⟨rfl, h2⟩⟩
      · intro a a' b hab hab'
        exact TTq_inj N I gs o huniq a a' b hab hab'
    have hcard : ((Finset.range gs.length ×ˢ Finset.range 2) ×ˢ
        (Finset.univ : Finset Bool)).card = 4 * gs.length := by
      simp [Finset.card_product]; ring
    rw [hcard] at hle
    exact hle
  have hSumGood : ∑ p : Fin N, (GoodEp p).card = GoodE.card := by
    have h1 : GoodE.card = ∑ e : Fin N × Fin N, if e ∈ GoodE then 1 else 0 := by
      rw [← Finset.card_filter]
      congr 1; ext e; simp
    rw [h1, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.card_filter]
  have hSumEy : ∑ p : Fin N, (Ep p).card = EyP.card := by
    have h1 : EyP.card = ∑ e : Fin N × Fin N, if e ∈ EyP then 1 else 0 := by
      rw [← Finset.card_filter]
      congr 1; ext e; simp
    rw [h1, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.card_filter]
  have hSumDp : ∑ p : Fin N, (Dp p).card ≤ 2 * C.size := by
    have hdisj : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin N)) : Set (Fin N)) Dp := by
      intro p _ p' _ hpp
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨_, g, u, hg, hu, hnd, r1, r2, hne, hd1, hd2⟩ := Finset.mem_filter.1 hx
      obtain ⟨_, g', u', hg', hu', hnd', _⟩ := Finset.mem_filter.1 hx'
      rw [hg] at hg'; cases hg'
      rw [hu] at hu'; cases hu'
      exact hpp (eq_point_of_two_lines N I huniq p p' r1 r2 hne
        (inc_of_not_dSmall N I gs o u p r1 hnd hd1)
        (inc_of_not_dSmall N I gs o u p r2 hnd hd2)
        (inc_of_not_dSmall N I gs o u p' r1 hnd' hd1)
        (inc_of_not_dSmall N I gs o u p' r2 hnd' hd2))
    have hsub : Finset.univ.biUnion Dp ⊆ Finset.range gs.length ×ˢ Finset.range 2 := by
      intro x hx
      obtain ⟨p, _, hxp⟩ := Finset.mem_biUnion.1 hx
      exact (Finset.mem_filter.1 hxp).1
    calc ∑ p : Fin N, (Dp p).card
        = (Finset.univ.biUnion Dp).card := (Finset.card_biUnion hdisj).symm
      _ ≤ (Finset.range gs.length ×ˢ Finset.range 2).card := Finset.card_le_card hsub
      _ = 2 * C.size := by simp [Finset.card_product, Circuit.size, gs, Nat.mul_comm]
  have hSumVp : ∑ p : Fin N, (Vp p).card ≤ C.size := by
    have hdisj : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin N)) : Set (Fin N)) Vp := by
      intro p _ p' _ hpp
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro k hk hk'
      obtain ⟨_, hnv, r1, r2, hne, hv1, hv2⟩ := Finset.mem_filter.1 hk
      obtain ⟨_, hnv', _⟩ := Finset.mem_filter.1 hk'
      exact hpp (eq_point_of_two_lines N I huniq p p' r1 r2 hne
        (inc_of_not_valSmall N I gs (N + N + k) p r1 hnv hv1)
        (inc_of_not_valSmall N I gs (N + N + k) p r2 hnv hv2)
        (inc_of_not_valSmall N I gs (N + N + k) p' r1 hnv' hv1)
        (inc_of_not_valSmall N I gs (N + N + k) p' r2 hnv' hv2))
    have hsub : Finset.univ.biUnion Vp ⊆ Finset.range gs.length := by
      intro k hk
      obtain ⟨p, _, hkp⟩ := Finset.mem_biUnion.1 hk
      exact (Finset.mem_filter.1 hkp).1
    calc ∑ p : Fin N, (Vp p).card
        = (Finset.univ.biUnion Vp).card := (Finset.card_biUnion hdisj).symm
      _ ≤ (Finset.range gs.length).card := Finset.card_le_card hsub
      _ = C.size := by simp [Circuit.size, gs]
  have hTotal : ∑ p : Fin N, (Ep p).card ≤
      ∑ p : Fin N, ((GoodEp p).card + (Dp p).card + 2 * (Vp p).card + 1) :=
    Finset.sum_le_sum (fun p _ => hpoint p)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at hTotal
  rw [hSumEy, hSumGood] at hTotal
  change EyP.card ≤ 8 * C.size + N
  omega

theorem final (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hLine : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l1 : Fin N, I p1 l1 ∧ I p2 l1)
    (hao : AndOrFanInTwo C) (hrb : ReadsBack (N + N) C)
    (hsound : ∀ z : Fin (N + N) → Bool,
      (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N + N) C z = false) :
    N * q ≤ 32 * C.size + 3 * N + (doubleReread C (N + N) (fun w => decide (N ≤ w))
      ((List.finRange N).flatMap (fun p5 => ((List.finRange N).filter
        (fun l5 => decide (I p5 l5))).map (fun l6 => (p5.val, N + l6.val))))).length := by
  classical
  have hL := coreL q N I C hq huniq hao hrb hsound
  have hX := coreP_q q N I C hq hN hLine huniq hao hrb hsound
  let E : Finset (Fin N × Fin N) := Finset.univ.filter (fun e => I e.1 e.2)
  have hE : E.card = N * (q + 1) := by
    have h1 : E.card = ∑ e : Fin N × Fin N, if I e.1 e.2 then 1 else 0 := Finset.card_filter _ _
    rw [h1, Fintype.sum_prod_type_right]
    have h2 : ∀ l : Fin N, (∑ p : Fin N, if I p l then 1 else 0) = q + 1 := by
      intro l
      rw [← hLine l, Finset.card_filter]
    simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hneg : (fun i : ℕ => !decide (N ≤ i)) = (fun i => decide (i < N)) := by
    funext i
    by_cases h : N ≤ i
    · simp [h]
    · simp [h, Nat.lt_of_not_le h]
  let L := (List.finRange N).flatMap (fun p5 => ((List.finRange N).filter
        (fun l5 => decide (I p5 l5))).map (fun l6 => (p5.val, N + l6.val)))
  let Dl := doubleReread C (N + N) (fun w => decide (N ≤ w)) L
  let Ds : Finset (Fin N × Fin N) := E.filter (fun e =>
    lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
    lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false)
  have hDs : Ds.card ≤ Dl.length := by
    have himg : Ds.image (fun e => (e.1.val, N + e.2.val)) ⊆ Dl.toFinset := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨heE, h1, h2⟩ := Finset.mem_filter.1 he
      have hI : I e.1 e.2 := (Finset.mem_filter.1 heE).2
      rw [List.mem_toFinset]
      show (e.1.val, N + e.2.val) ∈ doubleReread C (N + N) (fun w => decide (N ≤ w)) L
      unfold doubleReread
      rw [List.mem_filter]
      refine ⟨?_, ?_⟩
      · simp only [L, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange,
          true_and, decide_eq_true_eq]
        exact ⟨e.1, e.2, hI, rfl⟩
      · rw [hneg]
        simp [h1, h2]
    have hinj : (Ds.image (fun e => (e.1.val, N + e.2.val))).card = Ds.card := by
      apply Finset.card_image_of_injective
      intro e e' h
      have h1 := (Prod.ext_iff.1 h).1
      have h2 := (Prod.ext_iff.1 h).2
      exact Prod.ext (Fin.ext h1) (Fin.ext (by simpa using h2))
    calc Ds.card = _ := hinj.symm
      _ ≤ Dl.toFinset.card := Finset.card_le_card himg
      _ ≤ Dl.length := List.toFinset_card_le _
  have hsub : E ⊆ (Ey N I C (fun i => decide (N ≤ i)) ∪ Ey N I C (fun i => decide (i < N))) ∪ Ds := by
    intro e he
    have hI : I e.1 e.2 := (Finset.mem_filter.1 he).2
    by_cases h1 : lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = true
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hI, h1⟩))
    · by_cases h2 : lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = true
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, hI, h2⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨he, by simpa using h1,
          by simpa using h2⟩)
  have hc := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le (Ey N I C (fun i => decide (N ≤ i)) ∪
    Ey N I C (fun i => decide (i < N))) Ds
  have hu2 := Finset.card_union_le (Ey N I C (fun i => decide (N ≤ i)))
    (Ey N I C (fun i => decide (i < N)))
  have hDl : Dl.length = (doubleReread C (N + N) (fun w => decide (N ≤ w))
      ((List.finRange N).flatMap (fun p5 => ((List.finRange N).filter
        (fun l5 => decide (I p5 l5))).map (fun l6 => (p5.val, N + l6.val))))).length := rfl
  rw [← hDl]
  have : N * (q + 1) = N * q + N := by ring
  omega

end PEqualNP.Outside.L_meta_3716

theorem PEqualNP.Outside.L_meta_3716 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l1 : Fin N, I p1 l1 ∧ I p2 l1) → PEqualNP.ReadK.AndOrFanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q → (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → N * q ≤ 32 * C.size + 3 * N + (PEqualNP.ReadK.doubleReread C (N + N) (fun w => decide (N ≤ w)) ((List.finRange N).flatMap (fun p5 => ((List.finRange N).filter (fun l5 => decide (I p5 l5))).map (fun l6 => (p5.val, N + l6.val))))).length := by
  intro q N I _ C hq hN hLine huniq hao hrb _ hsound
  exact PEqualNP.Outside.L_meta_3716.final q N I C hq hN hLine huniq hao hrb hsound
