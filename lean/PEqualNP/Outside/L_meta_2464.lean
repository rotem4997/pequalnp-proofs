import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2464

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
          · push_neg at hu
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
      · push_neg at hu
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

theorem start (gs : List Gate) (o n : ℕ) (isL : ℕ → Bool) (R : ℕ → ℕ → Bool)
    (hrb : RB n gs) (legal : Legal gs)
    (hsound : ∀ z : Fin n → Bool, val gs o z = true →
      ∃ i j : Fin n, R i.val j.val = true ∧ z i = true ∧ z j = true)
    (hR : ∀ a b, R a b = true → isL a = false ∧ isL b = true)
    (l : ℕ) (hln : l < n) (hl : isL l = true) : ¬ D gs o (off n isL R l) l := by
  rintro ⟨t, ht⟩
  have hz : val gs o (fun i : Fin n => off n isL R l i || decide (i.val = l)) = true := by
    refine snd gs o legal hrb (off n isL R l) _ (fun v hv => by simp [hv]) t l ht ?_
    rw [val_input gs _ l hln]
    simp
  obtain ⟨i, j, hRij, hzi, hzj⟩ := hsound _ hz
  obtain ⟨hi, hj⟩ := hR _ _ hRij
  have hjl : j.val = l := by
    simpa [off, hj] using hzj
  rw [hjl] at hRij
  have hil : i.val ≠ l := by
    intro e
    rw [e, hl] at hi
    exact Bool.noConfusion hi
  simp [off, hi, hRij, hil] at hzi

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
    (hsound : ∀ z : Fin n → Bool, circuitFun n C z = true →
      ∃ i j : Fin n, R i.val j.val = true ∧ z i = true ∧ z j = true)
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
      have hst := start C.gates C.output n isL R hrb legal hsound hR e.2 hen hl
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


def Rr (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (a b : ℕ) : Bool :=
  decide (∃ p l : Fin N, a = p.val ∧ b = N + l.val ∧ I p l)

theorem Rr_iff (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (a b : ℕ) :
    Rr N I a b = true ↔ ∃ p l : Fin N, a = p.val ∧ b = N + l.val ∧ I p l := by
  unfold Rr
  exact decide_eq_true_iff

def Ey (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) (isL : ℕ → Bool) :
    Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => I e.1 e.2 ∧ lineSingle C (N + N) isL e.1.val (N + e.2.val) = true)

theorem img_le (N : ℕ) (S : Finset (ℕ × ℕ)) (h : ∀ e ∈ S, e.2 < N + N) :
    (S.image Prod.snd).card ≤ N + N := by
  have hsub : S.image Prod.snd ⊆ Finset.range (N + N) := by
    intro b hb
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hb
    exact Finset.mem_range.2 (h e he)
  exact (Finset.card_le_card hsub).trans_eq (Finset.card_range _)

theorem img2 (n : ℕ) (C : Circuit) (isL : ℕ → Bool) (R : ℕ → ℕ → Bool)
    (hmono : AndOrFanInTwo C) (hrb0 : ReadsBack n C)
    (hsound : ∀ z : Fin n → Bool, circuitFun n C z = true →
      ∃ i j : Fin n, R i.val j.val = true ∧ z i = true ∧ z j = true)
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
      have hst := start C.gates C.output n isL R hrb legal hsound hR e.2 hen h2
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

theorem core2 (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l1 : Fin N, I p1 l1 ∧ I p2 l1)
    (hao : AndOrFanInTwo C) (hrb : ReadsBack (N + N) C)
    (hf : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = decide (∃ p3 l3 : Fin N,
      I p3 l3 ∧ z (Fin.castAdd N p3) = true ∧ z (Fin.natAdd N l3) = true)) :
    (Ey N I C (fun i => decide (i < N))).card ≤ 6 * C.size := by
  have hsoundR : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true →
      ∃ i j : Fin (N + N), Rr N I i.val j.val = true ∧ z i = true ∧ z j = true := by
    intro z hz
    rw [hf z, decide_eq_true_eq] at hz
    obtain ⟨p, l, hI, hp, hl⟩ := hz
    exact ⟨Fin.castAdd N p, Fin.natAdd N l, (Rr_iff N I _ _).2 ⟨p, l, rfl, rfl, hI⟩, hp, hl⟩
  have hsoundX : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true →
      ∃ i j : Fin (N + N), (fun a b => Rr N I b a) i.val j.val = true ∧
        z i = true ∧ z j = true := by
    intro z hz
    obtain ⟨i, j, h1, h2, h3⟩ := hsoundR z hz
    exact ⟨j, i, h1, h3, h2⟩
  have hRx : ∀ a b, (fun a b => Rr N I b a) a b = true →
      (fun i => decide (i < N)) a = false ∧ (fun i => decide (i < N)) b = true := by
    intro a b h
    obtain ⟨p, l, rfl, rfl, _⟩ := (Rr_iff N I _ _).1 h
    refine ⟨?_, ?_⟩
    · show decide (N + l.val < N) = false
      exact decide_eq_false (by omega)
    · show decide (p.val < N) = true
      exact decide_eq_true p.isLt
  have h4x : ∀ a a' b b', (fun a b => Rr N I b a) a b = true →
      (fun a b => Rr N I b a) a' b = true → (fun a b => Rr N I b a) a b' = true →
      (fun a b => Rr N I b a) a' b' = true → a ≠ a' → b = b' := by
    intro a a' b b' h1 h2 h3 h4 hne
    obtain ⟨p, l, rfl, rfl, i1⟩ := (Rr_iff N I _ _).1 h1
    obtain ⟨p2, l', e2, rfl, i2⟩ := (Rr_iff N I _ _).1 h2
    obtain ⟨p', l3, rfl, e3, i3⟩ := (Rr_iff N I _ _).1 h3
    obtain ⟨p4, l4, e4, e5, i4⟩ := (Rr_iff N I _ _).1 h4
    have ep2 : p2 = p := Fin.ext e2.symm
    have el3 : l3 = l := Fin.ext (by omega)
    have ep4 : p4 = p' := Fin.ext e4.symm
    have el4 : l4 = l' := Fin.ext (by omega)
    rw [ep2] at i2
    rw [el3] at i3
    rw [ep4, el4] at i4
    by_contra hc
    have hpp : p ≠ p' := fun h => hc (by rw [h])
    obtain ⟨l0, _, hu⟩ := huniq p p' hpp
    have ea := hu l ⟨i1, i3⟩
    have eb := hu l' ⟨i2, i4⟩
    exact hne (by rw [ea, eb])
  have hSx : ∀ e ∈ (Ey N I C (fun i => decide (i < N))).image (fun e => (N + e.2.val, e.1.val)),
      (fun a b => Rr N I b a) e.1 e.2 = true ∧ e.2 < N + N ∧ ∃ xs : List Bool,
      xs.length = N + N ∧
      (∀ i < N + N, xs.getD i false = true ↔ (i = e.1 ∨ i = e.2)) ∧
      ((linearParts C (fun i => decide (i < N)) xs).getD C.output (false, false)).2 = true := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨_, hI, hls⟩ := Finset.mem_filter.1 he0
    refine ⟨(Rr_iff N I _ _).2 ⟨e0.1, e0.2, rfl, rfl, hI⟩, ?_,
      (List.range (N + N)).map (fun i => i == e0.1.val || i == N + e0.2.val), by simp, ?_, hls⟩
    · show e0.1.val < N + N
      have := e0.1.isLt
      omega
    · intro i hi
      simp [List.getD_eq_getElem?_getD, hi, or_comm]
  have hx := gen (N + N) C (fun i => decide (i < N)) (fun a b => Rr N I b a) hao hrb hsoundX
    hRx h4x _ hSx
  have ix := img2 (N + N) C (fun i => decide (i < N)) (fun a b => Rr N I b a) hao hrb hsoundX
    hRx _ hSx
  have cx : ((Ey N I C (fun i => decide (i < N))).image (fun e => (N + e.2.val, e.1.val))).card
      = (Ey N I C (fun i => decide (i < N))).card := by
    apply Finset.card_image_of_injective
    intro e e' h
    have h1 := (Prod.ext_iff.1 h).1
    have h2 := (Prod.ext_iff.1 h).2
    exact Prod.ext (Fin.ext h2) (Fin.ext (by simpa using h1))
  omega

end PEqualNP.Outside.L_meta_2464

theorem PEqualNP.Outside.L_meta_2464 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Decidable.decide (∃ (x12 : Fin x2) (x13 : Fin x2), x3 x12 x13 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x2 x13) = Bool.true)) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x13 < x2)) (↑x12.1) (x2 + ↑x12.2) = Bool.true } ≤ (33 : ℕ) * x5.size := by
  intro q N I _ C _ _ _ huniq hao hf
  have hc := PEqualNP.Outside.L_meta_2464.core2 N I C huniq
    ⟨hao.1, fun g hg => le_of_eq (hao.2.2 g hg)⟩ hao.2.1 hf
  rw [Fintype.card_of_subtype (PEqualNP.Outside.L_meta_2464.Ey N I C (fun i => decide (i < N)))
    (fun x => by simp [PEqualNP.Outside.L_meta_2464.Ey])]
  omega
