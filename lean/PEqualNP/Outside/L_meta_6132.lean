import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6132

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def F : ℕ := 65535

def prs : List ℕ → List ℕ
  | [] => []
  | a :: l => (l.flatMap fun b => [Nat.land a b, Nat.lor a b]) ++ prs l

def cand (W : List ℕ) : List ℕ := F :: prs W

def mem (v : ℕ) : List ℕ → Bool
  | [] => false
  | a :: l => match Nat.beq v a with
    | true => true
    | false => mem v l

theorem mem_iff (v : ℕ) : ∀ l : List ℕ, mem v l = true ↔ v ∈ l
  | [] => by simp [mem]
  | a :: l => by
    rw [mem, List.mem_cons]
    cases h : Nat.beq v a with
    | true => simp [Nat.eq_of_beq_eq_true h]
    | false => simp [Nat.ne_of_beq_eq_false h, mem_iff v l]

def anyb {α : Type} (f : α → Bool) : List α → Bool
  | [] => false
  | a :: l => match f a with
    | true => true
    | false => anyb f l

theorem anyb_iff {α : Type} (f : α → Bool) : ∀ l : List α, anyb f l = true ↔ ∃ a ∈ l, f a = true
  | [] => by simp [anyb]
  | a :: l => by
    rw [anyb]
    cases h : f a with
    | true => simp [h]
    | false => simp [h, anyb_iff f l]

def force {α : Type} (v : ℕ) (f : ℕ → α) : α :=
  match v with
  | 0 => f 0
  | n + 1 => f (Nat.succ n)

theorem force_eq {α : Type} (v : ℕ) (f : ℕ → α) : force v f = f v := by cases v <;> rfl

def upd (w : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | (p, Q) :: l => match Nat.beq (Nat.land w p) 0 with
    | true => (p, Q) :: upd w l
    | false => match Nat.land Q w with
      | 0 => upd w l
      | n + 1 => (p, Nat.succ n) :: upd w l

def hit (W : List ℕ) : ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | k + 1, (p, Q) :: l => force (2 ^ Nat.log2 Q) fun q => anyb (fun w => match Nat.beq (Nat.land w p) 0 with
      | true => false
      | false => match Nat.beq (Nat.land w q) 0 with
        | false => false
        | true => hit W k (upd w ((p, Q) :: l))) W

def st0 (t : ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => []
  | i + 1 => match Nat.beq (Nat.land t (2 ^ i)) 0 with
    | true => st0 t i
    | false => match Nat.xor F t with
      | 0 => st0 t i
      | n + 1 => (2 ^ i, n + 1) :: st0 t i

def loop (f : ℕ → List ℕ → Bool) : List ℕ → List ℕ → Bool
  | [], _ => false
  | v :: cs, X => force v fun v => match mem v X with
    | true => loop f cs X
    | false => match f v X with
      | true => true
      | false => loop f cs (v :: X)

def two (t : ℕ) (W : List ℕ) : Bool :=
  anyb (fun v => force v fun v => match Nat.beq v t with
    | true => true
    | false => match Nat.beq (Nat.land v t) v with
      | true => anyb (fun w => Nat.beq (Nat.lor v w) t) W
      | false => match Nat.beq (Nat.land v t) t with
        | true => anyb (fun w => Nat.beq (Nat.land v w) t) W
        | false => false) (cand W)

def go (t : ℕ) : ℕ → List ℕ → List ℕ → Bool
  | 0, W, _ => mem t W
  | r + 1, W, X => match mem t W with
    | true => true
    | false => match hit W (r + 2) (st0 t 16) with
      | false => false
      | true => match r with
        | 0 => mem t (cand W)
        | 1 => two t W
        | r' + 2 => loop (fun v X' => go t r (v :: W) (v :: X')) (cand W) X

theorem tb (w i : ℕ) : Nat.beq (Nat.land w (2 ^ i)) 0 = !w.testBit i := by
  have e : Nat.land w (2 ^ i) = (w.testBit i).toNat * 2 ^ i := Nat.and_two_pow w i
  have hp : 0 < 2 ^ i := Nat.two_pow_pos i
  cases h : w.testBit i with
  | true =>
    rw [e, h]
    have : Nat.beq (true.toNat * 2 ^ i) 0 = false := by
      rw [← Bool.not_eq_true, Nat.beq_eq]; simp
    simpa using this
  | false => rw [e, h]; simp

theorem tbl (Q w i : ℕ) : (Nat.land Q w).testBit i = (Q.testBit i && w.testBit i) := Nat.testBit_and Q w i

/-- the state `l` is separated by the wires `ws` -/
def Sep (ws : List ℕ) (l : List (ℕ × ℕ)) : Prop :=
  ∀ e ∈ l, e.2 ≠ 0 ∧ ∃ i, e.1 = 2 ^ i ∧ ∀ q, e.2.testBit q = true → ∃ w ∈ ws, w.testBit i = true ∧ w.testBit q = false

theorem upd_sep (w : ℕ) (ws ws' : List ℕ) (hw : ∀ x ∈ ws, x ≠ w → x ∈ ws') :
    ∀ l : List (ℕ × ℕ), Sep ws l → Sep ws' (upd w l)
  | [], _ => by intro e he; simp [upd] at he
  | (p, Q) :: l, h => by
    have ih := upd_sep w ws ws' hw l fun e he => h e (List.mem_cons_of_mem _ he)
    obtain ⟨hQ, i, hp, hs⟩ := h (p, Q) List.mem_cons_self
    simp only at hQ hp hs
    rw [upd]
    subst hp
    rw [tb]
    cases hb : w.testBit i with
    | false =>
      simp only [Bool.not_false]
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · refine ⟨hQ, i, rfl, fun q hq => ?_⟩
        obtain ⟨x, hx, h1, h2⟩ := hs q hq
        refine ⟨x, hw x hx ?_, h1, h2⟩
        rintro rfl
        rw [hb] at h1; cases h1
      · exact ih e he
    | true =>
      simp only [Bool.not_true]
      cases hn : Nat.land Q w with
      | zero => exact ih
      | succ n =>
        intro e he
        rcases List.mem_cons.1 he with rfl | he
        · refine ⟨Nat.succ_ne_zero n, i, rfl, fun q hq => ?_⟩
          have hq' : (Nat.land Q w).testBit q = true := by rw [hn]; exact hq
          rw [tbl, Bool.and_eq_true] at hq'
          obtain ⟨x, hx, h1, h2⟩ := hs q hq'.1
          refine ⟨x, hw x hx ?_, h1, h2⟩
          rintro rfl
          rw [hq'.2] at h2; cases h2
        · exact ih e he

theorem hit_of (W : List ℕ) : ∀ (k : ℕ) (ws : List ℕ) (l : List (ℕ × ℕ)), (∀ w ∈ ws, w ∈ W) → ws.length ≤ k →
    Sep ws l → hit W k l = true
  | 0, _, [], _, _, _ => by simp [hit]
  | _ + 1, _, [], _, _, _ => by simp [hit]
  | 0, ws, (p, Q) :: l, _, hk, h => by
    obtain ⟨hQ, i, _, hs⟩ := h (p, Q) List.mem_cons_self
    obtain ⟨q, hq⟩ := Nat.exists_testBit_of_ne_zero hQ
    obtain ⟨w, hw, _⟩ := hs q hq
    have : ws = [] := List.length_eq_zero_iff.1 (by omega)
    subst this
    cases hw
  | k + 1, ws, (p, Q) :: l, hW, hk, h => by
    obtain ⟨hQ, i, hp, hs⟩ := h (p, Q) List.mem_cons_self
    simp only at hQ hp hs
    have hq : Q.testBit (Nat.log2 Q) = true := Nat.testBit_log2 hQ
    obtain ⟨w, hw, h1, h2⟩ := hs _ hq
    rw [hit, force_eq, anyb_iff]
    refine ⟨w, hW w hw, ?_⟩
    have e1 : Nat.beq (Nat.land w p) 0 = false := by rw [hp, tb, h1]; rfl
    have e2 : Nat.beq (Nat.land w (2 ^ Nat.log2 Q)) 0 = true := by rw [tb, h2]; rfl
    rw [e1, e2]
    refine hit_of W k (ws.erase w) _ (fun x hx => hW x (List.mem_of_mem_erase hx)) ?_ ?_
    · rw [List.length_erase_of_mem hw]
      omega
    · exact upd_sep w ws _ (fun x hx hne => (List.mem_erase_of_ne hne).2 hx) _ h

theorem st0_sep (t : ℕ) (ht : t < 2 ^ 16) (ws : List ℕ)
    (h : ∀ p < 16, ∀ q < 16, t.testBit p = true → t.testBit q = false → ∃ w ∈ ws, w.testBit p = true ∧ w.testBit q = false) :
    ∀ i ≤ 16, Sep ws (st0 t i) := by
  intro i
  induction i with
  | zero => intro _ e he; simp [st0] at he
  | succ i ih =>
    intro hi
    rw [st0, tb]
    cases hb : t.testBit i with
    | false => simpa using ih (by omega)
    | true =>
      simp only [Bool.not_true]
      cases hn : Nat.xor F t with
      | zero => exact ih (by omega)
      | succ n =>
        intro e he
        rcases List.mem_cons.1 he with rfl | he
        · refine ⟨Nat.succ_ne_zero n, i, rfl, fun q hq => ?_⟩
          have hq' : (Nat.xor F t).testBit q = true := by rw [hn]; exact hq
          have e2 : (Nat.xor F t).testBit q = (F.testBit q ^^ t.testBit q) := Nat.testBit_xor F t q
          have hF : F.testBit q = decide (q < 16) := by
            have : F = 2 ^ 16 - 1 := rfl
            rw [this, Nat.testBit_two_pow_sub_one]
          rw [e2, hF] at hq'
          have hq16 : q < 16 := by
            by_contra hge
            have e3 : t < 2 ^ q := lt_of_lt_of_le ht (Nat.pow_le_pow_right (by omega) (by omega))
            rw [Nat.testBit_lt_two_pow e3] at hq'
            simp [hge] at hq'
          have hqt : t.testBit q = false := by
            simpa [hq16] using hq'
          exact h i (by omega) q hq16 hb hqt
        · exact ih (by omega) e he

/-- one step: the value `v` from the values `W` -/
def St (W : List ℕ) (v : ℕ) : Prop := v = F ∨ ∃ a ∈ W, ∃ b ∈ W, v = Nat.land a b ∨ v = Nat.lor a b

def Der : List ℕ → List ℕ → Prop
  | _, [] => True
  | W, v :: S => St W v ∧ Der (v :: W) S

theorem St_mono {W W' : List ℕ} (h : ∀ x ∈ W, x ∈ W') {v : ℕ} : St W v → St W' v := by
  rintro (h1 | ⟨a, ha, b, hb, h1⟩)
  · exact Or.inl h1
  · exact Or.inr ⟨a, h a ha, b, h b hb, h1⟩

theorem Der_mono : ∀ (S W W' : List ℕ), (∀ x ∈ W, x ∈ W') → Der W S → Der W' S
  | [], _, _, _, _ => trivial
  | v :: S, W, W', h, hd => ⟨St_mono h hd.1, Der_mono S _ _ (by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (h x hx)) hd.2⟩

theorem Der_filter (v : ℕ) : ∀ (S W : List ℕ), v ∈ W → Der W S → Der W (S.filter fun x => !Nat.beq x v)
  | [], _, _, _ => trivial
  | u :: S, W, hv, hd => by
    rw [List.filter_cons]
    cases h : Nat.beq u v with
    | true =>
      have e := Nat.eq_of_beq_eq_true h
      subst e
      refine Der_filter u S W hv (Der_mono S _ _ ?_ hd.2)
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hv
      · exact hx
    | false => exact ⟨hd.1, Der_filter v S (u :: W) (List.mem_cons_of_mem _ hv) hd.2⟩

theorem prs_mem : ∀ (W : List ℕ) (a b : ℕ), a ∈ W → b ∈ W →
    (Nat.land a b ∈ W ∨ Nat.land a b ∈ prs W) ∧ (Nat.lor a b ∈ W ∨ Nat.lor a b ∈ prs W)
  | [], a, b, h, _ => by simp at h
  | c :: l, a, b, ha, hb => by
    have cl : ∀ x y : ℕ, Nat.land x y = Nat.land y x := Nat.and_comm
    have co : ∀ x y : ℕ, Nat.lor x y = Nat.lor y x := Nat.or_comm
    have il : ∀ x : ℕ, Nat.land x x = x := Nat.and_self
    have io : ∀ x : ℕ, Nat.lor x x = x := Nat.or_self
    by_cases e : a = b
    · subst e
      rw [il, io]
      exact ⟨Or.inl ha, Or.inl ha⟩
    have key : ∀ a b : ℕ, a = c → b ∈ l → (Nat.land a b ∈ prs (c :: l)) ∧ (Nat.lor a b ∈ prs (c :: l)) := by
      rintro a b rfl hb
      simp only [prs, List.mem_append, List.mem_flatMap]
      exact ⟨Or.inl ⟨b, hb, by simp⟩, Or.inl ⟨b, hb, by simp⟩⟩
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd rfl e
      · exact ⟨Or.inr (key _ _ rfl hb').1, Or.inr (key _ _ rfl hb').2⟩
    · rcases List.mem_cons.1 hb with rfl | hb'
      · rw [cl, co]
        exact ⟨Or.inr (key _ _ rfl ha').1, Or.inr (key _ _ rfl ha').2⟩
      · obtain ⟨h1, h2⟩ := prs_mem l a b ha' hb'
        refine ⟨?_, ?_⟩
        · rcases h1 with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · right; simp only [prs, List.mem_append]; exact Or.inr h
        · rcases h2 with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · right; simp only [prs, List.mem_append]; exact Or.inr h

theorem St_cand {W : List ℕ} {v : ℕ} (h : St W v) : v ∈ W ∨ v ∈ cand W := by
  rcases h with rfl | ⟨a, ha, b, hb, rfl | rfl⟩
  · exact Or.inr List.mem_cons_self
  · rcases (prs_mem W a b ha hb).1 with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)
  · rcases (prs_mem W a b ha hb).2 with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem F_bit (q : ℕ) (hq : q < 16) : F.testBit q = true := by
  have : F = 2 ^ 16 - 1 := rfl
  rw [this, Nat.testBit_two_pow_sub_one]
  simpa using hq

theorem sepd (t : ℕ) : ∀ (S W : List ℕ), Der W S → (t ∈ W ∨ t ∈ S) → ∃ ws : List ℕ, (∀ w ∈ ws, w ∈ W) ∧ ws.length ≤ S.length + 1 ∧
    ∀ p < 16, ∀ q < 16, t.testBit p = true → t.testBit q = false → ∃ w ∈ ws, w.testBit p = true ∧ w.testBit q = false
  | [], W, _, ht => by
    rcases ht with ht | ht
    · exact ⟨[t], by simpa using ht, by simp, fun p _ q _ h1 h2 => ⟨t, by simp, h1, h2⟩⟩
    · cases ht
  | v :: S, W, hd, ht => by
    obtain ⟨ws, h1, h2, h3⟩ := sepd t S (v :: W) hd.2 (by
      rcases ht with ht | ht
      · exact Or.inl (List.mem_cons_of_mem _ ht)
      · rcases List.mem_cons.1 ht with rfl | ht
        · exact Or.inl List.mem_cons_self
        · exact Or.inr ht)
    by_cases hv : v ∈ ws
    · have hlen : (ws.filter fun x => !Nat.beq x v).length + 1 ≤ ws.length := by
        have : (ws.filter fun x => !Nat.beq x v).length < ws.length := by
          rw [List.length_filter_lt_length_iff_exists]
          exact ⟨v, hv, by simp⟩
        omega
      have hsub : ∀ w ∈ ws.filter (fun x => !Nat.beq x v), w ∈ W := by
        intro w hw
        rw [List.mem_filter] at hw
        rcases List.mem_cons.1 (h1 w hw.1) with rfl | h
        · simp at hw
        · exact h
      have keep : ∀ w ∈ ws, w ≠ v → w ∈ ws.filter (fun x => !Nat.beq x v) := by
        intro w hw hne
        rw [List.mem_filter]
        refine ⟨hw, ?_⟩
        rw [Bool.not_eq_true', ← Bool.not_eq_true, Nat.beq_eq]
        exact hne
      rcases hd.1 with rfl | ⟨a, ha, b, hb, hval⟩
      · refine ⟨ws.filter (fun x => !Nat.beq x F), hsub, by simp only [List.length_cons]; omega, fun p hp q hq e1 e2 => ?_⟩
        obtain ⟨w, hw, e3, e4⟩ := h3 p hp q hq e1 e2
        refine ⟨w, keep w hw ?_, e3, e4⟩
        rintro rfl
        rw [F_bit q hq] at e4; cases e4
      · refine ⟨a :: b :: ws.filter (fun x => !Nat.beq x v), ?_, by simp only [List.length_cons]; omega, fun p hp q hq e1 e2 => ?_⟩
        · intro w hw
          rcases List.mem_cons.1 hw with rfl | hw
          · exact ha
          rcases List.mem_cons.1 hw with rfl | hw
          · exact hb
          · exact hsub w hw
        · obtain ⟨w, hw, e3, e4⟩ := h3 p hp q hq e1 e2
          by_cases e : w = v
          · rw [e] at e3 e4
            rcases hval with hval | hval
            · have b1 : ∀ i, v.testBit i = (a.testBit i && b.testBit i) := by intro i; rw [hval]; exact Nat.testBit_and a b i
              rw [b1, Bool.and_eq_true] at e3
              rw [b1, Bool.and_eq_false_iff] at e4
              rcases e4 with e4 | e4
              · exact ⟨a, by simp, e3.1, e4⟩
              · exact ⟨b, by simp, e3.2, e4⟩
            · have b1 : ∀ i, v.testBit i = (a.testBit i || b.testBit i) := by intro i; rw [hval]; exact Nat.testBit_or a b i
              rw [b1, Bool.or_eq_true] at e3
              rw [b1, Bool.or_eq_false_iff] at e4
              rcases e3 with e3 | e3
              · exact ⟨a, by simp, e3, e4.1⟩
              · exact ⟨b, by simp, e3, e4.2⟩
          · exact ⟨w, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (keep w hw e)), e3, e4⟩
    · refine ⟨ws, ?_, by simp only [List.length_cons]; omega, h3⟩
      intro w hw
      rcases List.mem_cons.1 (h1 w hw) with rfl | h
      · exact absurd hw hv
      · exact h

theorem loop_of (f : ℕ → List ℕ → Bool) (S : List ℕ) (hf : ∀ v ∈ S, ∀ X, (∀ x ∈ S, x ∉ X) → f v X = true) :
    ∀ (cs X : List ℕ), (∃ v ∈ cs, v ∈ S) → (∀ x ∈ S, x ∉ X) → loop f cs X = true
  | [], _, h, _ => by obtain ⟨v, hv, _⟩ := h; cases hv
  | c :: cs, X, h, hX => by
    rw [loop, force_eq]
    by_cases hc : c ∈ S
    · have : mem c X = false := by
        rw [← Bool.not_eq_true, mem_iff]; exact hX c hc
      rw [this, hf c hc X hX]
    · have h' : ∃ v ∈ cs, v ∈ S := by
        obtain ⟨v, hv, hvS⟩ := h
        rcases List.mem_cons.1 hv with rfl | hv
        · exact absurd hvS hc
        · exact ⟨v, hv, hvS⟩
      cases mem c X with
      | true => exact loop_of f S hf cs X h' hX
      | false =>
        have := loop_of f S hf cs (c :: X) h' (by
          intro x hx hxc
          rcases List.mem_cons.1 hxc with rfl | hxc
          · exact hc hx
          · exact hX x hx hxc)
        simp only [this]
        cases f c X <;> rfl

theorem two_of (t : ℕ) (W : List ℕ) (v u : ℕ) (h1 : St W v) (h2 : St (v :: W) u) (ht : t = v ∨ t = u) : t ∈ W ∨ two t W = true := by
  have vt : t ∈ cand W → two t W = true := by
    intro h
    rw [two, anyb_iff]
    refine ⟨t, h, ?_⟩
    rw [force_eq]
    have : Nat.beq t t = true := by simp
    rw [this]
  have tr : St W t → t ∈ W ∨ two t W = true := fun h => (St_cand h).imp_right vt
  rcases ht with rfl | rfl
  · exact tr h1
  rcases St_cand h1 with hvW | hvc
  · refine tr (St_mono ?_ h2)
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hvW
    · exact hx
  have fin : ∀ b ∈ W, (t = Nat.land v b ∨ t = Nat.lor v b) → t ∈ W ∨ two t W = true := by
    intro b hb hval
    right
    rw [two, anyb_iff]
    refine ⟨v, hvc, ?_⟩
    rw [force_eq]
    cases e0 : Nat.beq v t with
    | true => rfl
    | false =>
      rcases hval with hval | hval
      · have e1 : Nat.beq (Nat.land v t) v = false := by
          rw [← Bool.not_eq_true, Nat.beq_eq]
          intro e
          have : Nat.land v t = t := by
            rw [hval]
            refine Nat.eq_of_testBit_eq fun i => ?_
            have b1 : ∀ x y : ℕ, (Nat.land x y).testBit i = (x.testBit i && y.testBit i) := fun x y => Nat.testBit_and x y i
            rw [b1, b1]; cases v.testBit i <;> simp
          exact absurd (e.symm.trans this) (by simpa using Nat.ne_of_beq_eq_false e0)
        have e2 : Nat.beq (Nat.land v t) t = true := by
          rw [Nat.beq_eq, hval]
          refine Nat.eq_of_testBit_eq fun i => ?_
          have b1 : ∀ x y : ℕ, (Nat.land x y).testBit i = (x.testBit i && y.testBit i) := fun x y => Nat.testBit_and x y i
          rw [b1, b1]; cases v.testBit i <;> simp
        simp only [e1, e2]
        rw [anyb_iff]
        exact ⟨b, hb, by rw [Nat.beq_eq, hval]⟩
      · have e1 : Nat.beq (Nat.land v t) v = true := by
          rw [Nat.beq_eq, hval]
          refine Nat.eq_of_testBit_eq fun i => ?_
          have b1 : ∀ x y : ℕ, (Nat.land x y).testBit i = (x.testBit i && y.testBit i) := fun x y => Nat.testBit_and x y i
          have b2 : ∀ x y : ℕ, (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) := fun x y => Nat.testBit_or x y i
          rw [b1, b2]; cases v.testBit i <;> simp
        simp only [e1]
        rw [anyb_iff]
        exact ⟨b, hb, by rw [Nat.beq_eq, hval]⟩
  rcases h2 with rfl | ⟨a, ha, b, hb, hval⟩
  · exact tr (Or.inl rfl)
  rcases List.mem_cons.1 ha with hav | ha'
  · rcases List.mem_cons.1 hb with hbv | hb'
    · have : t = v := by
        rw [hav, hbv] at hval
        rcases hval with h | h
        · exact h.trans (Nat.and_self v)
        · exact h.trans (Nat.or_self v)
      exact Or.inr (vt (this ▸ hvc))
    · rw [hav] at hval
      exact fin b hb' hval
  · rcases List.mem_cons.1 hb with hbv | hb'
    · rw [hbv] at hval
      refine fin a ha' ?_
      rcases hval with h | h
      · exact Or.inl (h.trans (Nat.and_comm _ _))
      · exact Or.inr (h.trans (Nat.or_comm _ _))
    · exact tr (Or.inr ⟨a, ha', b, hb', hval⟩)

theorem go_of (t : ℕ) (ht : t < 2 ^ 16) : ∀ (r : ℕ) (S W X : List ℕ), S.length ≤ r → Der W S → (t ∈ W ∨ t ∈ S) → (∀ x ∈ S, x ∉ X) → (∀ x ∈ S, x ∉ W) → go t r W X = true := by
  intro r
  induction r with
  | zero =>
    intro S W X hr hd hS hX hSW
    have : S = [] := List.length_eq_zero_iff.1 (by omega)
    subst this
    unfold go
    rw [mem_iff]
    simpa using hS
  | succ r ih =>
    intro S W X hr hd hS hX hSW
    unfold go
    cases hm : mem t W with
    | true => rfl
    | false =>
      have htW : t ∉ W := by rw [← mem_iff, hm]; simp
      have hit' : hit W (r + 2) (st0 t 16) = true := by
        obtain ⟨ws, h1, h2, h3⟩ := sepd t S W hd hS
        exact hit_of W _ ws _ h1 (by omega) (st0_sep t ht ws h3 16 le_rfl)
      rw [hit']
      have htS : t ∈ S := hS.resolve_left htW
      rcases r with _ | _ | r
      · rcases S with _ | ⟨v, _ | ⟨u, S⟩⟩
        · cases htS
        · have : t = v := by simpa using htS
          subst this
          simp only [mem_iff]
          exact (St_cand hd.1).resolve_left htW
        · simp at hr
      · rcases S with _ | ⟨v, _ | ⟨u, _ | ⟨y, S⟩⟩⟩
        · cases htS
        · have : t = v := by simpa using htS
          exact (two_of t W v v hd.1 (Or.inr ⟨v, by simp, v, by simp, Or.inl (Nat.and_self v).symm⟩) (Or.inl this)).resolve_left htW
        · exact (two_of t W v u hd.1 hd.2.1 (by simpa using htS)).resolve_left htW
        · simp at hr
      · refine loop_of _ S ?_ (cand W) X ?_ hX
        · intro v hv X' hX'
          have hd2 : Der (v :: W) (S.filter fun x => !Nat.beq x v) :=
            Der_filter v S (v :: W) List.mem_cons_self (Der_mono S W _ (fun x hx => List.mem_cons_of_mem _ hx) hd)
          have hlen : (S.filter fun x => !Nat.beq x v).length < S.length := by
            rw [List.length_filter_lt_length_iff_exists]
            exact ⟨v, hv, by simp⟩
          refine ih _ (v :: W) (v :: X') (by omega) hd2 ?_ ?_ ?_
          · by_cases e : t = v
            · exact Or.inl (by simp [e])
            · right
              rw [List.mem_filter]
              refine ⟨htS, ?_⟩
              rw [Bool.not_eq_true', ← Bool.not_eq_true, Nat.beq_eq]
              exact e
          · intro x hx hxv
            rw [List.mem_filter] at hx
            rcases List.mem_cons.1 hxv with rfl | hxv
            · simp at hx
            · exact hX' x hx.1 hxv
          · intro x hx hxv
            rw [List.mem_filter] at hx
            rcases List.mem_cons.1 hxv with rfl | hxv
            · simp at hx
            · exact hSW x hx.1 hxv
        · rcases S with _ | ⟨v, S⟩
          · cases htS
          · exact ⟨v, (St_cand hd.1).resolve_left (hSW v List.mem_cons_self), List.mem_cons_self⟩

def tv (g : Gate) (T : List ℕ) : ℕ :=
  match g.op, g.inputs with
  | GateOp.and, [] => F
  | GateOp.and, [i] => T.getD i 0
  | GateOp.and, i :: j :: _ => Nat.land (T.getD i 0) (T.getD j 0)
  | _, [] => 0
  | _, [i] => T.getD i 0
  | _, i :: j :: _ => Nat.lor (T.getD i 0) (T.getD j 0)

def trun (gs : List Gate) (T : List ℕ) : List ℕ := gs.foldl (fun w g => w ++ [tv g w]) T


theorem tv_st (g : Gate) (T W : List ℕ) (h0 : 0 ∈ W) (hT : ∀ i, T.getD i 0 ∈ W) : St W (tv g T) := by
  have one : ∀ x ∈ W, St W x := fun x hx => Or.inr ⟨x, hx, x, hx, Or.inl (Nat.and_self x).symm⟩
  unfold tv
  split
  · exact Or.inl rfl
  · exact one _ (hT _)
  · exact Or.inr ⟨_, hT _, _, hT _, Or.inl rfl⟩
  · exact one _ h0
  · exact one _ (hT _)
  · exact Or.inr ⟨_, hT _, _, hT _, Or.inr rfl⟩

theorem sound (t o : ℕ) : ∀ (gs : List Gate) (T W : List ℕ), 0 ∈ W → (∀ i, T.getD i 0 ∈ W) →
    (trun gs T).getD o 0 = t → ∃ S : List ℕ, S.length ≤ gs.length ∧ Der W S ∧ (t ∈ W ∨ t ∈ S) ∧ ∀ x ∈ S, x ∉ W
  | [], T, W, _, hT, h => by
    have := hT o
    simp only [trun, List.foldl_nil] at h
    rw [h] at this
    exact ⟨[], le_rfl, trivial, Or.inl this, by simp⟩
  | g :: gs, T, W, h0, hT, h => by
    have hT' : ∀ W' : List ℕ, (∀ i, T.getD i 0 ∈ W') → 0 ∈ W' → tv g T ∈ W' → ∀ i, (T ++ [tv g T]).getD i 0 ∈ W' := by
      intro W' h1 h2 h3 i
      rcases Nat.lt_trichotomy i T.length with hl | hl | hl
      · have : (T ++ [tv g T]).getD i 0 = T.getD i 0 := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hl]
        rw [this]; exact h1 i
      · have : (T ++ [tv g T]).getD i 0 = tv g T := by
          subst hl; simp [List.getD_eq_getElem?_getD]
        rw [this]; exact h3
      · rw [List.getD_eq_default _ _ (by simp; omega)]; exact h2
    have hr : (trun gs (T ++ [tv g T])).getD o 0 = t := h
    by_cases hv : tv g T ∈ W
    · obtain ⟨S, h1, h2, h3, h4⟩ := sound t o gs _ W h0 (hT' W hT h0 hv) hr
      exact ⟨S, by simp only [List.length_cons]; omega, h2, h3, h4⟩
    · obtain ⟨S, h1, h2, h3, h4⟩ := sound t o gs _ (tv g T :: W) (by simp [h0]) (hT' _ (fun i => List.mem_cons_of_mem _ (hT i))
        (by simp [h0]) (by simp)) hr
      refine ⟨tv g T :: S, by simp only [List.length_cons]; omega, ⟨tv_st g T W h0 hT, h2⟩, ?_, ?_⟩
      · rcases h3 with h3 | h3
        · rcases List.mem_cons.1 h3 with h3 | h3
          · exact Or.inr (by simp [h3])
          · exact Or.inl h3
        · exact Or.inr (List.mem_cons_of_mem _ h3)
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hv
        · exact fun hW => h4 x hx (List.mem_cons_of_mem _ hW)

theorem bits (p : ℕ) (hp : p < 16) (x : List Bool) : ∀ (gs : List Gate) (T : List ℕ),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) → T.length = x.length →
    (∀ i, (T.getD i 0).testBit p = x.getD i false) →
    ∀ i, ((trun gs T).getD i 0).testBit p =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD i false
  | [], T, _, _, h => h
  | g :: gs, T, hg, hl, h => by
    have hgv : (tv g T).testBit p = g.op.eval (g.inputs.map fun i => x.getD i false) := by
      obtain ⟨hop, hlen⟩ := hg g (by simp)
      rcases g with ⟨op, l⟩
      simp only at hop hlen
      have hF : F.testBit p = true := by
        have : F = 2 ^ 16 - 1 := rfl
        rw [this, Nat.testBit_two_pow_sub_one]; simpa using hp
      rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · rcases hop with rfl | rfl
        · simpa [tv, GateOp.eval] using hF
        · simp [tv, GateOp.eval]
      · rcases hop with rfl | rfl
        · simpa [tv, GateOp.eval] using h a
        · simpa [tv, GateOp.eval] using h a
      · rcases hop with rfl | rfl
        · have e : (tv ⟨GateOp.and, [a, b]⟩ T).testBit p = ((T.getD a 0).testBit p && (T.getD b 0).testBit p) := Nat.testBit_and _ _ _
          rw [e, h a, h b]; simp [GateOp.eval]
        · have e : (tv ⟨GateOp.or, [a, b]⟩ T).testBit p = ((T.getD a 0).testBit p || (T.getD b 0).testBit p) := Nat.testBit_or _ _ _
          rw [e, h a, h b]; simp [GateOp.eval]
      · simp at hlen
    refine bits p hp (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) gs (T ++ [tv g T])
      (fun g' h' => hg g' (by simp [h'])) (by simp [hl]) fun i => ?_
    rcases Nat.lt_trichotomy i T.length with hlt | hlt | hlt
    · have e1 : (T ++ [tv g T]).getD i 0 = T.getD i 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [e1, h i, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega)]
    · have e1 : (T ++ [tv g T]).getD i 0 = tv g T := by
        subst hlt; simp [List.getD_eq_getElem?_getD]
      rw [e1, hgv, hlt, hl]
      simp [List.getD_eq_getElem?_getD]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      simp

theorem tv_lt (g : Gate) (T : List ℕ) (h : ∀ i, T.getD i 0 < 2 ^ 16) : tv g T < 2 ^ 16 := by
  unfold tv
  split
  · simp [F]
  · exact h _
  · exact lt_of_le_of_lt Nat.and_le_left (h _)
  · simp
  · exact h _
  · exact Nat.or_lt_two_pow (h _) (h _)

theorem trun_lt : ∀ (gs : List Gate) (T : List ℕ), (∀ i, T.getD i 0 < 2 ^ 16) →
    ∀ i, (trun gs T).getD i 0 < 2 ^ 16
  | [], _, h => h
  | g :: gs, T, h => by
    refine trun_lt gs (T ++ [tv g T]) fun i => ?_
    rcases Nat.lt_trichotomy i T.length with hl | hl | hl
    · have : (T ++ [tv g T]).getD i 0 = T.getD i 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hl]
      rw [this]; exact h i
    · have : (T ++ [tv g T]).getD i 0 = tv g T := by
        subst hl; simp [List.getD_eq_getElem?_getD]
      rw [this]; exact tv_lt g T h
    · rw [List.getD_eq_default _ _ (by simp; omega)]; simp

def T0 : List ℕ := [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]

theorem lower (mask k : ℕ) (hm : mask < 2 ^ 16) (hs : go mask k (0 :: T0) (0 :: T0) = false) :
    ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => mask.testBit (4 * u.val + v.val)) k := by
  rintro ⟨C, hC, hsz, hrep⟩
  have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g h
    have := hC g h
    exact ⟨by simpa using this.1, this.2⟩
  have hT0 : ∀ i, T0.getD i 0 < 2 ^ 16 := by
    intro i
    by_cases hi : i < 8
    · interval_cases i <;> simp [T0]
    · rw [List.getD_eq_default _ _ (by simp [T0]; omega)]; simp
  have hout : (trun C.gates T0).getD C.output 0 = mask := by
    refine Nat.eq_of_testBit_eq fun p => ?_
    by_cases hp : p < 16
    · have hb := bits p hp (PEqualNP.Represents.oneEach (⟨p / 4, by omega⟩ : Fin 4) (⟨p % 4, by omega⟩ : Fin 4))
        C.gates T0 hg (by simp [T0, PEqualNP.Represents.oneEach]) (by
          intro i
          by_cases hi : i < 8
          · interval_cases p <;> interval_cases i <;> rfl
          · rw [List.getD_eq_default _ _ (by simp [T0]; omega),
              List.getD_eq_default _ _ (by simp [PEqualNP.Represents.oneEach]; omega)]
            simp) C.output
      rw [hb]
      have := hrep (⟨p / 4, by omega⟩ : Fin 4) (⟨p % 4, by omega⟩ : Fin 4)
      have e : 4 * (p / 4) + p % 4 = p := Nat.div_add_mod p 4
      simp only [e] at this
      exact this
    · have e : 2 ^ 16 ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (trun_lt C.gates T0 hT0 _) e),
        Nat.testBit_lt_two_pow (by omega)]
  obtain ⟨S, h1, h2, h3, h4⟩ := sound mask C.output C.gates T0 (0 :: T0) (by simp) (by
    intro i
    by_cases hi : i < 8
    · interval_cases i <;> simp [T0]
    · rw [List.getD_eq_default _ _ (by simp [T0]; omega)]; simp) hout
  have h5 := go_of mask hm k S (0 :: T0) (0 :: T0) (le_trans h1 hsz) h2 h3 h4 h4
  rw [hs] at h5
  cases h5

theorem shape (g : Gate) (h : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
  ⟨by rcases h.1 with e | e <;> simp [e], h.2⟩

end PEqualNP.Outside.L_meta_6132

open PEqualNP.Outside.L_meta_6132 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_6132 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (7918 : ℕ).testBit (4 * u.val + v.val)) 7 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (7918 : ℕ).testBit (4 * u.val + v.val)) 6 := by
  refine ⟨⟨⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.and, [12, 13]⟩], 14⟩, ?_, by decide, ?_⟩, lower 7918 6 (by decide) (by decide +kernel)⟩
  · intro g hg
    refine shape g ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
