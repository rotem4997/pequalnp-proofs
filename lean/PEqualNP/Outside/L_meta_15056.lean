import PEqualNP.Defs

-- The elimination of essential inputs and the normalized gate semantics are adapted
-- from L_meta_11441 (also L_meta_10886 and L_meta_9564). The six-vertex signed
-- fan certificate is adapted from L_meta_10600, L_meta_9136 and L_meta_8633
-- (Apache-2.0). Fixing the two remaining inputs, 3 and 4, saves two binary gates.
namespace PEqualNP.Outside.L_meta_15056

def zeroGate (k : Fin 4) (a b : Bool) : Bool :=
  match k.val with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => !a && b

theorem zeroGate_canalizes :
    ∀ k : Fin 4,
      (∃ b c : Bool, ∀ a : Bool, zeroGate k a b = c) ∧
      (∃ a c : Bool, ∀ b : Bool, zeroGate k a b = c) := by
  decide

def singleInput {n : Nat} (i : Fin n) : Fin n → Bool :=
  fun j => decide (j = i)

def pairInput {n : Nat} (i j : Fin n) : Fin n → Bool :=
  fun k => decide (k = i ∨ k = j)

section Generic
variable {α : Type} {β : Type}

def UC (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) : ℕ → (α → Prop) → α → Prop
  | 0, S, f => S f
  | t + 1, S, f => UC G A t S f ∨
      ∃ k a b, A k ∧ S a ∧ S b ∧ UC G A t (fun w => w = G k a b ∨ S w) f

theorem UC_monoS (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) :
    ∀ (t : ℕ) (S S' : α → Prop) (f : α), (∀ w, S w → S' w) → UC G A t S f → UC G A t S' f
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_monoS G A t S S' f h hu)
    · exact Or.inr ⟨k, a, b, hk, h a ha, h b hb,
        UC_monoS G A t _ _ f (fun w hw => hw.imp id (h w)) hu⟩

theorem UC_le {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t t' : ℕ} {S : α → Prop} {f : α}
    (h : t ≤ t') (hu : UC G A t S f) : UC G A t' S f := by
  induction h with
  | refl => exact hu
  | step _ ih => exact Or.inl ih

theorem UC_gate {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t : ℕ} {S : α → Prop} {f : α}
    (k : Fin 4) (a b : α) (hk : A k) (ha : S a) (hb : S b)
    (hu : UC G A t (fun w => w = G k a b ∨ S w) f) : UC G A (t + 1) S f :=
  Or.inr ⟨k, a, b, hk, ha, hb, hu⟩

theorem UC_map {G : Fin 4 → α → α → α} {G' : Fin 4 → β → β → β} {A : Fin 4 → Prop} (e : α → β)
    (he : ∀ k a b, e (G k a b) = G' k (e a) (e b)) :
    ∀ (t : ℕ) (S : α → Prop) (S' : β → Prop) (f : α), (∀ w, S w → S' (e w)) →
      UC G A t S f → UC G' A t S' (e f)
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_map e he t S S' f h hu)
    · refine Or.inr ⟨k, e a, e b, hk, h a ha, h b hb, UC_map e he t _ _ f ?_ hu⟩
      intro w hw
      rcases hw with rfl | hw
      · exact Or.inl (he k a b)
      · exact Or.inr (h w hw)

def TR (G : Fin 4 → α → α → α) (C : Fin 4 → α → α → Prop) (ys : List α) (t : ℕ)
    (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 ys →
    (∀ s xs zs, List.Perm xs zs → P s xs → P s zs) →
    (∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) →
    P t ws

section Run
variable {G : Fin 4 → α → α → α} {C : Fin 4 → α → α → Prop} {ys : List α}

theorem TR.done : TR G C ys 0 ys := fun _ d _ _ => d

theorem TR.perm {s : ℕ} {xs zs : List α} (p : List.Perm xs zs) (h : TR G C ys s xs) :
    TR G C ys s zs := fun P d q st => q s xs zs p (h P d q st)

theorem TR.step {s : ℕ} {a b : α} {r : List α} (k : Fin 4) (u : ℕ) (hc : C k a b)
    (h : TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) :
    TR G C ys (s + 1) (a :: b :: r) := fun P d q st => st s a b r k u hc (h P d q st)

theorem TR.ind {P : ℕ → List α → Prop} {t : ℕ} {ws : List α} (h : TR G C ys t ws)
    (d : P 0 ys)
    (p : ∀ s xs zs, List.Perm xs zs → TR G C ys s xs → P s xs → P s zs)
    (st : ∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      TR G C ys s (List.replicate (u + 1) (G k a b) ++ r) →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) : P t ws :=
  (h (fun s xs => TR G C ys s xs ∧ P s xs) ⟨TR.done, d⟩
    (fun s xs zs hp hx => ⟨TR.perm hp hx.1, p s xs zs hp hx.1 hx.2⟩)
    (fun s a b r k u hc hx => ⟨TR.step k u hc hx.1, st s a b r k u hc hx.1 hx.2⟩)).2

theorem TR.inv {t : ℕ} {ws : List α} (h : TR G C ys t ws) :
    (t = 0 → List.Perm ws ys) ∧
    (∀ s, t = s + 1 → ∃ (k : Fin 4) (u : ℕ) (a b : α) (r : List α), C k a b ∧
      List.Perm ws (a :: b :: r) ∧ TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) := by
  refine TR.ind (P := fun t ws => (t = 0 → List.Perm ws ys) ∧
    (∀ s, t = s + 1 → ∃ (k : Fin 4) (u : ℕ) (a b : α) (r : List α), C k a b ∧
      List.Perm ws (a :: b :: r) ∧ TR G C ys s (List.replicate (u + 1) (G k a b) ++ r))) h
    ⟨fun _ => List.Perm.refl _, fun s hs => by omega⟩ ?_ ?_
  · intro s xs zs hp _ ih
    refine ⟨fun h0 => hp.symm.trans (ih.1 h0), fun s' hs => ?_⟩
    obtain ⟨k, u, a, b, r, hc, hq, hr⟩ := ih.2 s' hs
    exact ⟨k, u, a, b, r, hc, hp.symm.trans hq, hr⟩
  · intro s a b r k u hc hr _
    refine ⟨fun h0 => by omega, fun s' hs => ?_⟩
    have : s = s' := by omega
    subst this
    exact ⟨k, u, a, b, r, hc, List.Perm.refl _, hr⟩

theorem TR.len {t : ℕ} {ws : List α} (h : TR G C ys t ws) : ws.length ≤ t + ys.length := by
  refine TR.ind (P := fun t ws => ws.length ≤ t + ys.length) h (by simp) ?_ ?_
  · intro s xs zs hp _ ih
    rw [← hp.length_eq]; exact ih
  · intro s a b r k u _ _ ih
    simp only [List.length_append, List.length_replicate, List.length_cons] at ih ⊢
    omega

theorem TR.monoC {C' : Fin 4 → α → α → Prop} (hC : ∀ k a b, C k a b → C' k a b) {t : ℕ}
    {ws : List α} (h : TR G C ys t ws) : TR G C' ys t ws :=
  TR.ind (P := fun t ws => TR G C' ys t ws) h TR.done (fun _ _ _ hp _ ih => TR.perm hp ih)
    (fun _ _ _ _ k u hc _ ih => TR.step k u (hC _ _ _ hc) ih)

end Run

def strictC (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop) (I : α → Prop) :
    Fin 4 → α → α → Prop :=
  fun k a b => A k ∧ I a ∧ I b ∧ a ≠ b ∧ G k a b ≠ a ∧ G k a b ≠ b ∧ G k a b ≠ z

theorem normalize [DecidableEq α] (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop)
    (I : α → Prop) (hI : ∀ k a b, I a → I b → I (G k a b))
    (hz1 : ∀ k b, G k z b = z ∨ G k z b = b) (hz2 : ∀ k a, G k a z = z ∨ G k a z = a)
    (hd : ∀ k a, G k a a = z ∨ G k a a = a) :
    ∀ (t : ℕ) (S : α → Prop) (f : α), (∀ w, S w → I w) → f ≠ z → UC G A t S f →
      ∃ t', t' ≤ t ∧ ∃ ws : List α, (∀ w ∈ ws, S w ∧ w ≠ z) ∧
        TR G (strictC G z A I) [f] t' ws
  | 0, S, f, _, hf, hu => ⟨0, le_rfl, [f], by simpa using ⟨hu, hf⟩, TR.done⟩
  | t + 1, S, f, hS, hf, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t S f hS hf hu
      exact ⟨t', by omega, ws, hws, hr⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t _ f (by
        rintro w (rfl | hw)
        · exact hI k a b (hS a ha) (hS b hb)
        · exact hS w hw) hf hu
      by_cases hg : S (G k a b)
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact hg
        · exact h
      by_cases hc : G k a b ∈ ws
      · have hgz : G k a b ≠ z := (hws _ hc).2
        have hga : G k a b ≠ a := fun h => hg (by rw [h]; exact ha)
        have hgb : G k a b ≠ b := fun h => hg (by rw [h]; exact hb)
        have hab : a ≠ b := by
          rintro rfl
          rcases hd k a with h | h
          · exact hgz h
          · exact hga h
        have haz : a ≠ z := by
          rintro rfl
          rcases hz1 k b with h | h
          · exact hgz h
          · exact hgb h
        have hbz : b ≠ z := by
          rintro rfl
          rcases hz2 k a with h | h
          · exact hgz h
          · exact hga h
        obtain ⟨u, hu1⟩ : ∃ u, List.count (G k a b) ws = u + 1 :=
          ⟨List.count (G k a b) ws - 1, by have := List.count_pos_iff.2 hc; omega⟩
        have hperm : ws.Perm (List.replicate (u + 1) (G k a b) ++ ws.filter (· ≠ G k a b)) := by
          rw [← hu1, ← List.filter_eq]
          have := List.filter_append_perm (fun x => decide (x = G k a b)) ws
          refine this.symm.trans ?_
          simp
        refine ⟨t' + 1, by omega, a :: b :: ws.filter (· ≠ G k a b), ?_,
          TR.step k u ⟨hk, hS a ha, hS b hb, hab, hga, hgb, hgz⟩ (TR.perm hperm hr)⟩
        intro w hw
        simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq] at hw
        rcases hw with rfl | rfl | ⟨hw, hne⟩
        · exact ⟨ha, haz⟩
        · exact ⟨hb, hbz⟩
        · rcases (hws w hw).1 with h | h
          · exact absurd h hne
          · exact ⟨h, (hws w hw).2⟩
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact absurd hw hc
        · exact h

theorem TR.map {G : Fin 4 → α → α → α} {G' : Fin 4 → β → β → β} {C : Fin 4 → α → α → Prop}
    {C' : Fin 4 → β → β → Prop} (e : α → β) (he : ∀ k a b, e (G k a b) = G' k (e a) (e b))
    (hC : ∀ k a b, C k a b → C' k (e a) (e b)) {ys : List α} {t : ℕ} {ws : List α}
    (h : TR G C ys t ws) : TR G' C' (ys.map e) t (ws.map e) := by
  refine TR.ind (P := fun t ws => TR G' C' (ys.map e) t (ws.map e)) h TR.done
    (fun _ _ _ hp _ ih => TR.perm (hp.map e) ih) ?_
  intro s a b r k u hc _ ih
  rw [List.map_append, List.map_replicate, he] at ih
  exact TR.step k u (hC _ _ _ hc) ih

theorem TR.rel {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} (R : α → α → Prop)
    (hR : ∀ k a a' b b', R a a' → R b b' → R (G k a b) (G k a' b')) {ys : List α} {t : ℕ}
    {ws : List α} (h : TR G (fun k _ _ => A k) ys t ws) :
    ∀ ws', List.Forall₂ R ws ws' →
      ∃ ys', List.Forall₂ R ys ys' ∧ TR G (fun k _ _ => A k) ys' t ws' := by
  refine TR.ind (P := fun t ws => ∀ ws', List.Forall₂ R ws ws' →
      ∃ ys', List.Forall₂ R ys ys' ∧ TR G (fun k _ _ => A k) ys' t ws') h
    (fun ws' hw => ⟨ws', hw, TR.done⟩) ?_ ?_
  · intro s xs zs hp _ ih zs' hz
    obtain ⟨xs', hx, hp'⟩ := List.perm_comp_forall₂ hp hz
    obtain ⟨ys', hy, hr⟩ := ih xs' hx
    exact ⟨ys', hy, TR.perm hp' hr⟩
  · intro s a b r k u hc _ ih ws' hw
    obtain ⟨a', t1, ha, ht1, rfl⟩ := List.forall₂_cons_left_iff.1 hw
    obtain ⟨b', r', hb, hr', rfl⟩ := List.forall₂_cons_left_iff.1 ht1
    have h1 : List.Forall₂ R (List.replicate (u + 1) (G k a b) ++ r)
        (List.replicate (u + 1) (G k a' b') ++ r') := by
      refine List.rel_append ?_ hr'
      generalize u + 1 = n
      induction n with
      | zero => exact List.Forall₂.nil
      | succ n ih => exact List.Forall₂.cons (hR k a a' b b' ha hb) ih
    obtain ⟨ys', hy, hrun⟩ := ih _ h1
    exact ⟨ys', hy, TR.step k u hc hrun⟩

end Generic

abbrev BF := (Fin 8 → Bool) → Bool

def gF (k : Fin 4) (a b : BF) : BF := fun x => zeroGate k (a x) (b x)

def var (i : Fin 8) : BF := fun x => x i

def gM (k a b : ℕ) : ℕ :=
  match k with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)

def gN (k : Fin 4) (a b : ℕ) : ℕ := gM k.val a b

theorem gN_testBit (k : Fin 4) (a b i : ℕ) :
    (gN k a b).testBit i = zeroGate k (a.testBit i) (b.testBit i) := by
  fin_cases k <;>
    simp [gN, gM, zeroGate, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit i <;> cases b.testBit i <;> rfl

theorem gN_zero_left (k : Fin 4) (b : ℕ) : gN k 0 b = 0 ∨ gN k 0 b = b := by
  fin_cases k <;> simp [gN, gM]

theorem gN_zero_right (k : Fin 4) (a : ℕ) : gN k a 0 = 0 ∨ gN k a 0 = a := by
  fin_cases k <;> simp [gN, gM]

theorem gN_self (k : Fin 4) (a : ℕ) : gN k a a = 0 ∨ gN k a a = a := by
  fin_cases k <;> simp [gN, gM]

theorem gN_lt (k : Fin 4) (a b : ℕ) (ha : a < 1024) (hb : b < 1024) : gN k a b < 1024 := by
  apply Nat.lt_pow_two_of_testBit (n := 10)
  intro i hi
  have hp : (1024 : ℕ) ≤ 2 ^ i :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (show 0 < 2 by norm_num) hi)
  rw [gN_testBit, Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hp),
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hp)]
  fin_cases k <;> rfl

def enc {ρ : Type} (w : ρ → Bool) : List ρ → ℕ
  | [] => 0
  | p :: t => Nat.bit (w p) (enc w t)

theorem enc_testBit {ρ : Type} (w : ρ → Bool) : ∀ (l : List ρ) (j : ℕ),
    (enc w l).testBit j = (l.map w).getD j false
  | [], j => by simp [enc]
  | p :: t, 0 => by simp [enc]
  | p :: t, j + 1 => by simp [enc, Nat.testBit_bit_succ, enc_testBit w t j]

theorem enc_gate {ρ : Type} (k : Fin 4) (a b : ρ → Bool) (l : List ρ) :
    enc (fun r => zeroGate k (a r) (b r)) l = gN k (enc a l) (enc b l) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [gN_testBit, enc_testBit, enc_testBit, enc_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    fin_cases k <;> rfl

theorem enc_gF (k : Fin 4) (a b : BF) (l : List (Fin 8 → Bool)) :
    enc (gF k a b) l = gN k (enc a l) (enc b l) := enc_gate k a b l

theorem enc_lt {ρ : Type} (w : ρ → Bool) (l : List ρ) : enc w l < 2 ^ l.length := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [enc_testBit, List.getD_eq_default _ _ (by simp; omega)]

def zF : BF := fun _ => false

def rst (p : Fin 8) (a : BF) : BF := fun x => a (Function.update x p false)

def ThrL (V : Fin 8 → Prop) (F : BF) : Prop :=
  (∀ i, V i → F (singleInput i) = false) ∧
    ∀ i j, V i → V j → i ≠ j → F (pairInput i j) = true

theorem gF_zero_left (k : Fin 4) (b : BF) : gF k zF b = zF ∨ gF k zF b = b := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_right (k : Fin 4) (a : BF) : gF k a zF = zF ∨ gF k a zF = a := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_self (k : Fin 4) (a : BF) : gF k a a = zF ∨ gF k a a = a := by
  fin_cases k
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_zero (k : Fin 4) : gF k zF zF = zF := by
  fin_cases k <;> exact funext fun x => by simp [gF, zF, zeroGate]

theorem upd_single {i p : Fin 8} (h : i ≠ p) :
    Function.update (singleInput i) p false = singleInput i := by
  funext m
  by_cases hm : m = p
  · subst hm; simp [singleInput, Ne.symm h]
  · simp [Function.update_of_ne hm]

theorem upd_pair {i j p : Fin 8} (hi : i ≠ p) (hj : j ≠ p) :
    Function.update (pairInput i j) p false = pairInput i j := by
  funext m
  by_cases hm : m = p
  · subst hm; simp [pairInput, Ne.symm hi, Ne.symm hj]
  · simp [Function.update_of_ne hm]

theorem rst_var_self (p : Fin 8) : rst p (var p) = zF :=
  funext fun x => by simp [rst, var, zF]

theorem rst_var_ne {i p : Fin 8} (h : i ≠ p) : rst p (var i) = var i :=
  funext fun x => by simp [rst, var, Function.update_of_ne h]

theorem var_inj {i j : Fin 8} (h : var i = var j) : i = j := by
  have := congrFun h (singleInput i)
  exact (by simpa [var, singleInput] using this : j = i).symm

theorem TRF_det {C : Fin 4 → BF → BF → Prop} {ys : List BF} {s : ℕ} {ws : List BF}
    (h : TR gF C ys s ws) (x x' : Fin 8 → Bool) :
    (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x' := by
  refine TR.ind (P := fun _ ws => (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x') h
    (fun h => h) ?_ ?_
  · intro s xs zs hp _ ih hz
    exact ih fun t ht => hz t (hp.mem_iff.1 ht)
  · intro s a b r k u _ _ ih hz
    apply ih
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · rw [List.eq_of_mem_replicate ht]
      show zeroGate k (a x) (b x) = zeroGate k (a x') (b x')
      rw [hz a (by simp), hz b (by simp)]
    · exact hz t (by simp [ht])

def dcount (p : Fin 8) (ws : List BF) : ℕ := ws.countP fun w => decide (rst p w = zF)

theorem dcount_cons (p : Fin 8) (a : BF) (l : List BF) :
    dcount p (a :: l) = dcount p l + if rst p a = zF then 1 else 0 := by
  simp [dcount, List.countP_cons]

theorem dcount_rep (p : Fin 8) (n : ℕ) (g : BF) (r : List BF) :
    dcount p (List.replicate n g ++ r) = (if rst p g = zF then n else 0) + dcount p r := by
  simp only [dcount, List.countP_append, List.countP_replicate]
  split_ifs <;> simp_all

theorem pot_dead {A : Fin 4 → Prop} (p : Fin 8) {F : BF} (hF : rst p F ≠ zF) {s : ℕ}
    {ws : List BF} (h : TR gF (fun k _ _ => A k) [F] s ws) :
    dcount p ws ≤ s ∧ ∀ S : BF → Prop, (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) →
      UC gF A (s - dcount p ws) S (rst p F) := by
  refine TR.ind (P := fun s ws => dcount p ws ≤ s ∧ ∀ S : BF → Prop,
    (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) → UC gF A (s - dcount p ws) S (rst p F)) h ?_ ?_ ?_
  · refine ⟨by simp [dcount, hF], fun S hS => ?_⟩
    have : dcount p [F] = 0 := by simp [dcount, hF]
    rw [this]
    exact hS F (by simp) hF
  · intro s xs zs hp _ ih
    have hc : dcount p zs = dcount p xs := (hp.countP_eq _).symm
    rw [hc]
    exact ⟨ih.1, fun S hS => ih.2 S fun w hw => hS w (hp.mem_iff.1 hw)⟩
  · intro s a b r k u hk _ ih
    obtain ⟨ih1, ih2⟩ := ih
    have hg : rst p (gF k a b) = gF k (rst p a) (rst p b) := rfl
    rw [dcount_rep] at ih1 ih2
    rw [dcount_cons, dcount_cons]
    have hmem : ∀ (S : BF → Prop), (∀ w ∈ a :: b :: r, rst p w ≠ zF → S (rst p w)) →
        ∀ w ∈ r, rst p w ≠ zF → S (rst p w) := fun S hS w hw => hS w (by simp [hw])
    by_cases ha : rst p a = zF <;> by_cases hb : rst p b = zF
    · have hgz : rst p (gF k a b) = zF := by rw [hg, ha, hb, gF_zero_zero]
      simp only [hgz, ha, hb, ite_true] at ih1 ih2 ⊢
      refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
      intro w hw hwz
      rcases List.mem_append.1 hw with hw | hw
      · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
      · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hgb : rst p (gF k a b) = rst p b := by
          rcases gF_zero_left k (rst p b) with h | h
          · exact absurd (by rw [hg, ha, h]) hgz
          · rw [hg, ha, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hgb]
          exact hS b (by simp) hb
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hga : rst p (gF k a b) = rst p a := by
          rcases gF_zero_right k (rst p a) with h | h
          · exact absurd (by rw [hg, hb, h]) hgz
          · rw [hg, hb, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hga]
          exact hS a (by simp) ha
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · simp only [hgz, ha, hb, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => ?_⟩
        have h1 := ih2 (fun w => w = gF k (rst p a) (rst p b) ∨ S w) (by
          intro w hw hwz
          rcases List.mem_append.1 hw with hw | hw
          · exact Or.inl (by rw [List.eq_of_mem_replicate hw, hg])
          · exact Or.inr (hmem S hS w hw hwz))
        have h2 := UC_gate k (rst p a) (rst p b) hk (hS a (by simp) ha) (hS b (by simp) hb) h1
        exact UC_le (by omega) h2

def MonoA : Fin 4 → Prop := fun k => k.val < 2

abbrev MR (ys : List BF) (s : ℕ) (ws : List BF) : Prop := TR gF (fun k _ _ => MonoA k) ys s ws

def outF (ys : List BF) : BF := fun x => ys.any fun y => y x

def otop (x : Fin 8) : BF := fun p => decide (∃ i, i ≠ x ∧ p i = true)

theorem mono_cases (k : Fin 4) (hk : MonoA k) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp_all [MonoA]

theorem gF_and (a b : BF) : gF 0 a b = fun p => a p && b p := rfl

theorem gF_or (a b : BF) : gF 1 a b = fun p => a p || b p := rfl

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gv (g : Gate) (W : List BF) : BF :=
  fun x => g.op.eval (g.inputs.map fun i => (W.getD i zF) x)

def wiresF : List Gate → List BF → List BF
  | [], W => W
  | g :: gs, W => wiresF gs (W ++ [gv g W])

theorem getD_map_x (W : List BF) (i : ℕ) (x : Fin 8 → Bool) :
    (W.map fun w => w x).getD i false = (W.getD i zF) x := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> rfl

theorem wires_eq (x : Fin 8 → Bool) : ∀ (gs : List Gate) (W : List BF),
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (W.map fun w => w x) = (wiresF gs W).map fun w => w x
  | [], W => rfl
  | g :: gs, W => by
    simp only [List.foldl_cons, wiresF]
    rw [← wires_eq x gs (W ++ [gv g W])]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_nil, gv, getD_map_x]

theorem getD_mem (W : List BF) (i : ℕ) : W.getD i zF ∈ W ∨ W.getD i zF = zF := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : W[i]? with _ | a
  · exact Or.inr rfl
  · exact Or.inl (List.mem_of_getElem? h)

theorem gate_form (g : Gate) (W : List BF)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) :
    gv g W = zF ∨ gv g W = (fun _ => true) ∨
    (∃ a, (a ∈ W ∨ a = zF) ∧ gv g W = a) ∨
    (∃ a, (a ∈ W ∨ a = zF) ∧ gv g W = fun x => !a x) ∨
    (∃ k a b, MonoA k ∧ (a ∈ W ∨ a = zF) ∧ (b ∈ W ∨ b = zF) ∧ gv g W = gF k a b) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨l, rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inl (funext fun x => by simp [gv, GateOp.eval]))
    · exact Or.inl (funext fun x => by simp [gv, GateOp.eval, zF])
    · exact Or.inr (Or.inl (funext fun x => by simp [gv, GateOp.eval]))
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩)))
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨0, W.getD i zF, W.getD j zF, by simp [MonoA],
        getD_mem W i, getD_mem W j, funext fun x => by simp [gv, GateOp.eval, gF_and]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨1, W.getD i zF, W.getD j zF, by simp [MonoA],
        getD_mem W i, getD_mem W j, funext fun x => by simp [gv, GateOp.eval, gF_or]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩)))
  · simp at hl

def ori (w : BF) : BF := fun x => xor (w x) (w fun _ => false)

theorem ori_zero : ori zF = zF := funext fun x => by simp [ori, zF]

theorem ori_true : ori (fun _ => true) = zF := funext fun x => by simp [ori, zF]

theorem ori_not (a : BF) : ori (fun x => !a x) = ori a :=
  funext fun x => by
    simp only [ori]
    cases a x <;> cases a (fun _ => false) <;> rfl

theorem ori_zp {w : BF} (h : w (fun _ => false) = false) : ori w = w :=
  funext fun x => by simp [ori, h]

theorem ori_gate (k : Fin 4) (hk : MonoA k) (a b : BF) :
    ∃ k', ori (gF k a b) = gF k' (ori a) (ori b) := by
  rcases mono_cases k hk with rfl | rfl
  · cases hu : a (fun _ => false) <;> cases hv : b (fun _ => false)
    · exact ⟨0, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨2, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨3, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨1, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
  · cases hu : a (fun _ => false) <;> cases hv : b (fun _ => false)
    · exact ⟨1, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨3, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨2, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨0, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩

abbrev GOK (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem ori_key (g : Gate) (W : List BF) (S : BF → Prop)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) (hW : ∀ w ∈ W, ori w = zF ∨ S (ori w)) :
    (ori (gv g W) = zF ∨ S (ori (gv g W))) ∨
      ∃ k a b, S a ∧ S b ∧ ori (gv g W) = gF k a b := by
  have hWz : ∀ a, (a ∈ W ∨ a = zF) → ori a = zF ∨ S (ori a) := by
    rintro a (h | rfl)
    · exact hW a h
    · exact Or.inl ori_zero
  rcases gate_form g W hop hl with h | h | ⟨a, ha, h⟩ | ⟨a, ha, h⟩ | ⟨k, a, b, hk, ha, hb, h⟩
  · rw [h]; exact Or.inl (Or.inl ori_zero)
  · rw [h]; exact Or.inl (Or.inl ori_true)
  · rw [h]; exact Or.inl (hWz a ha)
  · rw [h, ori_not]; exact Or.inl (hWz a ha)
  · obtain ⟨k', hk'⟩ := ori_gate k hk a b
    rw [h, hk']
    rcases hWz a ha with ha1 | ha1
    · rw [ha1]
      rcases gF_zero_left k' (ori b) with e | e
      · rw [e]; exact Or.inl (Or.inl rfl)
      · rw [e]; exact Or.inl (hWz b hb)
    rcases hWz b hb with hb1 | hb1
    · rw [hb1]
      rcases gF_zero_right k' (ori a) with e | e
      · rw [e]; exact Or.inl (Or.inl rfl)
      · rw [e]; exact Or.inl (Or.inr ha1)
    exact Or.inr ⟨k', ori a, ori b, ha1, hb1, rfl⟩

def graph (x : Fin 8 → Bool) : Bool := (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 5 && x 7) || (x 6 && x 7)
def assignment (a : ℕ) (i : Fin 8) : Bool := a.testBit i.val

def isNot : GateOp → Bool
  | .not => true
  | _ => false

theorem isNot_true (op : GateOp) : isNot op = true ↔ op = GateOp.not := by
  cases op <;> simp [isNot]

def countBinary : List Gate → ℕ
  | [] => 0
  | g :: gs => countBinary gs + if isNot g.op then 0 else 1

theorem countBinary_le (gs : List Gate) : countBinary gs ≤ gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [countBinary, List.length_cons]
    split <;> omega

theorem countBinary_lt (gs : List Gate) (h : ∃ g ∈ gs, g.op = GateOp.not) :
    countBinary gs < gs.length := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨a, ha, he⟩ := h
    rcases List.mem_cons.1 ha with rfl | ha
    · have hb := countBinary_le gs
      simp [countBinary, he, isNot, Nat.lt_succ_of_le hb]
    · have hb := ih ⟨a, ha, he⟩
      simp only [countBinary, List.length_cons]
      split <;> omega

theorem not_key (g : Gate) (W : List BF) (S : BF → Prop) (hop : g.op = GateOp.not)
    (hW : ∀ w ∈ W, ori w = zF ∨ S (ori w)) :
    ori (gv g W) = zF ∨ S (ori (gv g W)) := by
  obtain ⟨op, ins⟩ := g
  change op = GateOp.not at hop
  subst op
  cases ins with
  | nil => exact Or.inl ori_true
  | cons i rest =>
    have he : gv ⟨GateOp.not, i :: rest⟩ W = fun x => !(W.getD i zF) x := rfl
    rw [he, ori_not]
    rcases getD_mem W i with h | h
    · exact hW _ h
    · rw [h]; exact Or.inl ori_zero

theorem trans_binary : ∀ (gs : List Gate) (W : List BF) (S : BF → Prop), GOK gs →
    (∀ w ∈ W, ori w = zF ∨ S (ori w)) → ∀ o : ℕ,
    ori ((wiresF gs W).getD o zF) = zF ∨
      UC gF (fun _ => True) (countBinary gs) S (ori ((wiresF gs W).getD o zF))
  | [], W, S, _, hw, o => by
    rcases getD_mem W o with h | h
    · exact hw _ h
    · rw [wiresF, h]; exact Or.inl ori_zero
  | g :: gs, W, S, hg, hw, o => by
    have hg1 := hg g (by simp)
    have hg2 : GOK gs := fun g' h => hg g' (by simp [h])
    have free (h : ori (gv g W) = zF ∨ S (ori (gv g W))) :=
      trans_binary gs (W ++ [gv g W]) S hg2 (by
        intro w hm
        rcases List.mem_append.1 hm with hm | hm
        · exact hw w hm
        · rw [List.mem_singleton.1 hm]; exact h) o
    simp only [wiresF, countBinary]
    by_cases hn : g.op = GateOp.not
    · simpa [hn, isNot] using free (not_key g W S hn hw)
    · rw [if_neg (fun ht => hn ((isNot_true g.op).1 ht))]
      rcases ori_key g W S hg1.1 hg1.2 hw with h | ⟨k, a, b, ha, hb, h⟩
      · exact (free h).imp id (UC_le (Nat.le_succ _))
      · have next := trans_binary gs (W ++ [gv g W]) (fun w => w = gF k a b ∨ S w) hg2 (by
          intro w hm
          rcases List.mem_append.1 hm with hm | hm
          · exact (hw w hm).imp id Or.inr
          · rw [List.mem_singleton.1 hm]; exact Or.inr (Or.inl h)) o
        exact next.imp id (UC_gate k a b trivial ha hb)

def sourceVars (xs : Finset (Fin 8)) (f : BF) : Prop := ∃ i ∈ xs, f = var i

theorem remove_var (F : BF) (p : Fin 8) (xs : Finset (Fin 8)) (s : ℕ)
    (hd : ∃ x, rst p F x ≠ F x) (hn : rst p F ≠ zF)
    (h : UC gF (fun _ => True) s (sourceVars xs) F) :
    ∃ t, t + 1 ≤ s ∧ UC gF (fun _ => True) t (sourceVars (xs.erase p)) (rst p F) := by
  have hf : F ≠ zF := fun e => hn (by rw [e]; rfl)
  obtain ⟨k, hk, ws, hws, run⟩ := normalize gF zF (fun _ => True) (fun _ => True)
    (fun _ _ _ _ _ => trivial) gF_zero_left gF_zero_right gF_self
    s (sourceVars xs) F (fun _ _ => trivial) hf h
  have hp : var p ∈ ws := by
    by_contra hmiss
    obtain ⟨x, hx⟩ := hd
    apply hx
    exact TRF_det run (Function.update x p false) x (by
      intro w hw
      obtain ⟨i, _, rfl⟩ := (hws w hw).1
      have hi : i ≠ p := fun e => hmiss (e ▸ hw)
      exact Function.update_of_ne hi false x) F (by simp)
  have hc : 1 ≤ dcount p ws := by
    apply Nat.succ_le_of_lt
    unfold dcount
    exact List.countP_pos_iff.2 ⟨var p, hp, by simp [rst_var_self]⟩
  have dr := pot_dead p hn (TR.monoC (fun _ _ _ _ => trivial) run)
  refine ⟨k - dcount p ws, by omega, dr.2 (sourceVars (xs.erase p)) ?_⟩
  intro w hw hz
  obtain ⟨i, hi, rfl⟩ := (hws w hw).1
  have hne : i ≠ p := fun e => hz (e ▸ rst_var_self p)
  exact ⟨i, Finset.mem_erase.2 ⟨hne, hi⟩, rst_var_ne hne⟩

namespace CoreSigned

-- The signed live-wire search follows L-meta-8463 and L-meta-1449, Apache-2.0.

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

set_option maxRecDepth 100000 in
theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

set_option maxRecDepth 100000 in
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

set_option maxRecDepth 100000 in
theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

set_option maxRecDepth 100000 in
theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

def F (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 3) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 4)

end CoreSigned

namespace SignedProjection
variable {α β : Type} [DecidableEq α] [DecidableEq β] [Zero β]

def avail (pin : α → β) (S : Finset α) := (S.image pin).erase 0
def lost (pin : α → β) (S : Finset α) := (S.filter fun x => pin x = 0).card

theorem avail_mem (pin : α → β) {S : Finset α} {x : β} :
    x ∈ avail pin S ↔ x ≠ 0 ∧ ∃ a ∈ S, pin a = x := by simp [avail]

theorem avail_mono (pin : α → β) {S T : Finset α} (h : S ⊆ T) : avail pin S ⊆ avail pin T := by
  intro y hy
  obtain ⟨hn,x,hx,rfl⟩ := (avail_mem pin).mp hy
  exact (avail_mem pin).mpr ⟨hn,x,h hx,rfl⟩

theorem avail_cases (pin : α → β) {S : Finset α} {c : α} {x : β} (h : x ∈ avail pin (insert c S)) :
    x = pin c ∨ x ∈ avail pin S := by
  obtain ⟨hn,y,hy,rfl⟩ := (avail_mem pin).mp h
  rcases Finset.mem_insert.mp hy with rfl|hy
  · exact Or.inl rfl
  · exact Or.inr ((avail_mem pin).mpr ⟨hn,y,hy,rfl⟩)

theorem lost_insert (pin : α → β) (c : α) (S : Finset α) :
    lost pin (insert c S) = lost pin S + (if pin c = 0 ∧ c ∉ S then 1 else 0) := by
  by_cases mem : c ∈ S
  · rw [Finset.insert_eq_of_mem mem,ite_eq_right (fun q => q.2 mem),Nat.add_zero]
  · by_cases h : pin c = 0
    · rw [ite_eq_left ⟨h,mem⟩]
      unfold lost
      rw [Finset.filter_insert,ite_eq_left h,Finset.card_insert_of_notMem]
      exact fun q => mem (Finset.mem_filter.mp q).1
    · rw [ite_eq_right (fun q => h q.1),Nat.add_zero]
      unfold lost
      rw [Finset.filter_insert,ite_eq_right h]

theorem projected (pin : α → β) (ops : α → α → Finset α) (ops2 : β → β → Finset β) (goal : α)
    (hgoal : pin goal ≠ 0)
    (maps : ∀ {a b c}, c ∈ ops a b → pin c ∈ ops2 (pin a) (pin b))
    (idA : ∀ {a b c}, c ∈ ops2 a b → a = 0 → c = 0 ∨ c = b)
    (idB : ∀ {a b c}, c ∈ ops2 a b → b = 0 → c = 0 ∨ c = a)
    (idS : ∀ {a b c}, c ∈ ops2 a b → a = b → c = 0 ∨ c = b)
    {k : Nat} {S : Finset α} (h : CoreSigned.live ops goal k S) :
    ∃ j, j + lost pin S ≤ k ∧ ∃ T ⊆ avail pin S, CoreSigned.live ops2 (pin goal) j T := by
  induction k generalizing S with
  | zero =>
    change S = {goal} at h
    subst S
    exact ⟨0,by simp [lost,hgoal],{(pin goal)},by simp [avail,hgoal],rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a,_,b,_,ne,c,op,fresh,U,rfl,tail⟩
    · obtain ⟨j,hj,ws,sub,hws⟩ := ih skip
      exact ⟨j,by omega,ws,sub,hws⟩
    let prev := insert a (insert b U)
    have cnew : c ∉ U := fun h => fresh (by simp [h])
    have repr := maps op
    obtain ⟨j,limit,T,sub,path⟩ := ih tail
    have both (ha : pin a = 0) (hb : pin b = 0) : pin c = 0 := by
      exact (idA repr ha).elim id (fun e => e.trans hb)
    have skipcost : lost pin prev ≤ lost pin (insert c U) + 1 := by
      simp only [prev,lost_insert]
      split_ifs <;> grind
    have liftU : avail pin U ⊆ avail pin prev := avail_mono pin (by intro u hu; simp [prev,hu])
    by_cases useful : pin c ∈ T ∧ pin c ∉ avail pin prev
    · have nz := ((avail_mem pin).mp (sub useful.1)).1
      have df (v : α) (hv : v ∈ prev) : pin c ≠ pin v := by
        intro e
        exact useful.2 ((avail_mem pin).mpr ⟨nz,v,hv,e.symm⟩)
      have da := df a (by simp [prev])
      have db := df b (by simp [prev])
      have ha : pin a ≠ 0 := fun e => (idA repr e).elim nz db
      have hb : pin b ≠ 0 := fun e => (idB repr e).elim nz da
      have distinct : pin a ≠ pin b := fun e => (idS repr e).elim nz db
      have vcost : lost pin prev ≤ lost pin (insert c U) := by
        simp only [prev,lost_insert]
        split_ifs <;> grind
      let V := T.erase (pin c)
      have old (v : β) (hv : v ∈ V) : v ∈ avail pin U :=
        (avail_cases pin (sub (Finset.mem_erase.mp hv).2)).resolve_left (Finset.mem_erase.mp hv).1
      let B := insert (pin a) (insert (pin b) V)
      refine ⟨j+1,by change j+1+lost pin prev ≤ k+1; omega,B,?_,Or.inr ?_⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl|hv
        · exact (avail_mem pin).mpr ⟨ha,a,by simp,rfl⟩
        rcases Finset.mem_insert.mp hv with rfl|hv
        · exact (avail_mem pin).mpr ⟨hb,b,by simp,rfl⟩
        exact liftU (old _ hv)
      · refine ⟨pin a,by simp [B],pin b,by simp [B],distinct,pin c,?_,?_,V,rfl,?_⟩
        · exact repr
        · simp [B,V,da,db]
        · rwa [show insert (pin c) V = T from Finset.insert_erase useful.1]
    · refine ⟨j,by change j+lost pin prev ≤ k+1; omega,T,?_,path⟩
      intro v hv
      rcases avail_cases pin (sub hv) with rfl|old
      · by_contra miss
        exact useful ⟨hv,miss⟩
      · exact liftU old


end SignedProjection

namespace SignedProjection
variable {n : Nat}

def signedOps (a b : BitVec n) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a].toFinset

theorem zero_left {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : a = 0) : c = 0 ∨ c = b := by
  subst a
  simpa [signedOps,or_comm] using h

theorem zero_right {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : b = 0) : c = 0 ∨ c = a := by
  subst b
  simpa [signedOps,or_comm] using h

theorem equal_inputs {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : a = b) : c = 0 ∨ c = b := by
  subst a
  simpa [signedOps,or_comm] using h

def signedPin (mask : BitVec n) (base : Fin n) (x : BitVec n) : BitVec n :=
  (if x[base.val] then ~~~x else x) &&& mask

theorem masked_ops (m : BitVec n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    c &&& m ∈ signedOps (a &&& m) (b &&& m) := by
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at *
  rcases h with rfl|rfl|rfl|rfl
  · left; ext i h; simp [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  · right;left; ext i h; simp only [BitVec.getElem_or,BitVec.getElem_and]; cases a[i] <;> cases b[i] <;> simp
  · right;right;left; ext i h
    simp only [BitVec.getElem_and,BitVec.getElem_not]
    cases a[i] <;> cases b[i] <;> cases m[i] <;> decide
  · right;right;right; ext i h
    simp only [BitVec.getElem_and,BitVec.getElem_not]
    cases a[i] <;> cases b[i] <;> cases m[i] <;> decide

def polarity (b : Bool) (x : BitVec n) := if b then ~~~x else x

theorem polarity_ops (i : Fin n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    polarity (c[i.val]) c ∈ signedOps (polarity (a[i.val]) a) (polarity (b[i.val]) b) := by
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at *
  rcases h with rfl|rfl|rfl|rfl <;>
    simp only [BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not] <;>
    cases a[i.val] <;> cases b[i.val] <;>
    simp [polarity,BitVec.not_and,BitVec.not_or,BitVec.and_comm,BitVec.or_comm]

theorem signedPin_ops (m : BitVec n) (i : Fin n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    signedPin m i c ∈ signedOps (signedPin m i a) (signedPin m i b) :=
  masked_ops m (polarity_ops i h)

theorem live_build {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}
    {k : Nat} {S V : Finset α} (h : CoreSigned.live ops goal k S) (sub : S ⊆ V) :
    CoreSigned.build ops goal k V := by
  induction k generalizing S V with
  | zero => change S = {goal} at h; subst S; exact sub (Finset.mem_singleton_self _)
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,ne,c,opc,_,rest,eq,tail⟩
    · exact Or.inl (ih skip sub)
    · refine Or.inr ⟨a,sub ha,b,sub hb,ne,c,opc,ih tail ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl|hr
      · simp
      · exact Finset.mem_insert_of_mem (sub (eq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr)))

end SignedProjection

namespace SignedProjection
variable {α : Type} [DecidableEq α]

def generated (ops : α → α → Finset α) (stock : Finset α) : List (α × α × α) → Finset α → Prop
  | [], result => stock = result
  | (a,b,w) :: rest, result =>
    a ∈ stock ∧ b ∈ stock ∧ a ≠ b ∧ w ∈ ops a b ∧ generated ops (insert w stock) rest result

theorem extend_generated {ops : α → α → Finset α} {goal : α} {stock result : Finset α}
    {recipe : List (α × α × α)} {k : ℕ}
    (h : generated ops stock recipe result) (tail : CoreSigned.build ops goal k result) :
    CoreSigned.build ops goal (k + recipe.length) stock := by
  induction recipe generalizing stock with
  | nil => change stock = result at h; simpa [h] using tail
  | cons step rest ih =>
    obtain ⟨a,b,w⟩ := step
    rcases h with ⟨ha,hb,hn,ho,hrest⟩
    change CoreSigned.build ops goal (k+rest.length+1) stock
    exact Or.inr ⟨a,ha,b,hb,hn,w,ho,ih hrest⟩

theorem pad_build {ops : α → α → Finset α} {goal : α} {S : Finset α} {a b : Nat}
    (le : a ≤ b) (ha : CoreSigned.build ops goal a S) : CoreSigned.build ops goal b S := by
  induction le with
  | refl => exact ha
  | step _ ih => exact Or.inl ih

end SignedProjection

namespace SignedProjection
variable {n : Nat}

theorem exclude_cut (m : BitVec n) (i : Fin n) (goal : BitVec n) (k cap : ℕ)
    (S A U : Finset (BitVec n)) (recipes : List (BitVec n × BitVec n × BitVec n))
    (nonzero : signedPin m i goal ≠ 0)
    (bound : ¬ CoreSigned.build signedOps (signedPin m i goal) cap A)
    (regen : generated signedOps A recipes U) (sub : avail (signedPin m i) S ⊆ U)
    (budget : recipes.length + k ≤ cap + lost (signedPin m i) S) :
    ¬ CoreSigned.live signedOps goal k S := by
  intro h
  obtain ⟨j, hj, T, ht, path⟩ := projected (signedPin m i) signedOps signedOps goal nonzero
    (signedPin_ops m i) zero_left zero_right equal_inputs h
  have localRun := live_build path (ht.trans sub)
  exact bound (pad_build (by omega) (extend_generated regen localRun))

end SignedProjection

namespace SignedProjection
open CoreSigned (live build first_live live_card pairs pick_two live_separates)

abbrev Word := BitVec 64
def signedList (a b : Word) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]
theorem ops_swap (a b : Word) : signedOps a b = signedOps b a := by
  ext z
  simp only [signedOps, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto
def keepChoices (a b : Word) (r : List Word) : List (List Word) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List Word} {a b : Word} {needed : Finset Word}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : Word} {ws : List Word} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (v : Word) : List Word → List Word
  | [] => [v]
  | x :: xs => if v ≤ x then v :: x :: xs else x :: insertW v xs

def ordered (ws : List Word) := ws.foldr insertW []

theorem insertW_perm (v : Word) (ws : List Word) : (insertW v ws).Perm (v :: ws) := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insertW]
    split
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

theorem ordered_perm (ws : List Word) : (ordered ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih => exact (insertW_perm x (ordered xs)).trans (ih.cons x)

theorem perm_set {u v : List Word} (p : u.Perm v) : u.toFinset = v.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (p.mem_iff : a ∈ u ↔ a ∈ v)


def children (k : Nat) (ws : List Word) : List (List Word) :=
  (pairs ws).flatMap fun (a,b,r) => (signedList a b).flatMap fun z =>
    if z ∈ ws then [] else
      (keepChoices a b r).filterMap fun kept =>
        if kept.length ≤ k then some (ordered (z :: kept)) else none

theorem zero_prune {goal : Word} (nz : goal ≠ 0) {k : Nat} {S : Finset Word}
    (h : live signedOps goal k S) : ∃ j ≤ k, ∃ T ⊆ S.erase 0, live signedOps goal j T := by
  obtain ⟨j,le,T,sub,path⟩ := projected id signedOps signedOps goal nz (fun q => q)
    zero_left zero_right equal_inputs h
  refine ⟨j,by omega,T,?_,path⟩
  simpa [avail] using sub

theorem step_no (goal : Word) (n : Nat) (ws : List Word) (hn : ws.Nodup)
    (done_ : ws ≠ [goal])
    (children_ : ∀ qs ∈ children n ws, ¬ live signedOps goal n qs.toFinset)
    : ¬ live signedOps goal (n+1) ws.toFinset := by
  intro h
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · exact done_ (singleton_list hn done)
  obtain ⟨r,hm,hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
  have go {a b : Word} (hp : ws.Perm (a :: b :: r)) (hmem : (a,b,r) ∈ pairs ws)
      (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ signedOps a b) : False := by
    obtain ⟨kept,hkeep,hnk,hfin⟩ := recover_kept hp hn hset
    have hznew : z ∉ kept := by
      intro hu
      apply hout
      rw [hset]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))
    have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
    have hraw : live signedOps goal n (z :: kept).toFinset := by simpa [hfin] using tail
    have hc := live_card hraw
    rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
    have hzws : z ∉ ws := by simpa using hout
    have hp' := ordered_perm (z :: kept)
    have mem : ordered (z :: kept) ∈ children n ws := by
      apply List.mem_flatMap.mpr
      refine ⟨(a,b,r),hmem,List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩⟩
      simpa only [hzws,ite_false] using
        (List.mem_filterMap.mpr ⟨kept,hkeep,by simp [show kept.length ≤ n by omega]⟩ :
          ordered (z::kept) ∈ ((keepChoices a b r).filterMap fun kept =>
            if kept.length ≤ n then some (ordered (z :: kept)) else none))
    exact children_ _ mem ((perm_set hp').symm ▸ hraw)
  rcases hm with direct|swap
  · exact go hp direct hs hz
  · exact go (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)
end SignedProjection

namespace SignedProjection
abbrev V64 := BitVec 64

def bitAt (w : V64) (n : Nat) := w.getLsbD n
def mismatch (g : V64) (ws : List V64) (p q : Nat) :=
  (bitAt g p != bitAt g q) && ws.all (fun w => bitAt w p == bitAt w q)

theorem mismatch_sound {g : V64} {ws : List V64} {p q : Nat} (pp : p < 64) (qq : q < 64)
    (cert : mismatch g ws p q = true) (k : ℕ) : ¬ CoreSigned.live signedOps g k ws.toFinset := by
  intro h
  have parts := Bool.and_eq_true_iff.mp cert
  let D : V64 → Prop := fun w => bitAt w p ≠ bitAt w q
  have dg : D g := by simpa [D] using parts.1
  have hop (a b : V64) (z : V64) (hz : z ∈ signedOps a b) (dz : D z) : D a ∨ D b := by
    by_contra! fail
    apply dz
    obtain ⟨ea,eb⟩ := fail
    simp only [D, not_not] at ea eb
    change bitAt a p = bitAt a q at ea
    change bitAt b p = bitAt b q at eb
    simp only [signedOps, List.mem_toFinset,List.mem_cons, List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl <;>
      simpa only [bitAt, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
        pp,qq,decide_true, Bool.true_and, show a.getLsbD p = a.getLsbD q from ea,
        show b.getLsbD p = b.getLsbD q from eb]
  obtain ⟨x,hx,dx⟩ := CoreSigned.live_separates D dg hop h
  exact dx (beq_iff_eq.mp (List.all_eq_true.mp parts.2 x (List.mem_toFinset.mp hx)))

end SignedProjection

namespace SignedProjection
abbrev View := Word × Fin 64 × Word × List Word × Nat × (Nat → Nat)
abbrev Node := Nat × Nat × List Word × (Nat → Nat)
def vm (v : View) := v.1
def va (v : View) := v.2.1
def vg (v : View) := v.2.2.1
def vs (v : View) := v.2.2.2.1
def vk (v : View) := v.2.2.2.2.1
def vh (v : View) := v.2.2.2.2.2
def nv (a : Node) := a.1
def nk (a : Node) := a.2.1
def ns (a : Node) := a.2.2.1
def nh (a : Node) := a.2.2.2

def recipeRun : Nat → Nat → List Word → Option (List (Word × Word × Word) × List Word)
  | 0, code, ws => if code = 1 then some ([],ws) else none
  | fuel+1, code, ws => if code = 1 then some ([],ws) else
    let i := code % 16
    let j := (code / 16) % 16
    let o := (code / 256) % 4
    match ws[i]?, ws[j]? with
    | some a, some b => if a = b then none else
      let w := (signedList a b).getD o 0
      match recipeRun fuel (code / 1024) (ws++[w]) with
      | some (rs,ws') => some ((a,b,w)::rs,ws')
      | none => none
    | _,_ => none

theorem recipeRun_sound (fuel code : Nat) (ws : List Word) {rs out}
    (h : recipeRun fuel code ws = some (rs,out)) :
    generated signedOps ws.toFinset rs out.toFinset := by
  induction fuel generalizing code ws rs out with
  | zero =>
    simp only [recipeRun] at h
    split at h
    · cases h; rfl
    · contradiction
  | succ k ih =>
    simp only [recipeRun] at h
    split at h
    · cases h; rfl
    split at h <;> try contradiction
    rename_i a b ha hb
    split at h <;> try contradiction
    rename_i ne
    split at h <;> try contradiction
    rename_i tail end_ ht
    cases h
    set r := (code / 256) % 4
    let w := (signedList a b).getD r 0
    change a ∈ ws.toFinset ∧ b ∈ ws.toFinset ∧ a ≠ b ∧ w ∈ signedOps a b ∧ _
    refine ⟨List.mem_toFinset.mpr (List.mem_of_getElem? ha),
      List.mem_toFinset.mpr (List.mem_of_getElem? hb),ne,?_,?_⟩
    · have hr : r < 4 := Nat.mod_lt _ (by decide)
      change w ∈ (signedList a b).toFinset
      simp only [List.mem_toFinset]
      have hr' : r < (signedList a b).length := by simpa [signedList] using hr
      simpa [w, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr'] using
        (List.getElem_mem (l := signedList a b) (i := r) hr')
    · have eq : (ws++[w]).toFinset = insert w ws.toFinset := by
        ext x
        simp [or_comm]
      rw [← eq]
      exact ih _ _ ht

def ViewOK (v : View) := ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset

def cutOK (v : View) (g : Word) (k : Nat) (ws : List Word) (recipe : Nat) : Bool :=
  let p := signedPin (vm v) (va v)
  if p g != vg v || p g == 0 then false else
    match recipeRun 12 recipe (vs v) with
    | none => false
    | some (rs,out) =>
      decide (avail p ws.toFinset ⊆ out.toFinset) &&
      decide (rs.length+k ≤ vk v + lost p ws.toFinset)

theorem cutOK_sound {v : View} {g : Word} {k : Nat} {ws : List Word} {recipe : Nat}
    (hv : ViewOK v) (hc : cutOK v g k ws recipe = true) :
    ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [cutOK] at hc
  split at hc <;> try contradiction
  rename_i ok
  split at hc <;> try contradiction
  rename_i rs out hr
  have parts := Bool.and_eq_true_iff.mp hc
  have good : signedPin (vm v) (va v) g = vg v ∧ signedPin (vm v) (va v) g ≠ 0 := by
    simpa using ok
  apply exclude_cut (vm v) (va v) g k (vk v) ws.toFinset (vs v).toFinset out.toFinset rs good.2
    (good.1 ▸ hv) (recipeRun_sound _ _ _ hr) (of_decide_eq_true parts.1)
    (of_decide_eq_true parts.2)

end SignedProjection
namespace SignedProjection.Fast
abbrev Table (α : Type) := Nat × (Nat → Option α)
def get {α : Type} (t : Table α) (i : Nat) : Option α := if i < t.1 then t.2 i else none

def checkHint (views : Table View) (nodes : Table Node) (vID : Nat) (g : Word)
    (k : Nat) (ws : List Word) (hint : Nat) : Bool :=
  let val := hint/4
  match hint % 4 with
  | 0 => mismatch g ws (val % 64) ((val/64)%64)
  | 1 => match (get nodes val) with
    | some a => (nv a == vID) && (nk a == k) && (ns a == ws)
    | none => false
  | 2 =>
    let j := val % 1024
    if j < vID then
      match (get views j) with
      | some v => cutOK v g k ws (val/1024)
      | none => false
    else false
  | _ => (k == 0 && ws.toFinset != {g}) || decide (k+1 < ws.toFinset.card)

theorem checkHint_sound {views : Table View} {nodes : Table Node} {vID : Nat} {g : Word}
    {k : Nat} {ws : List Word} {h : Nat}
    (known : ∀ i < vID, ∀ v, (get views i) = some v → ViewOK v)
    (closed : ∀ (i : Nat) (a : Node), (get nodes i) = some a → nv a = vID → nk a = k →
      ¬ CoreSigned.live signedOps g k (ns a).toFinset)
    (ok : checkHint views nodes vID g k ws h = true) : ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [checkHint] at ok
  split at ok
  · exact mismatch_sound (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) ok k
  · split at ok <;> try contradiction
    rename_i a ha
    simp only [Bool.and_eq_true,beq_iff_eq] at ok
    exact ok.2 ▸ closed _ a ha ok.1.1 ok.1.2
  · split at ok <;> try contradiction
    rename_i lt
    split at ok <;> try contradiction
    rename_i v hv
    exact cutOK_sound (known _ lt _ hv) ok
  · simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,bne_iff_ne,decide_eq_true_eq] at ok
    intro h
    rcases ok with ⟨rfl,ne⟩|wide
    · exact ne h
    · exact (Nat.not_lt_of_ge (CoreSigned.live_card h)) wide

def scanFrom {α : Type} (f : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | i, x::xs => f i x && scanFrom f (i+1) xs

theorem scanFrom_sound {α : Type} (f : Nat → α → Bool) {i : Nat} {xs : List α}
    (ok : scanFrom f i xs = true) {x : α} (hx : x ∈ xs) : ∃ j, f j x = true := by
  induction xs generalizing i with
  | nil => simp at hx
  | cons a xs ih =>
    have parts := Bool.and_eq_true_iff.mp ok
    rcases List.mem_cons.mp hx with rfl|hm
    · exact ⟨_,parts.1⟩
    · exact ih parts.2 hm

def evalNode (views : Table View) (nodes : Table Node) (a : Node) : Bool :=
  match (get views (nv a)) with
  | none => false
  | some v => decide (ns a).Nodup && (ns a != [vg v]) &&
    match nk a with
    | 0 => true
    | k+1 => scanFrom (fun i ws => checkHint views nodes (nv a) (vg v) k ws (nh a i)) 0
               (children k (ns a))

def evalRoot (views : Table View) (nodes : Table Node) (i : Nat) (v : View) : Bool :=
  scanFrom (fun q ws => checkHint views nodes i (vg v) (vk v) ws (vh v q)) 0 (vs v).sublists

theorem view_from_earlier (views : Table View) (nodes : Table Node) (vID : Nat) (v : View)
    (hv : (get views vID) = some v)
    (earlier : ∀ i < vID, ∀ w, (get views i) = some w → ViewOK w)
    (hroots : evalRoot views nodes vID v = true)
    (hnodes : ∀ (i : Nat) (a : Node), (get nodes i) = some a → evalNode views nodes a = true) :
    ViewOK v := by
  have closed (k : Nat) : ∀ (i : Nat) (a : Node), (get nodes i) = some a → nv a = vID → nk a = k →
      ¬ CoreSigned.live signedOps (vg v) k (ns a).toFinset := by
    induction k with
    | zero =>
      intro i a found owner fuel h
      have ok := hnodes i a found
      simp only [evalNode,owner,hv,fuel,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
      exact ok.2 (singleton_list ok.1 h)
    | succ k ih =>
      intro i a found owner fuel
      have ok := hnodes i a found
      simp only [evalNode,owner,hv,fuel,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
      apply step_no _ _ _ ok.1.1 ok.1.2
      intro ws hm
      obtain ⟨j,good⟩ := scanFrom_sound _ ok.2 hm
      exact checkHint_sound earlier ih good
  intro build_
  classical
  obtain ⟨S, sub, path⟩ := CoreSigned.compress build_
  let ws := (vs v).filter (· ∈ S)
  have eq : ws.toFinset = S := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (sub hw)
  obtain ⟨q,hq⟩ := scanFrom_sound _ hroots (show ws ∈ (vs v).sublists from
    List.mem_sublists.mpr (List.filter_sublist ..))
  exact checkHint_sound earlier (closed _) hq (eq.symm ▸ path)

theorem whole_sound (views : Table View) (nodes : Table Node)
    (allRoots : ∀ (i : Nat) (v : View), (get views i) = some v → evalRoot views nodes i v = true)
    (allNodes : ∀ (i : Nat) (a : Node), (get nodes i) = some a → evalNode views nodes a = true)
    (i : Nat) (v : View) (hv : (get views i) = some v) : ViewOK v := by
  induction i using Nat.strong_induction_on generalizing v with
  | ind i ih => exact view_from_earlier views nodes i v hv ih (allRoots i v hv) allNodes

def checkRootAt (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match (get views i) with
  | some v => evalRoot views nodes i v
  | none => true

def checkNodeAt (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match (get nodes i) with
  | some a => evalNode views nodes a
  | none => true

def passBlock (check : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => passBlock check start n && check (start+n)

theorem block_at (check : Nat → Bool) {s n i} (ok : passBlock check s n = true)
    (lo : s ≤ i) (hi : i < s+n) : check i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have parts := Bool.and_eq_true_iff.mp ok
    by_cases lt : i < s+n
    · exact ih parts.1 lt
    · have eq : i = s+n := by omega
      exact eq ▸ parts.2

theorem merge_blocks {c : Nat → Bool} {s a b : Nat} (x : passBlock c s a = true)
    (y : passBlock c (s+a) b = true) : passBlock c s (a+b) = true := by
  induction b with
  | zero => simpa using x
  | succ b ih =>
    have parts := Bool.and_eq_true_iff.mp y
    change passBlock c s (a+b) && c (s+(a+b)) = true
    exact Bool.and_eq_true_iff.mpr ⟨ih parts.1,by simpa [Nat.add_assoc] using parts.2⟩

theorem certified_view (views : Table View) (nodes : Table Node)
    (roots : passBlock (checkRootAt views nodes) 0 views.1 = true)
    (states : passBlock (checkNodeAt views nodes) 0 nodes.1 = true)
    {i : Nat} {v : View} (hv : (get views i) = some v) : ViewOK v := by
  apply whole_sound views nodes _ _ i v hv
  · intro j w hw
    have hj : j < views.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at hw
    have ok := block_at _ roots (i := j) (Nat.zero_le _) (by omega)
    simpa [checkRootAt,hw] using ok
  · intro j a ha
    have hj : j < nodes.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at ha
    have ok := block_at _ states (i := j) (Nat.zero_le _) (by omega)
    simpa [checkNodeAt,ha] using ok

end SignedProjection.Fast
namespace SignedProjection

def wordsBlock0 : Array Word := #[
  0xaa,
  0xa0a,
  0xc0c,
  0xe0e,
  0xf00,
  0xf0a,
  0xf0c,
  0xf0e,
  0x2222,
  0x3030,
  0x3232,
  0x3300,
  0x3322,
  0x3330,
  0x3332,
  0xaaaa
]

def wordsBlock1 : Array Word := #[
  0xcccc,
  0xeeee,
  0xf0f0,
  0xfafa,
  0xff00,
  0xa000a,
  0x220022,
  0x300030,
  0x330000,
  0x440044,
  0x600060,
  0x660000,
  0x880022,
  0xaa00aa,
  0xc00030,
  0xc80032
]

def wordsBlock2 : Array Word := #[
  0xcc0000,
  0xcc0022,
  0xcc0030,
  0xcc0032,
  0xcc00cc,
  0xcc00ee,
  0xce00ce,
  0xee00ee,
  0xf000f0,
  0xfa00fa,
  0xfc00fc,
  0xff0000,
  0xff00aa,
  0xff00cc,
  0xff00f0,
  0x4040808
]

def wordsBlock3 : Array Word := #[
  0x5000a00,
  0x5050000,
  0x8080202,
  0xa0a0a0a,
  0xc000300,
  0xc080302,
  0xc0c0000,
  0xc0c0202,
  0xc0c0300,
  0xc0c0302,
  0xc0c0c0c,
  0xe0e0e0e,
  0xf000f00,
  0xf0f0000,
  0x22222222,
  0x30303030
]

def wordsBlock4 : Array Word := #[
  0x33003300,
  0x33330000,
  0x40401010,
  0x44001100,
  0x44401110,
  0x44440000,
  0x44441010,
  0x44441100,
  0x44441110,
  0x44444444,
  0x44448888,
  0x4e4e4e4e,
  0x5050a0a0,
  0x5500aa00,
  0x55550000,
  0x60606060
]

def wordsBlock5 : Array Word := #[
  0x66006600,
  0x66660000,
  0x88882222,
  0xa0a00a0a,
  0xaaaaaaaa,
  0xc0c00c0c,
  0xc0c03030,
  0xc8c83232,
  0xcc003300,
  0xcc883322,
  0xccc03330,
  0xccc83332,
  0xcccc0000,
  0xcccc2222,
  0xcccc3030,
  0xcccc3232
]

def wordsBlock6 : Array Word := #[
  0xcccc3300,
  0xcccc3322,
  0xcccc3330,
  0xcccccccc,
  0xcccccece,
  0xcccceeee,
  0xcececece,
  0xeeeecece,
  0xeeeeeeee,
  0xf0000f00,
  0xf0f00000,
  0xfafafafa,
  0xfcfcfcfc,
  0xfefefefe,
  0xffff2222,
  0xffffaaaa
]

def wordsBlock7 : Array Word := #[
  0xffffeeee,
  0xa0000000a,
  0xc0000000c,
  0xf00000000,
  0x1000100000,
  0x1400000000,
  0x2200000022,
  0x4400440000,
  0x4800000048,
  0x5000000050,
  0x5000500000,
  0x5500000000,
  0x5a00000000,
  0xa00000000a,
  0xaa000000aa,
  0xc00000000c
]

def wordsBlock8 : Array Word := #[
  0xcc000000cc,
  0xe00000000e,
  0xee000000ee,
  0xf000000000,
  0xf00000000a,
  0xf00000000c,
  0xf00000000e,
  0xf0000000f0,
  0xf0000000fa,
  0xf2000000f2,
  0xfa000000fa,
  0xfc000000fc,
  0xff00000000,
  0xff000000aa,
  0xff000000cc,
  0xff000000f0
]

def wordsBlock9 : Array Word := #[
  0xa0a00000a0a,
  0xc0c00000c0c,
  0xf0000000f00,
  0xf0f00000000,
  0x101000002020,
  0x110000002200,
  0x111100000000,
  0x202000000202,
  0x222200002222,
  0x300000000300,
  0x302000000302,
  0x303000000000,
  0x303000000202,
  0x303000000300,
  0x303000000302,
  0x303000003030
]

def wordsBlock10 : Array Word := #[
  0x323200003232,
  0x330000003300,
  0x333300000000,
  0x404000000404,
  0x444400008888,
  0x444444440000,
  0x484800004848,
  0x500000000500,
  0x504000000504,
  0x505000000000,
  0x505000000404,
  0x505000000500,
  0x505000000504,
  0x505000005050,
  0x50500000a0a0,
  0x505050500000
]

def wordsBlock11 : Array Word := #[
  0x55000000aa00,
  0x550055000000,
  0x555500000000,
  0x5a0000005a00,
  0x5a5a00000000,
  0x727200007272,
  0xa0a000000a0a,
  0xaaaa0000aaaa,
  0xaaaaaaaa0000,
  0xc0c000000c0c,
  0xcccccccc0000,
  0xe0e000000e0e,
  0xeeee0000eeee,
  0xf00000000f00,
  0xf0a000000f0a,
  0xf0c000000f0c
]

def wordsBlock12 : Array Word := #[
  0xf0e000000f0e,
  0xf0f000000000,
  0xf0f000000a0a,
  0xf0f000000c0c,
  0xf0f000000e0e,
  0xf0f000000f00,
  0xf0f000000f0a,
  0xf0f000000f0c,
  0xf0f00000f0f0,
  0xf0f00000f2f2,
  0xf0f00000fafa,
  0xf0f0f0f00000,
  0xf2f20000f2f2,
  0xfafa0000f2f2,
  0xfafa0000fafa,
  0xfcfc0000fcfc
]

def wordsBlock13 : Array Word := #[
  0xfefe0000fefe,
  0xff00ff000000,
  0xffff00000000,
  0xffff00000a0a,
  0xffff0000aaaa,
  0xffff0000fafa,
  0x2000200020002,
  0x4000800040008,
  0x5000000050000,
  0x5000a00000000,
  0x500ff00000000,
  0xa000a000a000a,
  0xc000c000c000c,
  0xe000e000e000e,
  0xf0000000f0000,
  0xf0000000f000a
]

def wordsBlock14 : Array Word := #[
  0xf0002000f0002,
  0xf000a000f000a,
  0xf000c000f000c,
  0xf000f00000000,
  0xf000f000a000a,
  0xf000f000c000c,
  0xf000f000f0000,
  0x10001000200020,
  0x11000000220000,
  0x11000000ff0000,
  0x11001100000000,
  0x22002200220022,
  0x30003000300030,
  0x32003200320032,
  0x33000000330000,
  0x33002200330022
]

def wordsBlock15 : Array Word := #[
  0x33003000330030,
  0x33003300000000,
  0x33003300000022,
  0x33003300020002,
  0x33003300220022,
  0x33003300300030,
  0x33003300330000,
  0x44004400440044,
  0x44004400880088,
  0x44008800440088,
  0x48004800480048,
  0x50005000500050,
  0x50005000a000a0,
  0x5000a0005000a0,
  0x54005400540054,
  0x55000000550000
]

def wordsBlock16 : Array Word := #[
  0x55000000aa0000,
  0x55004400550044,
  0x55005000550050,
  0x55005500000000,
  0x55005500440044,
  0x55005500500050,
  0x55005500550000,
  0x5500aa00000000,
  0x57000000570000,
  0x57005700000000,
  0x5a0000005a0000,
  0x5a005a00000000,
  0x60006000600060,
  0x66000000660000,
  0x66006600000000,
  0x80002000080002
]

def wordsBlock17 : Array Word := #[
  0xa800a800a800a8,
  0xaa008800aa0088,
  0xaa00a000aa00a0,
  0xaa00aa00880088,
  0xaa00aa00a000a0,
  0xaa00aa00aa0000,
  0xaa00aa00aa00aa,
  0xc00000000c0000,
  0xc00020000c0002,
  0xc0003000000000,
  0xc0003000080002,
  0xc00030000c0000,
  0xc00030000c0002,
  0xcc00cc00cc00cc,
  0xcc00cc00ee00ee,
  0xcc00cc00ff00fc
]

def wordsBlock18 : Array Word := #[
  0xcc00ee00cc00ee,
  0xce00ce00ce00ce,
  0xee00ec00ee00ec,
  0xee00ee00ec00ec,
  0xee00ee00ee00cc,
  0xee00ee00ee00ee,
  0xf000f000f000f0,
  0xf000f000fa00fa,
  0xf000fa00f000fa,
  0xf000ff00f000fc,
  0xf200f200f200f2,
  0xfa00f800fa00f8,
  0xfa00fa00f800f8,
  0xfa00fa00fa00f0,
  0xfa00fa00fa00fa,
  0xfc00fc00fc00fc
]

def wordsBlock19 : Array Word := #[
  0xfe00fe00fe00fe,
  0xff000000ff0000,
  0xff000000ff00aa,
  0xff000a00ff000a,
  0xff000f00ff000c,
  0xff002200ff0022,
  0xff00a800ff00a8,
  0xff00aa00ff0088,
  0xff00aa00ff00a0,
  0xff00aa00ff00aa,
  0xff00cc00ff00cc,
  0xff00f000ff00f0,
  0xff00fc00ff00fc,
  0xff00ff00000000,
  0xff00ff000000aa,
  0xff00ff000a000a
]

def wordsBlock20 : Array Word := #[
  0xff00ff00220022,
  0xff00ff00330030,
  0xff00ff00a800a8,
  0xff00ff00aa0088,
  0xff00ff00aa00a0,
  0xff00ff00aa00aa,
  0xff00ff00cc00cc,
  0xff00ff00f000f0,
  0xff00ff00fc00fc,
  0xff00ff00ff0000,
  0xff00ff00ff00cc,
  0xff00ff00ff00f0,
  0x202020202020202,
  0x404080804040808,
  0x5000a0005000a00,
  0x505000005050000
]

def wordsBlock21 : Array Word := #[
  0x5050a0a00000000,
  0x808020208080202,
  0xa0a0a0a0a0a0a0a,
  0xa0a0a0a0e0e0e0e,
  0xa0a0a0acececece,
  0xc0003000c000300,
  0xc0c00000c0c0000,
  0xc0c030300000000,
  0xc0c0c0c0c0c0c0c,
  0xc0c0c0c0e0e0e0e,
  0xc0c0e0e0c0c0e0e,
  0xe0e0e0e0e0e0e0e,
  0xf000f000f000f00,
  0xf0f00000f0f0000,
  0xf0f02020f0f0202,
  0xf0f0a0a0f0f0a0a
]

def wordsBlock22 : Array Word := #[
  0xf0f0f0f00000000,
  0xf0f0f0f0a0a0a0a,
  0xf0f0f0f0e0e0e0e,
  0x1010101020202020,
  0x1100110022002200,
  0x1111000022220000,
  0x1111111100000000,
  0x2020202002020202,
  0x2222222222222222,
  0x2222323222223232,
  0x2222f2f22222f2f2,
  0x2a2a2a2a2a2a2a2a,
  0x3000300003000300,
  0x3030000003030000,
  0x3030303000000000,
  0x3030303030303030
]

def wordsBlock23 : Array Word := #[
  0x3030303032323232,
  0x3030323230303232,
  0x3232323232323232,
  0x3300330033003300,
  0x3333000033330000,
  0x3333222233332222,
  0x3333323233333232,
  0x3333333300000000,
  0x3333333302020202,
  0x3333333322222222,
  0x4000100004000100,
  0x4040000004040000,
  0x4040100004040100,
  0x4040101000000000,
  0x4040101004000100,
  0x4040101004040000
]

def wordsBlock24 : Array Word := #[
  0x4040101004040100,
  0x4040101040401010,
  0x4040404004040404,
  0x4400110044001100,
  0x4444000044440000,
  0x4444111100000000,
  0x4444444444444444,
  0x4444444488888888,
  0x4444545444445454,
  0x4444888844448888,
  0x4848484848484848,
  0x4c4c4c4c4c4c4c4c,
  0x4e4e4e4e4e4e4e4e,
  0x5000500005000500,
  0x5050000005050000,
  0x5050505000000000
]

def wordsBlock25 : Array Word := #[
  0x5050505050505050,
  0x5050505054545454,
  0x50505050a0a0a0a0,
  0x5050a0a05050a0a0,
  0x5454545454545454,
  0x55005500aa00aa00,
  0x5500aa005500aa00,
  0x5555000055550000,
  0x55550000aaaa0000,
  0x5555545455555454,
  0x5555555500000000,
  0x5555555554545454,
  0x5555aaaa00000000,
  0x5656565656565656,
  0x5a005a005a005a00,
  0x5a5a00005a5a0000
]

def wordsBlock26 : Array Word := #[
  0x5a5a5a5a00000000,
  0x6060606060606060,
  0x6600660066006600,
  0x6666000066660000,
  0x6666666600000000,
  0x7070707070707070,
  0x7272727272727272,
  0x8080202008080202,
  0x8888222288882222,
  0x8888888822222222,
  0x8888888888888888,
  0x8a8a8a8a8a8a8a8a,
  0xa0a00a0aa0a00a0a,
  0xa0a0a0a00a0a0a0a,
  0xa0a0a0a0a0a0a0a0,
  0xa2a2a2a2a2a2a2a2
]

def wordsBlock27 : Array Word := #[
  0xa8a8a8a8a8a8a8a8,
  0xaaaa0a0aaaaa0a0a,
  0xaaaaaaaa22222222,
  0xaaaaaaaaaaaaaaaa,
  0xaaaaaaaaeeeeeeee,
  0xaaaafafaaaaafafa,
  0xacacacacacacacac,
  0xaeaeaeaeaeaeaeae,
  0xb8b8b8b8b8b8b8b8,
  0xbabababababababa,
  0xc00030000c000300,
  0xc08030200c080302,
  0xc0c000000c0c0000,
  0xc0c00c0cc0c00c0c,
  0xc0c020200c0c0202,
  0xc0c030000c0c0300
]

def wordsBlock28 : Array Word := #[
  0xc0c030200c0c0302,
  0xc0c0303000000000,
  0xc0c0303008080202,
  0xc0c030300c000300,
  0xc0c030300c080302,
  0xc0c030300c0c0000,
  0xc0c030300c0c0202,
  0xc0c030300c0c0300,
  0xc0c03030c0c03030,
  0xc0c0c0c00c0c0c0c,
  0xc0c0c0c030303030,
  0xc0c0c0c0c0c0c0c0,
  0xc4c4c4c4c4c4c4c4,
  0xc8c8c8c8c8c8c8c8,
  0xcacacacacacacaca,
  0xcc003300cc003300
]

def wordsBlock29 : Array Word := #[
  0xcc00cc0033003300,
  0xcccc000033330000,
  0xcccc0000cccc0000,
  0xcccc333300000000,
  0xcccccccc00000000,
  0xcccccccccccccccc,
  0xcccccccccccceeee,
  0xcccccccccececece,
  0xcccccccceeeeeeee,
  0xcccccececccccece,
  0xcccceeee00000000,
  0xcccceeeecccceeee,
  0xccccfcfcccccfcfc,
  0xcececece00000000,
  0xcececececececece,
  0xcfcfcfcfcececece
]

def wordsBlock30 : Array Word := #[
  0xd0d0d0d0d0d0d0d0,
  0xd8d8d8d8d8d8d8d8,
  0xdcdcdcdcdcdcdcdc,
  0xe0e0e0e0e0e0e0e0,
  0xe2e2e2e2e2e2e2e2,
  0xe4e4e4e4e4e4e4e4,
  0xeaeaeaeaeaeaeaea,
  0xecececececececec,
  0xeeee0e0eeeee0e0e,
  0xeeeececeeeeecece,
  0xeeeeeeee00000000,
  0xeeeeeeeeeeeeeeee,
  0xf0000f00f0000f00,
  0xf000f0000f000f00,
  0xf0f000000f0f0000,
  0xf0f00000f0f00000
]

def wordsBlock31 : Array Word := #[
  0xf0f00000fafa0000,
  0xf0f00f0f00000000,
  0xf0f0f0f000000000,
  0xf0f0f0f0f0f0f0f0,
  0xf0f0f0f0f0f0fafa,
  0xf0f0f0f0f2f2f2f2,
  0xf0f0f0f0fafafafa,
  0xf0f0f0f0fcfcfcfc,
  0xf0f0f2f2f0f0f2f2,
  0xf0f0fafaf0f0fafa,
  0xf2f20000f2f20000,
  0xf2f2f2f2f2f2f2f2,
  0xf3f3f2f2f3f3f2f2,
  0xf4f4f4f4f4f4f4f4,
  0xf8f8f8f8f8f8f8f8,
  0xfafa0000fafa0000
]

def wordsBlock32 : Array Word := #[
  0xfafafafa32323232,
  0xfafafafaf2f2f2f2,
  0xfafafafafafafafa,
  0xfcfc5454fcfc5454,
  0xfcfca8a8fcfca8a8,
  0xfcfcfcfc54545454,
  0xfcfcfcfca8a8a8a8,
  0xfcfcfcfcfcfcfcfc,
  0xfefefefefefefefe,
  0xff00ff00ff00ff00,
  0xff88ff88ff88ff88,
  0xffa0ffa0ffa0ffa0,
  0xffa8ffa8ffa8ffa8,
  0xffccffeeff00ff00,
  0xffceffceff00ff00,
  0xffeeffeeff00ff00
]

def wordsBlock33 : Array Word := #[
  0xffeeffeeffaaffaa,
  0xffeeffeeffccffcc,
  0xfff0ff00fffaff00,
  0xfff2ff00fff2ff00,
  0xfffaff00fffaff00,
  0xfffaffaafffaffaa,
  0xfffafff0fffafff0,
  0xffff0000ffff0000,
  0xffff0000ffff2222,
  0xffff0000ffffaaaa,
  0xffff0202ffff0202,
  0xffff0a0affff0a0a,
  0xffff2222ffff2222,
  0xffff3232ffff3232,
  0xffff5454ffff5454,
  0xffffa0a0ffffa0a0
]

def wordsBlock34 : Array Word := #[
  0xffffa8a8ffffa8a8,
  0xffffaaaaffffaaaa,
  0xffffccccffffcccc,
  0xffffeeeeffffeeee,
  0xfffff0f0fffff0f0,
  0xfffff2f2fffff2f2,
  0xfffffafafffffafa,
  0xfffffcfcfffffcfc,
  0xffffffa8ffffffa8,
  0xffffffeeffffff00,
  0xffffffff00000000,
  0xffffffff00000a0a,
  0xffffffff0000aaaa,
  0xffffffff02020202,
  0xffffffff0a0a0a0a,
  0xffffffff0e0e0e0e
]

def wordsBlock35 : Array Word := #[
  0xffffffff22222222,
  0xffffffff54545454,
  0xffffffff88888888,
  0xffffffffa8a8a8a8,
  0xffffffffaaaaaaaa,
  0xffffffffcccccccc,
  0xffffffffcececece,
  0xffffffffeeeeeeee,
  0xfffffffff0f0f0f0,
  0xfffffffffafafafa,
  0xfffffffffcfcfcfc,
  0xffffffffffa8ffa8,
  0xfffffffffffaff00,
  0xffffffffffff0000,
  0xffffffffffffaaaa
]

def wordsGet (i : Nat) : Word :=
  if i < 288 then
    if i < 144 then
      if i < 64 then
        if i < 32 then
          if i < 16 then
            wordsBlock0.getD (i-0) 0
          else
            wordsBlock1.getD (i-16) 0
        else
          if i < 48 then
            wordsBlock2.getD (i-32) 0
          else
            wordsBlock3.getD (i-48) 0
      else
        if i < 96 then
          if i < 80 then
            wordsBlock4.getD (i-64) 0
          else
            wordsBlock5.getD (i-80) 0
        else
          if i < 112 then
            wordsBlock6.getD (i-96) 0
          else
            if i < 128 then
              wordsBlock7.getD (i-112) 0
            else
              wordsBlock8.getD (i-128) 0
    else
      if i < 208 then
        if i < 176 then
          if i < 160 then
            wordsBlock9.getD (i-144) 0
          else
            wordsBlock10.getD (i-160) 0
        else
          if i < 192 then
            wordsBlock11.getD (i-176) 0
          else
            wordsBlock12.getD (i-192) 0
      else
        if i < 240 then
          if i < 224 then
            wordsBlock13.getD (i-208) 0
          else
            wordsBlock14.getD (i-224) 0
        else
          if i < 256 then
            wordsBlock15.getD (i-240) 0
          else
            if i < 272 then
              wordsBlock16.getD (i-256) 0
            else
              wordsBlock17.getD (i-272) 0
  else
    if i < 432 then
      if i < 352 then
        if i < 320 then
          if i < 304 then
            wordsBlock18.getD (i-288) 0
          else
            wordsBlock19.getD (i-304) 0
        else
          if i < 336 then
            wordsBlock20.getD (i-320) 0
          else
            wordsBlock21.getD (i-336) 0
      else
        if i < 384 then
          if i < 368 then
            wordsBlock22.getD (i-352) 0
          else
            wordsBlock23.getD (i-368) 0
        else
          if i < 400 then
            wordsBlock24.getD (i-384) 0
          else
            if i < 416 then
              wordsBlock25.getD (i-400) 0
            else
              wordsBlock26.getD (i-416) 0
    else
      if i < 496 then
        if i < 464 then
          if i < 448 then
            wordsBlock27.getD (i-432) 0
          else
            wordsBlock28.getD (i-448) 0
        else
          if i < 480 then
            wordsBlock29.getD (i-464) 0
          else
            wordsBlock30.getD (i-480) 0
      else
        if i < 528 then
          if i < 512 then
            wordsBlock31.getD (i-496) 0
          else
            wordsBlock32.getD (i-512) 0
        else
          if i < 544 then
            wordsBlock33.getD (i-528) 0
          else
            if i < 560 then
              wordsBlock34.getD (i-544) 0
            else
              wordsBlock35.getD (i-560) 0

def labelsBlock0 : Array Nat := #[
  0x904,
  0x1104,
  0x304,
  0x2104,
  0x504,
  0x308,
  0xa08,
  0x2208,
  0x1410,
  0x510,
  0xa20,
  0xc20,
  0xc10,
  0x1400,
  0x2200,
  0x920
]

def labelsBlock1 : Array Nat := #[
  0x1648,
  0x1100,
  0x2100,
  0x1440,
  0x2690,
  0x1618,
  0x2618,
  0x1140,
  0x2280,
  0xa00,
  0x10ca,
  0xc00,
  0x2180,
  0x1a48,
  0x300,
  0x500
]

def labelsBlock2 : Array Nat := #[
  0x10ce,
  0x3248,
  0x2c90,
  0x1304,
  0x106a,
  0x2504,
  0x3490,
  0xa48,
  0xc90,
  0x900,
  0x2248,
  0x10c6,
  0x1a60,
  0x2218,
  0x1418,
  0x1448
]

def labelsBlock3 : Array Nat := #[
  0x108a,
  0x1348,
  0x2ca0,
  0x2608,
  0x1610,
  0x718,
  0x1082,
  0x2590,
  0x1308,
  0x1a20,
  0x1608,
  0x2c20,
  0x105a,
  0x1076,
  0x708,
  0x318
]

def labelsBlock4 : Array Nat := #[
  0x53006a,
  0x105e,
  0x10e2,
  0x10ee,
  0x53008a,
  0x107a,
  0x1056,
  0x518,
  0x2610,
  0x32c0,
  0x34c0,
  0x101e,
  0x710,
  0x1300,
  0x3208,
  0x10da
]

def labelsBlock5 : Array Nat := #[
  0x2500,
  0x103a,
  0x1600,
  0x2600,
  0x31c0,
  0x1072,
  0x348,
  0x310,
  0x51306a,
  0x1a00,
  0x108e,
  0xe08,
  0x1006,
  0x3100,
  0x2c00,
  0x3648
]

def labelsBlock6 : Array Nat := #[
  0x590,
  0x100a,
  0x1092,
  0x1148,
  0x53108a,
  0x1408,
  0x704,
  0x2210,
  0x1066,
  0x1a08,
  0x2510,
  0x10de,
  0x3200,
  0x3400,
  0x2190,
  0x1960
]

def labelsBlock7 : Array Nat := #[
  0x1490,
  0x63006a,
  0x63008a,
  0x3690,
  0x18d5200c6,
  0x1915100c6,
  0x2290,
  0x508,
  0x1016,
  0x1032,
  0x6100c6,
  0x5300e2,
  0x5400ee,
  0x1c00,
  0x2a00,
  0x29a0
]

def labelsBlock8 : Array Nat := #[
  0x3240,
  0x1640,
  0x4100c6,
  0x1086,
  0x4200c6,
  0x104a,
  0x10d6,
  0x10d2,
  0x5210c6,
  0x5200c6,
  0x5100c6,
  0x1900,
  0x3410,
  0x1494100c6,
  0x7200c6,
  0x7100c6
]

def labelsBlock9 : Array Nat := #[
  0x1454200c6,
  0x2900,
  0x6200c6,
  0x6210c6,
  0x7210c6,
  0x3140,
  0x6300ca,
  0x6400ce,
  0xa60,
  0x5300c6,
  0x6300c6,
  0x5400c6,
  0x6400c6,
  0x4210c6,
  0x5310c6,
  0x5410c6
]

def labelsBlock10 : Array Nat := #[
  0x6410c6,
  0x5320c6,
  0x6320c6,
  0x5420c6,
  0x5430c6,
  0x3600,
  0xca0,
  0x520,
  0x320,
  0x1108,
  0x1022,
  0x103e,
  0x540,
  0x104e,
  0x1c60,
  0x3480
]

def labelsBlock11 : Array Nat := #[
  0x10ae,
  0x10a6,
  0x380,
  0x1c94100c6,
  0x1514100c6,
  0x51006a,
  0x2aa0,
  0x10c2,
  0x1c54200c6,
  0x14d4200c6,
  0x340,
  0x11c0,
  0x5410ee,
  0x51008a,
  0x1115100c6,
  0x10d5200c6
]

def labelsBlock12 : Array Nat := #[
  0x2108,
  0x1110,
  0x3180,
  0x1504,
  0xaa0,
  0xc60,
  0x107e,
  0x2110,
  0x2240,
  0x3440,
  0x2304,
  0x14d01006a,
  0x1340,
  0x2680,
  0x14d01008a,
  0x5130e2
]

def labelsBlock13 : Array Nat := #[
  0x1062,
  0x580,
  0x10b6,
  0x10ba,
  0x1180,
  0x2920,
  0x61306a,
  0x1920,
  0x63108a,
  0x1096,
  0x61006a,
  0x2c10,
  0x73108a,
  0x700,
  0x3104,
  0x18d11006a
]

def labelsBlock14 : Array Nat := #[
  0x2204,
  0x1c20,
  0x2a20,
  0x1404,
  0x61008a,
  0x6410ee,
  0x1052,
  0x5310ca,
  0x5410ce,
  0x2308,
  0x1495100c6,
  0x21c0,
  0x14c0,
  0x109a,
  0x22c0,
  0x43006a
]

def labelsBlock15 : Array Nat := #[
  0x18d11008a,
  0x1485100c6,
  0xe18,
  0x63106a,
  0x1485200c6,
  0x960,
  0x109e,
  0x71006a,
  0x6310e2,
  0x43008a,
  0x9a0,
  0x14901006a,
  0x41006a,
  0x1885100c6,
  0x71306a,
  0x1895100c6
]

def labelsBlock16 : Array Nat := #[
  0x5430e2,
  0x1456100c6,
  0x1496100c6,
  0x1497100c6,
  0x71008a,
  0x73006a,
  0x1487100c6,
  0x1c85200c6,
  0x1d45200c6,
  0x1456200c6,
  0x1496200c6,
  0x1457200c6,
  0x1487200c6,
  0x70306a,
  0x1d41210c6,
  0x1416210c6
]

def labelsBlock17 : Array Nat := #[
  0x1496210c6,
  0x1417210c6,
  0x2140,
  0x1480,
  0x14901008a,
  0x14903006a,
  0x41008a,
  0x73008a,
  0x53106a,
  0x1510,
  0x41306a,
  0x948,
  0x1a40,
  0x908,
  0x3280,
  0x451
]

def labelsBlock18 : Array Nat := #[
  0x1c14100c6,
  0x14503006a,
  0x1c503006a,
  0x1841100c6,
  0x2300,
  0x1500,
  0x1501100c6,
  0x1901100c6,
  0x10b2,
  0x5e1,
  0x14c5100c6,
  0x1505100c6,
  0x1905100c6,
  0x1896100c6,
  0x1c14200c6,
  0x14903008a
]

def labelsBlock19 : Array Nat := #[
  0x1881200c6,
  0x14c1200c6,
  0x18c1200c6,
  0x10aa,
  0x14c9200c6,
  0x18c9200c6,
  0x1509200c6,
  0x1d49300c6,
  0x70308a,
  0x1456300c6,
  0x1496300c6,
  0x1d45400c6,
  0x1456400c6,
  0x1496400c6,
  0x1540210c6,
  0x1940210c6
]

def labelsBlock20 : Array Nat := #[
  0x43108a,
  0x14c5210c6,
  0x1509210c6,
  0x1c16210c6,
  0x1c17210c6,
  0x1416410c6,
  0x1c16410c6,
  0x1496410c6,
  0x1416320c6,
  0x1c16320c6,
  0x1456320c6,
  0xd00,
  0x1915300e2,
  0xb00,
  0x6300e2,
  0x14503008a
]

def labelsBlock21 : Array Nat := #[
  0x1c503008a,
  0x1cd01006a,
  0x63005a,
  0x6400ee,
  0x1141210c6,
  0x50306a,
  0x50308a,
  0x910,
  0x1310,
  0x990,
  0x521056,
  0x531056,
  0x10a2,
  0x610056,
  0x521072,
  0x620072
]

def labelsBlock22 : Array Nat := #[
  0x455,
  0x1cd01008a,
  0x541501100c6,
  0x641901100c6,
  0x5d1,
  0x5e5,
  0x615,
  0x621,
  0x625,
  0x14d5100c6,
  0x18d5100c6,
  0x671,
  0x1515100c6,
  0x63007a,
  0x14d6100c6,
  0x18d6100c6
]

def labelsBlock23 : Array Nat := #[
  0x1516100c6,
  0x1916100c6,
  0x1c42100c6,
  0x1502100c6,
  0x1902100c6,
  0x5324c1200c6,
  0x6328c1200c6,
  0x8ed,
  0x18d5400ee,
  0x51308a,
  0x96d,
  0x14d5200c6,
  0x1515200c6,
  0x1915200c6,
  0x5430ee,
  0x14d6200c6
]

def labelsBlock24 : Array Nat := #[
  0x18d6200c6,
  0x1516200c6,
  0x1916200c6,
  0x1c82200c6,
  0x14c2200c6,
  0x18c2200c6,
  0x18c1300c6,
  0x14c5300c6,
  0x1d45300c6,
  0x14c9300c6,
  0x150d300c6,
  0x1515300c6,
  0x1915300c6,
  0x1516300c6,
  0x1916300c6,
  0x18ca300c6
]

def labelsBlock25 : Array Nat := #[
  0x1901400c6,
  0x1505400c6,
  0x1509400c6,
  0x1d49400c6,
  0x150d400c6,
  0x1d4d400c6,
  0x14d6400c6,
  0x1906400c6,
  0x14d5210c6,
  0x18d5210c6,
  0x1515210c6,
  0x1915210c6,
  0x18c9310c6,
  0x150a410c6,
  0x532072,
  0x2580
]

def labelsBlock26 : Array Nat := #[
  0x461,
  0x4cd,
  0x535,
  0x790,
  0x569,
  0x1494400ce,
  0x5240de,
  0x841,
  0x748,
  0x1318,
  0x875,
  0x1494300ca,
  0x5230da,
  0x548,
  0x2508,
  0x45d
]

def labelsBlock27 : Array Nat := #[
  0x1514100ee,
  0x5100e2,
  0x4c9,
  0x5100ee,
  0x144d1006a,
  0x14c51008a,
  0x531,
  0xa04,
  0xa18,
  0xc08,
  0xa10,
  0x5a5,
  0x5ad,
  0xe00,
  0x636495100c6,
  0x646495100c6
]

def labelsBlock28 : Array Nat := #[
  0x6464d5100c6,
  0x756115100c6,
  0xc18,
  0x4400ce,
  0x4bd,
  0x4c5,
  0x636496100c6,
  0x14d6300e2,
  0x759,
  0xe20,
  0x5310e2,
  0x7300e2,
  0x14d4100e2,
  0x83d,
  0xc04,
  0x8c1
]

def labelsBlock29 : Array Nat := #[
  0x8c9,
  0x14d23108a,
  0x7560d5200c6,
  0x4300ca,
  0x763515200c6,
  0x831,
  0x839,
  0x646456200c6,
  0x1516400ee,
  0xa61,
  0x7400ee,
  0xad1,
  0xabd,
  0x646456300c6,
  0xba1,
  0xb95
]

def labelsBlock30 : Array Nat := #[
  0x636496400c6,
  0x5340ee,
  0x536141210c6,
  0x546141210c6,
  0x6130e2,
  0x7410ee,
  0x5310ee,
  0x5410e2,
  0x4d,
  0xd48,
  0x55,
  0x69,
  0x75,
  0x81,
  0x99,
  0xc48
]

def labelsBlock31 : Array Nat := #[
  0xbd,
  0xcd,
  0x1c40,
  0xfd,
  0x390,
  0xb90,
  0x105,
  0x119,
  0x125,
  0x131,
  0x149,
  0xa90,
  0x16d,
  0x17d,
  0x1a9,
  0x1b90
]

def labelsBlock32 : Array Nat := #[
  0x1b1,
  0x1c5,
  0x1d1,
  0x1390,
  0x1dd,
  0x1f5,
  0x1a90,
  0x219,
  0x229,
  0x255,
  0x630092,
  0x289,
  0x295,
  0x29d,
  0x2ad,
  0x62008e
]

def labelsBlock33 : Array Nat := #[
  0x2e5,
  0x2f1,
  0x52108e,
  0x335,
  0x38d,
  0x395,
  0x3b9,
  0x401,
  0x465,
  0x7100e2,
  0x4300e2,
  0x4b1,
  0x4b5,
  0x4b9,
  0x4c1,
  0x4f1
]

def labelsBlock34 : Array Nat := #[
  0x144f1006a,
  0x511,
  0x539,
  0x53d,
  0x541,
  0x545,
  0x54d,
  0x555,
  0x2518,
  0x559,
  0x55d,
  0x565,
  0x585,
  0x589,
  0x5a1,
  0x5c1
]

def labelsBlock35 : Array Nat := #[
  0x5fd,
  0x60d,
  0x63d,
  0x1915100ee,
  0x14d23106a,
  0x635,
  0x659,
  0x6a5,
  0x1516100ee,
  0x6f9,
  0x715,
  0x2380,
  0x791,
  0x6100ee,
  0x739,
  0x75d
]

def labelsBlock36 : Array Nat := #[
  0x779,
  0x7cd,
  0x7100ee,
  0x14c71008a,
  0x7dd,
  0x7f5,
  0x4400ee,
  0x825,
  0x829,
  0x82d,
  0x835,
  0x845,
  0x849,
  0x84d,
  0x851,
  0x859
]

def labelsBlock37 : Array Nat := #[
  0x861,
  0x865,
  0x869,
  0x871,
  0x8a1,
  0x8a5,
  0x8ad,
  0x8dd,
  0x915,
  0x931,
  0x94d,
  0x18d5100e2,
  0x9a9,
  0x9d1,
  0x14d6100e2,
  0x9ed
]

def labelsBlock38 : Array Nat := #[
  0xa09,
  0x1540,
  0xa6d,
  0x6100e2,
  0xa45,
  0xa65,
  0xab5,
  0xab9,
  0xac9,
  0xb01,
  0xb69,
  0xb8d,
  0xb91,
  0xb9d,
  0x4130e2,
  0x4410ee
]

def labelsBlock39 : Array Nat := #[
  0x10be,
  0xcd9,
  0xcf1,
  0x7130e2,
  0x6430e2,
  0x6340ee,
  0x940,
  0x51,
  0x59,
  0x5d,
  0x61,
  0x1320,
  0x85,
  0x89,
  0x91,
  0xa5
]

def labelsBlock40 : Array Nat := #[
  0xad,
  0xc1,
  0xc5,
  0xdd,
  0x102a,
  0x101,
  0x109,
  0x10d,
  0x111,
  0x2520,
  0x135,
  0x139,
  0x141,
  0x155,
  0x15d,
  0x171
]

def labelsBlock41 : Array Nat := #[
  0x175,
  0x18d,
  0x1ad,
  0x1b5,
  0x1b9,
  0x1bd,
  0x1e1,
  0x1e5,
  0x1ed,
  0x201,
  0x209,
  0x21d,
  0x221,
  0x239,
  0x259,
  0x25d
]

def labelsBlock42 : Array Nat := #[
  0x261,
  0x265,
  0x269,
  0x2a1,
  0x2a5,
  0x740,
  0x2b1,
  0x2b5,
  0x2b9,
  0x2c1,
  0x2c5,
  0x2f5,
  0x2f9,
  0x53208e,
  0x301,
  0x309
]

def labelsBlock43 : Array Nat := #[
  0x315,
  0x531092,
  0x532092,
  0x33d,
  0x349,
  0x351,
  0x385,
  0x389,
  0x3b5,
  0x425,
  0x1454300e2,
  0x1c54300e2,
  0x475,
  0x479,
  0x47d,
  0x1494300e2
]

def labelsBlock44 : Array Nat := #[
  0x1494100ee,
  0x485,
  0x489,
  0x48d,
  0x1514300e2,
  0x495,
  0x499,
  0x49d,
  0x4a5,
  0x459,
  0x4a1,
  0x4a9,
  0x4100ee,
  0x4d1,
  0x4d9,
  0x4e1
]

def labelsBlock45 : Array Nat := #[
  0x4d5,
  0x4dd,
  0x4e5,
  0x4e9,
  0x4f5,
  0x4f9,
  0x4fd,
  0x505,
  0x509,
  0x515,
  0x519,
  0x521,
  0x529,
  0xba0,
  0x13c0,
  0x6400de
]

def labelsBlock46 : Array Nat := #[
  0x3108,
  0x3148,
  0x5400de,
  0x571,
  0x575,
  0x595,
  0x579,
  0x57d,
  0x581,
  0x58d,
  0x591,
  0x599,
  0x59d,
  0x5a9,
  0x5b1,
  0x5b9
]

def labelsBlock47 : Array Nat := #[
  0x5bd,
  0x5c5,
  0x5d5,
  0x5dd,
  0x5e9,
  0x5ed,
  0x5f5,
  0x5f9,
  0x609,
  0x619,
  0x1940,
  0x2980,
  0x2a80,
  0x2c80,
  0x645,
  0x649
]

def labelsBlock48 : Array Nat := #[
  0x64d,
  0x18d5300e2,
  0x661,
  0x665,
  0x669,
  0x720,
  0x1160,
  0x675,
  0x679,
  0x689,
  0x526115300e2,
  0x1115300e2,
  0x6b5,
  0x6b9,
  0x6c5,
  0x6c9
]

def labelsBlock49 : Array Nat := #[
  0x6d5,
  0x4ed,
  0x501,
  0x50d,
  0x51d,
  0x525,
  0x52d,
  0x549,
  0x551,
  0x561,
  0x56d,
  0x5b5,
  0x5c9,
  0x5d9,
  0x5f1,
  0x601
]

def labelsBlock50 : Array Nat := #[
  0x605,
  0x611,
  0x6d1,
  0x6dd,
  0x6e1,
  0x6e5,
  0x6f1,
  0x6f5,
  0x6fd,
  0x701,
  0x705,
  0x709,
  0x741,
  0x761,
  0xb20,
  0x781
]

def labelsBlock51 : Array Nat := #[
  0x7a1,
  0x7a9,
  0x6ed,
  0x77d,
  0x785,
  0x789,
  0x78d,
  0x795,
  0x799,
  0x79d,
  0x7a5,
  0x7ad,
  0x7b1,
  0x7b9,
  0x7bd,
  0x7c5
]

def labelsBlock52 : Array Nat := #[
  0x14d31008a,
  0x7d1,
  0x7d5,
  0x7e1,
  0x7e5,
  0x7f1,
  0x7d9,
  0x7e9,
  0x7ed,
  0x7f9,
  0x801,
  0x1454400ee,
  0x1c54400ee,
  0x1494100e2,
  0x1494400ee,
  0x14d4400ee
]

def labelsBlock53 : Array Nat := #[
  0x809,
  0x4100e2,
  0xd60,
  0x25c0,
  0x6310da,
  0x3190,
  0x5310da,
  0x87d,
  0x885,
  0x88d,
  0x891,
  0x8b1,
  0x895,
  0x899,
  0x89d,
  0x8a9
]

def labelsBlock54 : Array Nat := #[
  0x8b5,
  0x8b9,
  0x8bd,
  0x8c5,
  0x8cd,
  0x8d5,
  0x8d9,
  0x8e1,
  0x8e9,
  0x8f1,
  0x8f5,
  0x901,
  0x909,
  0x919,
  0x921,
  0x925
]

def labelsBlock55 : Array Nat := #[
  0x929,
  0x935,
  0x93d,
  0x945,
  0x951,
  0x95d,
  0x965,
  0x21a0,
  0x971,
  0x975,
  0x985,
  0x5260d5400ee,
  0x98d,
  0x10d5400ee,
  0x99d,
  0x9bd
]

def labelsBlock56 : Array Nat := #[
  0x9c5,
  0x1915400ee,
  0x855,
  0x85d,
  0x86d,
  0x879,
  0x881,
  0x889,
  0x8d1,
  0x8e5,
  0x8f9,
  0x905,
  0x939,
  0x941,
  0x955,
  0x959
]

def labelsBlock57 : Array Nat := #[
  0x961,
  0x969,
  0x9dd,
  0x9e5,
  0x9e9,
  0x9f1,
  0x9f5,
  0x9f9,
  0x9fd,
  0xa2d,
  0xa49,
  0xd20,
  0xa81,
  0xa89,
  0xa29,
  0xa69
]

def labelsBlock58 : Array Nat := #[
  0xa71,
  0xa75,
  0xa79,
  0xa7d,
  0xa85,
  0xa8d,
  0xa91,
  0xa95,
  0xa9d,
  0x14d31006a,
  0xaad,
  0xacd,
  0x70108a,
  0x1d4d300e2,
  0xae5,
  0x5430ca
]

def labelsBlock59 : Array Nat := #[
  0xac1,
  0xac5,
  0xad9,
  0xadd,
  0xaf1,
  0xaf5,
  0x5300ee,
  0xafd,
  0xb21,
  0xb0d,
  0xb11,
  0xb31,
  0xb41,
  0x1516300ee,
  0xb4d,
  0xb55
]

def labelsBlock60 : Array Nat := #[
  0xb75,
  0xb81,
  0xb6d,
  0xb79,
  0xb7d,
  0xb85,
  0x6300ee,
  0xb99,
  0x70106a,
  0x1d51400ee,
  0xbc1,
  0x5430ce,
  0xba9,
  0x5400e2,
  0xbad,
  0xbb5
]

def labelsBlock61 : Array Nat := #[
  0xbb9,
  0xbcd,
  0xbd9,
  0x14d6400e2,
  0xbe5,
  0xbf5,
  0xbed,
  0xbf9,
  0xbfd,
  0xc21,
  0xc31,
  0xc39,
  0xc35,
  0x6400e2,
  0xc3d,
  0xc41
]

def labelsBlock62 : Array Nat := #[
  0xc55,
  0xc81,
  0xc91,
  0xc95,
  0xcad,
  0xcbd,
  0xcc1,
  0x18d5130e2,
  0xce1,
  0x1915410ee,
  0xcf9,
  0xccd,
  0xcd1,
  0xd05,
  0xd15,
  0xd29
]

def labelsBlock63 : Array Nat := #[
  0xd2d,
  0xd35,
  0xd41,
  0xd5d,
  0x100e,
  0x101a,
  0x1012,
  0x1026,
  0x1036,
  0x102e,
  0x980,
  0x1720,
  0x65,
  0x71,
  0x6d,
  0x79
]

def labelsBlock64 : Array Nat := #[
  0x95,
  0x8d,
  0x9d,
  0xa9,
  0xb1,
  0x1620,
  0xc9,
  0xb9,
  0xd1,
  0xd9,
  0xe1,
  0xe9,
  0xed,
  0x7d,
  0xa1,
  0xb5
]

def labelsBlock65 : Array Nat := #[
  0xd5,
  0xe5,
  0xf1,
  0x1460,
  0x1c90,
  0x2720,
  0x115,
  0x121,
  0x11d,
  0x129,
  0x145,
  0x13d,
  0x14d,
  0x159,
  0x161,
  0x2620
]

def labelsBlock66 : Array Nat := #[
  0x179,
  0x169,
  0x181,
  0x189,
  0x191,
  0x199,
  0x19d,
  0x12d,
  0x151,
  0x165,
  0x185,
  0x195,
  0x1a1,
  0x2d48,
  0x1c1,
  0x1cd
]

def labelsBlock67 : Array Nat := #[
  0x1c9,
  0x1d5,
  0x2548,
  0x1f1,
  0x1e9,
  0x1f9,
  0x205,
  0x20d,
  0x2c48,
  0x225,
  0x215,
  0x22d,
  0x235,
  0x23d,
  0x245,
  0x249
]

def labelsBlock68 : Array Nat := #[
  0x1d9,
  0x1fd,
  0x211,
  0x231,
  0x241,
  0x24d,
  0x26d,
  0x271,
  0x275,
  0x279,
  0x281,
  0x28d,
  0x285,
  0x291,
  0x299,
  0x2bd
]

def labelsBlock69 : Array Nat := #[
  0x2c9,
  0x2cd,
  0x2d1,
  0x2d9,
  0x2e9,
  0x2dd,
  0x2e1,
  0x2ed,
  0x305,
  0x30d,
  0x311,
  0x319,
  0x321,
  0x32d,
  0x325,
  0x329
]

def labelsBlock70 : Array Nat := #[
  0x331,
  0x341,
  0x345,
  0x34d,
  0x355,
  0x361,
  0x369,
  0x35d,
  0x365,
  0x36d,
  0x375,
  0x379,
  0x37d,
  0x381,
  0x391,
  0x399
]

def labelsBlock71 : Array Nat := #[
  0x3a1,
  0x3a5,
  0x3a9,
  0x3ad,
  0x3b1,
  0x3bd,
  0x149010056,
  0x14d010056,
  0x3c5,
  0x3c9,
  0x410056,
  0x14d312056,
  0x3d5,
  0x712056,
  0x149313056,
  0x3dd
]

def labelsBlock72 : Array Nat := #[
  0x713056,
  0x3cd,
  0x3d1,
  0x3d9,
  0x3e1,
  0x145020072,
  0x14d020072,
  0x3e9,
  0x3ed,
  0x420072,
  0x14d321072,
  0x3f9,
  0x721072,
  0x145232072,
  0x405,
  0x632072
]

def labelsBlock73 : Array Nat := #[
  0x3f1,
  0x3f5,
  0x3fd,
  0x409,
  0x411,
  0x415,
  0x419,
  0x41d,
  0x421,
  0x429,
  0x431,
  0x435,
  0x439,
  0x43d,
  0x441,
  0x445
]

def labelsBlock74 : Array Nat := #[
  0x27d,
  0x2a9,
  0x2d5,
  0x2fd,
  0x31d,
  0x339,
  0x359,
  0x371,
  0x39d,
  0x3c1,
  0x3e5,
  0x40d,
  0x42d,
  0x449,
  0x1d14100ee,
  0x469
]

def labelsBlock75 : Array Nat := #[
  0x46d,
  0x471,
  0x481,
  0x491,
  0x3900,
  0x2118,
  0x1501300e2,
  0x1501100ee,
  0x6400e6,
  0x5400e6,
  0x1901300e2,
  0x10e6,
  0x3290,
  0x1505100ee,
  0x5cd,
  0x1518
]

def labelsBlock76 : Array Nat := #[
  0x1508,
  0x1905100ee,
  0x1455300e2,
  0x1515100ee,
  0x629,
  0x62d,
  0x631,
  0x639,
  0x1855300e2,
  0x655,
  0x14d960115100c6,
  0x560115100c6,
  0x561115100c6,
  0x53205e,
  0x536115100c6,
  0x67d
]

def labelsBlock77 : Array Nat := #[
  0x681,
  0x685,
  0x68d,
  0x691,
  0x695,
  0x699,
  0x6a1,
  0x6a9,
  0x6ad,
  0x6b1,
  0x6d9,
  0x61d,
  0x641,
  0x651,
  0x65d,
  0x66d
]

def labelsBlock78 : Array Nat := #[
  0x69d,
  0x6bd,
  0x6c1,
  0x6cd,
  0x1704,
  0x70d,
  0x711,
  0x719,
  0x71d,
  0x721,
  0x729,
  0x731,
  0x735,
  0x745,
  0x749,
  0x755
]

def labelsBlock79 : Array Nat := #[
  0x76d,
  0x771,
  0x775,
  0x780,
  0x1502100ee,
  0x7b5,
  0x725,
  0x72d,
  0x73d,
  0x74d,
  0x751,
  0x765,
  0x769,
  0x1457300e2,
  0x1517100ee,
  0x7fd
]

def labelsBlock80 : Array Nat := #[
  0x1507100ee,
  0x7c9,
  0x1cd4100e2,
  0x80d,
  0x811,
  0x815,
  0x819,
  0x81d,
  0x1118,
  0x14c1100e2,
  0x14c1400ee,
  0x6300ea,
  0x5300ea,
  0x3110,
  0x18c1400ee,
  0x10ea
]

def labelsBlock81 : Array Nat := #[
  0xe10,
  0x3448,
  0x144d100e2,
  0x2318,
  0x8fd,
  0x911,
  0x1d45400ee,
  0x2310,
  0x949,
  0x18c5100e2,
  0x1519600d5200c6,
  0x5600d5200c6,
  0x5620d5200c6,
  0x532076,
  0x5460d5200c6,
  0x979
]

def labelsBlock82 : Array Nat := #[
  0x97d,
  0x981,
  0x989,
  0x5250d11006a,
  0x991,
  0x995,
  0x999,
  0x10d11006a,
  0x9a5,
  0x9ad,
  0x9b1,
  0x9b5,
  0x9cd,
  0x90d,
  0x91d,
  0x92d
]

def labelsBlock83 : Array Nat := #[
  0x9a1,
  0x9b9,
  0x9c1,
  0x9c9,
  0x9d5,
  0x9d9,
  0x2704,
  0xa01,
  0xa05,
  0xa0d,
  0xa11,
  0xa15,
  0xa1d,
  0xa39,
  0xa3d,
  0xa41
]

def labelsBlock84 : Array Nat := #[
  0xa4d,
  0xa51,
  0xa5d,
  0x14c2100e2,
  0xa99,
  0xa19,
  0xa21,
  0xa25,
  0xa31,
  0xa35,
  0xa55,
  0xa59,
  0x14d7100e2,
  0x1457400ee,
  0xaa9,
  0x144f100e2
]

def labelsBlock85 : Array Nat := #[
  0xaa5,
  0xad5,
  0xae1,
  0x150d300ee,
  0x1515300e2,
  0x1515300ee,
  0xae9,
  0xaed,
  0xaf9,
  0xb05,
  0xb19,
  0xb15,
  0xb1d,
  0xb25,
  0xb29,
  0xb2d
]

def labelsBlock86 : Array Nat := #[
  0xb39,
  0xb45,
  0xb61,
  0xb65,
  0xb71,
  0x1710,
  0xb35,
  0xb3d,
  0xb49,
  0xb51,
  0xb59,
  0xb5d,
  0xba5,
  0xbbd,
  0x150d400e2,
  0x70305a
]

def labelsBlock87 : Array Nat := #[
  0x1d4d400ee,
  0xbb1,
  0xbc5,
  0xbc9,
  0xbd1,
  0xbdd,
  0xc01,
  0xbf1,
  0xc05,
  0xc09,
  0xc0d,
  0xc11,
  0xc19,
  0xc2d,
  0x2708,
  0x3308
]

def labelsBlock88 : Array Nat := #[
  0xbe1,
  0xbe9,
  0xc15,
  0xc1d,
  0xc25,
  0xc29,
  0xc49,
  0xc4d,
  0x1120,
  0xa40,
  0x1420,
  0xc40,
  0x2120,
  0x2220,
  0xa80,
  0xc59
]

def labelsBlock89 : Array Nat := #[
  0xc5d,
  0xc61,
  0xc65,
  0xc69,
  0xc6d,
  0xc71,
  0xc75,
  0xc79,
  0xc85,
  0xc89,
  0xc8d,
  0xc9d,
  0xca1,
  0xca5,
  0xcb5,
  0xcb9
]

def labelsBlock90 : Array Nat := #[
  0x1d41130e2,
  0x1d41410ee,
  0x14c5410ee,
  0x1505130e2,
  0xcd5,
  0xced,
  0x2c60,
  0xc7d,
  0xc99,
  0xca9,
  0xcb1,
  0xcc5,
  0xcc9,
  0xcdd,
  0xce5,
  0xce9
]

def labelsBlock91 : Array Nat := #[
  0xcf5,
  0xcfd,
  0xd01,
  0x1416130e2,
  0x14521306a,
  0xd0d,
  0xd11,
  0x1417410ee,
  0xd1d,
  0xd21,
  0xd3d,
  0x1416410ee,
  0xd49,
  0xd4d,
  0xd55,
  0x1516410ee
]

def labelsBlock92 : Array Nat := #[
  0xd45,
  0xd51,
  0xd59,
  0xd69,
  0x1416310e2,
  0xd71,
  0xd75,
  0xd7d,
  0x14d6310e2,
  0xd6d,
  0xd79,
  0xd81,
  0x4ad,
  0x6e9,
  0x7c1,
  0x805
]

def labelsBlock93 : Array Nat := #[
  0x821,
  0x9e1,
  0xaa1,
  0xab1,
  0xb09,
  0xb89,
  0xbd5,
  0xc45,
  0xc51,
  0xd09,
  0xd19,
  0xd25,
  0xd31,
  0xd39,
  0xd61,
  0xd65
]

def labelsBlock94 : Array Nat := #[
  0xd85,
  0xd89,
  0xd8d,
  0x1,
  0x5,
  0x9,
  0xd,
  0x11,
  0x15,
  0x19,
  0x1d,
  0x21,
  0x25,
  0x1002,
  0x29,
  0x2d
]

def labelsBlock95 : Array Nat := #[
  0x31,
  0x35,
  0x39,
  0x3d,
  0x41,
  0x45,
  0x49,
  0xf5,
  0xf9,
  0x1a5,
  0x1046,
  0x1042,
  0x251,
  0x44d,
  0x106e,
  0xd91
]

def labelsGet (i : Nat) : Nat :=
  if i < 768 then
    if i < 384 then
      if i < 192 then
        if i < 96 then
          if i < 48 then
            if i < 16 then
              labelsBlock0.getD (i-0) 3
            else
              if i < 32 then
                labelsBlock1.getD (i-16) 3
              else
                labelsBlock2.getD (i-32) 3
          else
            if i < 64 then
              labelsBlock3.getD (i-48) 3
            else
              if i < 80 then
                labelsBlock4.getD (i-64) 3
              else
                labelsBlock5.getD (i-80) 3
        else
          if i < 144 then
            if i < 112 then
              labelsBlock6.getD (i-96) 3
            else
              if i < 128 then
                labelsBlock7.getD (i-112) 3
              else
                labelsBlock8.getD (i-128) 3
          else
            if i < 160 then
              labelsBlock9.getD (i-144) 3
            else
              if i < 176 then
                labelsBlock10.getD (i-160) 3
              else
                labelsBlock11.getD (i-176) 3
      else
        if i < 288 then
          if i < 240 then
            if i < 208 then
              labelsBlock12.getD (i-192) 3
            else
              if i < 224 then
                labelsBlock13.getD (i-208) 3
              else
                labelsBlock14.getD (i-224) 3
          else
            if i < 256 then
              labelsBlock15.getD (i-240) 3
            else
              if i < 272 then
                labelsBlock16.getD (i-256) 3
              else
                labelsBlock17.getD (i-272) 3
        else
          if i < 336 then
            if i < 304 then
              labelsBlock18.getD (i-288) 3
            else
              if i < 320 then
                labelsBlock19.getD (i-304) 3
              else
                labelsBlock20.getD (i-320) 3
          else
            if i < 352 then
              labelsBlock21.getD (i-336) 3
            else
              if i < 368 then
                labelsBlock22.getD (i-352) 3
              else
                labelsBlock23.getD (i-368) 3
    else
      if i < 576 then
        if i < 480 then
          if i < 432 then
            if i < 400 then
              labelsBlock24.getD (i-384) 3
            else
              if i < 416 then
                labelsBlock25.getD (i-400) 3
              else
                labelsBlock26.getD (i-416) 3
          else
            if i < 448 then
              labelsBlock27.getD (i-432) 3
            else
              if i < 464 then
                labelsBlock28.getD (i-448) 3
              else
                labelsBlock29.getD (i-464) 3
        else
          if i < 528 then
            if i < 496 then
              labelsBlock30.getD (i-480) 3
            else
              if i < 512 then
                labelsBlock31.getD (i-496) 3
              else
                labelsBlock32.getD (i-512) 3
          else
            if i < 544 then
              labelsBlock33.getD (i-528) 3
            else
              if i < 560 then
                labelsBlock34.getD (i-544) 3
              else
                labelsBlock35.getD (i-560) 3
      else
        if i < 672 then
          if i < 624 then
            if i < 592 then
              labelsBlock36.getD (i-576) 3
            else
              if i < 608 then
                labelsBlock37.getD (i-592) 3
              else
                labelsBlock38.getD (i-608) 3
          else
            if i < 640 then
              labelsBlock39.getD (i-624) 3
            else
              if i < 656 then
                labelsBlock40.getD (i-640) 3
              else
                labelsBlock41.getD (i-656) 3
        else
          if i < 720 then
            if i < 688 then
              labelsBlock42.getD (i-672) 3
            else
              if i < 704 then
                labelsBlock43.getD (i-688) 3
              else
                labelsBlock44.getD (i-704) 3
          else
            if i < 736 then
              labelsBlock45.getD (i-720) 3
            else
              if i < 752 then
                labelsBlock46.getD (i-736) 3
              else
                labelsBlock47.getD (i-752) 3
  else
    if i < 1152 then
      if i < 960 then
        if i < 864 then
          if i < 816 then
            if i < 784 then
              labelsBlock48.getD (i-768) 3
            else
              if i < 800 then
                labelsBlock49.getD (i-784) 3
              else
                labelsBlock50.getD (i-800) 3
          else
            if i < 832 then
              labelsBlock51.getD (i-816) 3
            else
              if i < 848 then
                labelsBlock52.getD (i-832) 3
              else
                labelsBlock53.getD (i-848) 3
        else
          if i < 912 then
            if i < 880 then
              labelsBlock54.getD (i-864) 3
            else
              if i < 896 then
                labelsBlock55.getD (i-880) 3
              else
                labelsBlock56.getD (i-896) 3
          else
            if i < 928 then
              labelsBlock57.getD (i-912) 3
            else
              if i < 944 then
                labelsBlock58.getD (i-928) 3
              else
                labelsBlock59.getD (i-944) 3
      else
        if i < 1056 then
          if i < 1008 then
            if i < 976 then
              labelsBlock60.getD (i-960) 3
            else
              if i < 992 then
                labelsBlock61.getD (i-976) 3
              else
                labelsBlock62.getD (i-992) 3
          else
            if i < 1024 then
              labelsBlock63.getD (i-1008) 3
            else
              if i < 1040 then
                labelsBlock64.getD (i-1024) 3
              else
                labelsBlock65.getD (i-1040) 3
        else
          if i < 1104 then
            if i < 1072 then
              labelsBlock66.getD (i-1056) 3
            else
              if i < 1088 then
                labelsBlock67.getD (i-1072) 3
              else
                labelsBlock68.getD (i-1088) 3
          else
            if i < 1120 then
              labelsBlock69.getD (i-1104) 3
            else
              if i < 1136 then
                labelsBlock70.getD (i-1120) 3
              else
                labelsBlock71.getD (i-1136) 3
    else
      if i < 1344 then
        if i < 1248 then
          if i < 1200 then
            if i < 1168 then
              labelsBlock72.getD (i-1152) 3
            else
              if i < 1184 then
                labelsBlock73.getD (i-1168) 3
              else
                labelsBlock74.getD (i-1184) 3
          else
            if i < 1216 then
              labelsBlock75.getD (i-1200) 3
            else
              if i < 1232 then
                labelsBlock76.getD (i-1216) 3
              else
                labelsBlock77.getD (i-1232) 3
        else
          if i < 1296 then
            if i < 1264 then
              labelsBlock78.getD (i-1248) 3
            else
              if i < 1280 then
                labelsBlock79.getD (i-1264) 3
              else
                labelsBlock80.getD (i-1280) 3
          else
            if i < 1312 then
              labelsBlock81.getD (i-1296) 3
            else
              if i < 1328 then
                labelsBlock82.getD (i-1312) 3
              else
                labelsBlock83.getD (i-1328) 3
      else
        if i < 1440 then
          if i < 1392 then
            if i < 1360 then
              labelsBlock84.getD (i-1344) 3
            else
              if i < 1376 then
                labelsBlock85.getD (i-1360) 3
              else
                labelsBlock86.getD (i-1376) 3
          else
            if i < 1408 then
              labelsBlock87.getD (i-1392) 3
            else
              if i < 1424 then
                labelsBlock88.getD (i-1408) 3
              else
                labelsBlock89.getD (i-1424) 3
        else
          if i < 1488 then
            if i < 1456 then
              labelsBlock90.getD (i-1440) 3
            else
              if i < 1472 then
                labelsBlock91.getD (i-1456) 3
              else
                labelsBlock92.getD (i-1472) 3
          else
            if i < 1504 then
              labelsBlock93.getD (i-1488) 3
            else
              if i < 1520 then
                labelsBlock94.getD (i-1504) 3
              else
                labelsBlock95.getD (i-1520) 3

def decodeBank : Nat → Nat → List Word
  | 0, _ => []
  | n+1, enc => wordsGet (enc % 1024) :: decodeBank n (enc >>> 10)

def decodeHints (enc i : Nat) := labelsGet ((enc >>> (i * 11)) % 2048)

def viewsBlock0 : Array View := #[
  ⟨0x1400140000,⟨18,by decide⟩,0x400100000,decodeBank 2 0x1d474,2,decodeHints 0xbc60bc1502f⟩,
  ⟨0xf0f,⟨0,by decide⟩,0xe08,decodeBank 3 0x400801,3,decodeHints 0xbc80140101e0000a40c81e⟩,
  ⟨0x3333,⟨0,by decide⟩,0x3220,decodeBank 3 0xb02408,3,decodeHints 0xbca0240201f0000a40d81f⟩,
  ⟨0x330033,⟨0,by decide⟩,0x320020,decodeBank 3 0x1805c16,3,decodeHints 0xbcc0240201f0020440681f⟩,
  ⟨0x660066,⟨1,by decide⟩,0x620020,decodeBank 3 0x1b06819,3,decodeHints 0xbce11c0200400200402004⟩,
  ⟨0xcc0033,⟨0,by decide⟩,0xc80020,decodeBank 3 0x200781c,3,decodeHints 0xbd00240201f0461342901f⟩,
  ⟨0x5050a0a,⟨1,by decide⟩,0x4000a08,decodeBank 3 0x310c02f,3,decodeHints 0xbd2008000020ac00800002⟩,
  ⟨0xc0c0303,⟨0,by decide⟩,0xc080200,decodeBank 3 0x360d032,3,decodeHints 0xbd403c000290461342c829⟩,
  ⟨0x44441111,⟨0,by decide⟩,0x44401000,decodeBank 3 0x4510c42,3,decodeHints 0xbd602c0601b0681482c81b⟩,
  ⟨0xf0000000f,⟨0,by decide⟩,0xe00000008,decodeBank 3 0x731c871,3,decodeHints 0xbd80140101e0060480701e⟩,
  ⟨0x5500550000,⟨16,by decide⟩,0x4400500000,decodeBank 3 0x7b1e877,2,decodeHints 0xbda0600981305432009813⟩,
  ⟨0x5a0000005a,⟨1,by decide⟩,0x4a00000008,decodeBank 3 0x7c1e478,3,decodeHints 0xbdc0081f80200600801802⟩,
  ⟨0xf00000000f,⟨0,by decide⟩,0xe000000008,decodeBank 3 0x831fc7d,3,decodeHints 0xbde0140101e04a1402981e⟩,
  ⟨0x111100002222,⟨1,by decide⟩,0x100000002220,decodeBank 3 0x9625494,3,decodeHints 0xbe0010000040c001000004⟩,
  ⟨0x303000000303,⟨0,by decide⟩,0x302000000200,decodeBank 3 0x9b26497,3,decodeHints 0xbe203c0002904a1402f029⟩,
  ⟨0x505000000505,⟨0,by decide⟩,0x504000000400,decodeBank 3 0xa929ca3,3,decodeHints 0xbe40280301906614c2f019⟩
]

def viewsBlock1 : Array View := #[
  ⟨0x5000a0005000a,⟨1,by decide⟩,0x4000a00000008,decodeBank 3 0xd9360d7,3,decodeHints 0xbe60082b00200600801802⟩,
  ⟨0x11001100220022,⟨1,by decide⟩,0x10000000220020,decodeBank 3 0xea3a0e7,3,decodeHints 0xbe8010008040c001000804⟩,
  ⟨0xc00030000c0003,⟨0,by decide⟩,0xc0002000080000,decodeBank 3 0x11945d0f,3,decodeHints 0xbea0c41184d04a1405284d⟩,
  ⟨0x4040101004040101,⟨0,by decide⟩,0x4040100004000000,decodeBank 3 0x17d5ed7a,3,decodeHints 0xbec0741c85907617852859⟩,
  ⟨0xffff,⟨0,by decide⟩,0xfea8,decodeBank 4 0x50120400f,4,decodeHints 0xb80140101e00807c0101e0000a40c81e03607c0c81e⟩,
  ⟨0xff00ff,⟨0,by decide⟩,0xfa00a8,decodeBank 4 0xac280901d,4,decodeHints 0x7e80140101e00807c0101e0020440101e01a07c0681e⟩,
  ⟨0xf0f0f0f,⟨0,by decide⟩,0xe0a0e08,decodeBank 4 0xf43c0e833,4,decodeHints 0xb80140101e0000a40c81e0020440101e0000a40c81e⟩,
  ⟨0x33333333,⟨0,by decide⟩,0x32323220,decodeBank 4 0x104400fc3e,4,decodeHints 0xc20240201f0000a40d81f0020440681f0000a40d81f⟩,
  ⟨0x5555aaaa,⟨1,by decide⟩,0x5450aaa8,decodeBank 4 0x1384d1304a,4,decodeHints 0x7ea00802002000008020020ac0080200200000802002⟩,
  ⟨0x66666666,⟨1,by decide⟩,0x66626620,decodeBank 4 0x1445013c49,4,decodeHints 0x7ec11c02004000000020040020040200400000002004⟩,
  ⟨0xcccc3333,⟨0,by decide⟩,0xccc83220,decodeBank 4 0x1705815852,6,decodeHints 0xbee0240201f0000a40d81f0461342901f0b20a40d81f⟩,
  ⟨0xf0f00f0f,⟨0,by decide⟩,0xf0f00e08,decodeBank 4 0x1a86915453,4,decodeHints 0xb80140101e0000a40c81e01a0340681e01a0a40c81e⟩,
  ⟨0xff000000ff,⟨0,by decide⟩,0xee000000a8,decodeBank 4 0x230872007e,4,decodeHints 0x7ee0140101e00807c0101e0060480701e00807c0701e⟩,
  ⟨0xf0f00000f0f,⟨0,by decide⟩,0xe0e00000e08,decodeBank 4 0x24c9224490,4,decodeHints 0xb80140101e0000a40c81e0060480701e0000a40c81e⟩,
  ⟨0x333300003333,⟨0,by decide⟩,0x322200003220,decodeBank 4 0x288a127c98,4,decodeHints 0xc20240201f0000a40d81f0060480201f0000a40d81f⟩,
  ⟨0x55550000aaaa,⟨1,by decide⟩,0x54440000aaa8,decodeBank 4 0x2c8b02b8a4,4,decodeHints 0x7f000802002000008020020c00080200200000802002⟩
]

def viewsBlock2 : Array View := #[
  ⟨0x555555550000,⟨16,by decide⟩,0x544454500000,decodeBank 4 0x2c8b12bca5,4,decodeHints 0xbf00b00981303a470098130543200981303a47009813⟩,
  ⟨0x5a5a00005a5a,⟨1,by decide⟩,0x5a4a00005a08,decodeBank 4 0x2d0b32b4a6,4,decodeHints 0x7f20081f802000008000020060080180200000800002⟩,
  ⟨0xf0f000000f0f,⟨0,by decide⟩,0xf0e000000e08,decodeBank 4 0x304bd2e4b6,6,decodeHints 0xbf20140101e0000a40c81e04a1402981e0bc0a40c81e⟩,
  ⟨0xf000f000f000f,⟨0,by decide⟩,0xe000e000a0008,decodeBank 4 0x38cde370db,4,decodeHints 0x7ee0140101e0020440101e0060480701e0020440701e⟩,
  ⟨0x33003300330033,⟨0,by decide⟩,0x32002200320020,decodeBank 4 0x3c4ee3b0eb,4,decodeHints 0x7e80240201f0020440681f0060480201f0020440681f⟩,
  ⟨0x55005500aa00aa,⟨1,by decide⟩,0x54004400aa00a8,decodeBank 4 0x40d003f0f8,4,decodeHints 0xbf400802002002008020020c00080200200200802002⟩,
  ⟨0x5500aa005500aa,⟨1,by decide⟩,0x5400aa005000a8,decodeBank 4 0x41cff3f4f9,4,decodeHints 0xbf6008020020ac008020020060080200200600802002⟩,
  ⟨0x5a005a005a005a,⟨1,by decide⟩,0x5a004a005a0008,decodeBank 4 0x42d0a3ecfa,4,decodeHints 0x7f20081f802002008008020060080180200200800802⟩,
  ⟨0x66006600660066,⟨1,by decide⟩,0x66006600620020,decodeBank 4 0x4390d430f7,4,decodeHints 0x7ec11c020040020040200400600c0200400200402004⟩,
  ⟨0x5050a0a05050a0a,⟨1,by decide⟩,0x4040a0a04000a08,decodeBank 4 0x5414f5394d,4,decodeHints 0x7ea008000020ac008000020060080000200600800002⟩,
  ⟨0xc0c03030c0c0303,⟨0,by decide⟩,0xc0c02020c080200,decodeBank 4 0x55d5655551,4,decodeHints 0x9603c000290461342c829006048000290d81342c829⟩,
  ⟨0x1111111122222222,⟨1,by decide⟩,0x1010100022222220,decodeBank 4 0x5996559163,4,decodeHints 0x7f001000004002010000040c00100000400201000004⟩,
  ⟨0x3030303003030303,⟨0,by decide⟩,0x3030302002020200,decodeBank 4 0x5b96d5b167,4,decodeHints 0xa203c000290020440002904a1402f0290da0442f029⟩,
  ⟨0x4444111144441111,⟨0,by decide⟩,0x4444100044401000,decodeBank 4 0x6158460d81,4,decodeHints 0x15402c0601b0681482c81b04202c0601b0d81482c81b⟩,
  ⟨0x5050505005050505,⟨0,by decide⟩,0x5050504004000400,decodeBank 4 0x63d8e63582,4,decodeHints 0x1560280301904c0280301906614c2f0190da14c2f019⟩,
  ⟨0xc0c030300c0c0303,⟨0,by decide⟩,0xc0c030200c080200,decodeBank 4 0x705bc6e9a7,6,decodeHints 0xbf803c000290461342c82904a1402f02914a1342c829⟩
]

def viewsBlock3 : Array View := #[
  ⟨0xffffffff0000,⟨16,by decide⟩,0xfeeefefa0000,decodeBank 5 0xd2344cb2e8b8,5,decodeHints 0x6c05c1601702605c0981703a05c8e01702605c0981705405c6401702605c0981703a05c8e01702605c09817⟩,
  ⟨0xff00ff00ff00ff,⟨0,by decide⟩,0xfe00ee00fa00a8,decodeBank 5 0x13d4c52647516,7,decodeHints 0xbfa0140101e00807c0101e0020440101e01a07c0681e0060480701e00807c0701e0020440701e01a07c0681e⟩,
  ⟨0xf0f0f0f0f0f0f0f,⟨0,by decide⟩,0xe0e0e0e0e0a0e08,decodeBank 5 0x1605755c56152,5,decodeHints 0x780140101e0000a40c81e0020440101e0000a40c81e0060480701e0000a40c81e0020440701e0000a40c81e⟩,
  ⟨0x3333333333333333,⟨0,by decide⟩,0x3232322232323220,decodeBank 5 0x1775d1735bd68,5,decodeHints 0x820240201f0000a40d81f0020440681f0000a40d81f0060480201f0000a40d81f0020440681f0000a40d81f⟩,
  ⟨0x55555555aaaaaaaa,⟨1,by decide⟩,0x54545444aaaaaaa8,decodeBank 5 0x19a6619564987,5,decodeHints 0x18c008020020000080200200200802002000008020020c000802002000008020020020080200200000802002⟩,
  ⟨0x5555aaaa5555aaaa,⟨1,by decide⟩,0x5454aaaa5450aaa8,decodeBank 5 0x19c65d9664d89,5,decodeHints 0x1a000802002000008020020ac008020020000080200200600802002000008020020060080200200000802002⟩,
  ⟨0x5a5a5a5a5a5a5a5a,⟨1,by decide⟩,0x5a5a5a4a5a5a5a08,decodeBank 5 0x1a067d9e6418a,5,decodeHints 0x1060081f80200000800002002008008020000080000200600801802000008000020020080080200000800002⟩,
  ⟨0x6666666666666666,⟨1,by decide⟩,0x6666666666626620,decodeBank 5 0x1a468da268586,5,decodeHints 0xd011c0200400000002004002004020040000000200400600c02004000000020040020040200400000002004⟩,
  ⟨0xcccc3333cccc3333,⟨0,by decide⟩,0xcccc3222ccc83220,decodeBank 5 0x1d3749cf721a8,7,decodeHints 0x480240201f0000a40d81f0461342901f0b20a40d81f0060480201f0000a40d81f0d81342901f0b20a40d81f⟩,
  ⟨0xcccccccc33333333,⟨0,by decide⟩,0xcccccccc32323220,decodeBank 5 0x1d4745d0729a9,5,decodeHints 0x820240201f0000a40d81f0020440681f0000a40d81f01c0380701f01c0a40d81f01c0440681f01c0a40d81f⟩,
  ⟨0xf0f00f0ff0f00f0f,⟨0,by decide⟩,0xf0f00e0ef0f00e08,decodeBank 5 0x1f17bdec6f5ac,5,decodeHints 0xbfc0140101e0000a40c81e01a0340681e01a0a40c81e0060480701e0000a40c81e01a0340681e01a0a40c81e⟩,
  ⟨0xf0f0f0f00f0f0f0f,⟨0,by decide⟩,0xf0f0f0e00e0a0e08,decodeBank 5 0x1f27b9ed725ad,7,decodeHints 0x600140101e0000a40c81e0020440101e0000a40c81e04a1402981e0bc0a40c81e0da0442981e0bc0a40c81e⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xfefefeeefefafea8,decodeBank 6 0x8aa17825f3755b3,9,decodeHints 0xbfe0140101e00807c0101e0000a40c81e03607c0c81e0020440101e01a07c0681e0000a40c81e03607c0c81e0060480701e00807c0701e0000a40c81e03607c0c81e0020440701e01a07c0681e0000a40c81e03607c0c81e⟩
]

def viewsGet (i : Nat) : Option View :=
  if i < 32 then
    if i < 16 then
      viewsBlock0[(i-0)]?
    else
      viewsBlock1[(i-16)]?
  else
    if i < 48 then
      viewsBlock2[(i-32)]?
    else
      viewsBlock3[(i-48)]?

def nodesBlock0 : Array Node := #[
  ⟨0,2,decodeBank 2 0x1d474,decodeHints 0x5e1c0178760540a83b0700e00bc1502f⟩,
  ⟨1,3,decodeBank 3 0x400801,decodeHints 0x40180c80a0000640500600c0080000200a0001480f00c0a4078000000140300501e0080f0050140780280200403c0500f⟩,
  ⟨2,3,decodeBank 3 0xb02408,decodeHints 0x80300d80b00006c0580c018010000040120001480f0180a4078000000240600901e0100f80901607c0480400803c0580f⟩,
  ⟨3,3,decodeBank 3 0x1805c16,decodeHints 0x8020068130020340980801001000804012004088170100440b8010020240400902e0100f80902607c0480400805c09817⟩,
  ⟨4,3,decodeBank 3 0x1b06819,decodeHints 0x8054020100020040801502a0100080408e054238630020043181515211c008010c604031847008010238100ee18c02004⟩,
  ⟨5,3,decodeBank 3 0x200781c,decodeHints 0x80d029010046148080340680101180401208c26831068134188230460241a0090620100f80902007c048040080c408031⟩,
  ⟨6,3,decodeBank 3 0x310c02f,decodeHints 0x3d40001d0ac1580e8f54ec0002b0000041580102c1ea3d4160561740087a8020040740102c0000001601d03a00800002⟩,
  ⟨7,3,decodeBank 3 0x360d032,decodeHints 0xe42c81d0461640e8390720001180001e08c268310721341882304603c1c80f0620001480f03a0a4078000000c40e831⟩,
  ⟨8,3,decodeBank 3 0x4510c42,decodeHints 0x180e42c81d0681640e8390720301a00c0160d0290100721480803406802c1c80b0200300d80b03a06c0580c0180400e810⟩,
  ⟨9,3,decodeBank 3 0x731c871,decodeHints 0x401c070180060380c00700e0080180200a00c0901c00e0480e003006014038050380080f005030078028020040700c01c⟩,
  ⟨11,3,decodeBank 3 0x7c1e478,decodeHints 0x7e0581f86e00600c3701618e0fc018030040580101400600c0a01602c008018020040fc010140dc1b80a03f0ae00837002⟩,
  ⟨12,3,decodeBank 3 0x831fc7d,decodeHints 0x40cc2981404a14c0a0330660081280200a094280370661401b82504a0141980506e0080f005028078028020040dc0a037⟩,
  ⟨13,3,decodeBank 3 0x9625494,decodeHints 0x3e8000220c0180110fa7f400030000008180020321f43e8190601a20107d004008088020320000001902204401000004⟩,
  ⟨14,3,decodeBank 3 0x9b26497,decodeHints 0xec2f02204a1781103b0760001280001e094280370761401b82504a03c1d80f06e0001480f0440a4078000000dc11037⟩,
  ⟨15,3,decodeBank 3 0xa929ca3,decodeHints 0xc0ec2f0220661781103b076018198060140cc2981407614c0a0330660281d80a0280180c80a0440640500600c05011014⟩,
  ⟨16,3,decodeBank 3 0xd9360d7,decodeHints 0xac0842b0eb00600c75821224158018030040840104900600c2482104200801802004158010491d63ac2485617400875802⟩
]

def nodesBlock1 : Array Node := #[
  ⟨17,3,decodeBank 3 0xea3a0e7,decodeHints 0x22ec008260c0180130bb1a8004300010081800204a1762ec250601a20105d8040080980204a0020042502604c01000804⟩,
  ⟨18,3,decodeBank 3 0x11945d0f,decodeHints 0x4617c5287304a2943985f0be08c12823062094280370be1401b82504a0c42f83106e08c268310e6134188230460dc39837⟩,
  ⟨19,3,decodeBank 3 0x17d5ed7a,decodeHints 0x7217c528730762943985f0be0e41d83903a0ec2f0220be1781103b0760742f81d0440e42c81d0e61640e83907208839822⟩,
  ⟨26,3,decodeBank 4 0x1705a16457,decodeHints 0x808c1a0040460d0118090080240204b046fec118a700829c0207801229c04878⟩,
  ⟨26,4,decodeBank 5 0x5c1645815c56,decodeHints 0x460d01180900008c1c8000180001183904603c0480f0121e00000f0001e0020230680100480400812c020003d001005804⟩,
  ⟨26,3,decodeBank 4 0x1785d16057,decodeHints 0x80240204b000010060040180000000900802c0206101203c048610007a4001ad⟩,
  ⟨26,4,decodeBank 5 0x5d1705815c56,decodeHints 0x6808c060000000240002303a0000480f012184118310461840001d0000c40480400812c020233d40100200001801005804⟩,
  ⟨26,4,decodeBank 5 0x5c1685815c52,decodeHints 0x808c1a00401808c1c8230000101183904602c0200b0081e00600b0181e011834046024020090082a8049573d002407809⟩,
  ⟨26,4,decodeBank 5 0x5e1705815c52,decodeHints 0x46010000040180100003403a0000200b0081841a0100681840001d000040020090082a8049583d40240000c00002407809⟩,
  ⟨26,3,decodeBank 4 0x160561480e,decodeHints 0xa41640605209a1640004d09a1480204d00016400059008148020520121341184d⟩,
  ⟨26,4,decodeBank 5 0x5c16c5815852,decodeHints 0x11bfc046184000230720000e80000808c1a004020010020000180101183404602418809000030000090080240200f⟩,
  ⟨26,4,decodeBank 5 0x5c160561481f,decodeHints 0x2c85907208c020230680100d81b016010118340460241482901e0240200900803c118390460e40000000802c0200b01203c0480f⟩,
  ⟨26,3,decodeBank 4 0x1705614823,decodeHints 0x361641a01b0521641182905206c020290001641185900806c0201b0120a400029⟩,
  ⟨26,4,decodeBank 5 0x5f1705815852,decodeHints 0x1c8237fa0000007800008c0e8000160100202306801002000018010078090460d0118090000300000900802402031⟩,
  ⟨26,4,decodeBank 5 0x5c160561480a,decodeHints 0x2c85907200029052020010020000180102684d0620240000c000024020090080c4118230000740001d00802c0201001203c04831⟩,
  ⟨26,5,decodeBank 5 0x5c1605715852,decodeHints 0x721640e8230b20741c83900008c0006104608dff8390727b0118230c20e41c878000001ff01d03a7ac000000f00740e804068010258230469e81a03400808c02004018010258000009e40600c008000020aa09602c02061008024118231540d01a27804608c0483401202400000154030062770000000480c01212c2580f0121840484b008010048aa01212c2584b⟩
]

def nodesBlock2 : Array Node := #[
  ⟨26,3,decodeBank 4 0x1805d16456,decodeHints 0xd0000780000300006101202407861008000058040160100200f3d20100211b⟩,
  ⟨26,4,decodeBank 5 0x5d1705916056,decodeHints 0x6808c0480901e18411831046184078000001e0000233da000060000160100200f00808c080040200100203100800005804⟩,
  ⟨26,4,decodeBank 5 0x5c1685915852,decodeHints 0x8c1a0000460d01180c0000300004b06808c1a0230080100600b01812c118340460d00000f0002a80480914e29cf400f⟩,
  ⟨26,4,decodeBank 5 0x5c1605614835,decodeHints 0x230720002905206808c0d81b018000118340460240000c0000240f81f01203c118340460d00000c0000300200401e02407809⟩,
  ⟨26,4,decodeBank 5 0x601705915852,decodeHints 0x460000000c0001841c81d0721840200001601002039020010080040080400000f0002a807a7b3da03c0480900802c0200f⟩,
  ⟨26,3,decodeBank 4 0x1705814839,decodeHints 0x361481c81b03e1481181f03e06c0001f0081481185200806c0001b01e07c0201f⟩,
  ⟨26,4,decodeBank 5 0x611705815852,decodeHints 0x1a023018000000230720020000400812c0202302001002000016010048090460e41180f00003c0003100802c0200f⟩,
  ⟨26,4,decodeBank 5 0x5c160561480c,decodeHints 0x2c85903a00029052068010020000160102684d0620d00000f0000c40200b00803c118230000300001d0080400201001202407831⟩,
  ⟨26,5,decodeBank 5 0x5c1645815852,decodeHints 0x6104608e010340687b8118230c20d01a0000720003c0230469f81c83900008c000aa0f0030000610000101a05202008c290100680d0020230080420081000812c020043d60100804b0200103c0040160000000b4fa02c0200000803c118231540d01a27c04608c078340681e03c00901e18404878000000078aa01e1e03c07801e010020aa01602d3b80400803c0580f⟩,
  ⟨26,4,decodeBank 5 0x5e1745815852,decodeHints 0x460d01184b00008c060000180000000c0080101a01006812c06000018000118310462a8048090000300000c35a6b4f5031⟩,
  ⟨26,4,decodeBank 5 0x5c1605614837,decodeHints 0x2303a0002905206808c0d81b018000118340460240000c0000240f81f01202c118340460d00000c0000300200401e02418809⟩,
  ⟨26,4,decodeBank 5 0x601745815852,decodeHints 0x460d0118780000001c81d0721e0020230160100580400802c0200b016010118310462a80480923646cf683100802c0200b⟩,
  ⟨26,4,decodeBank 5 0x5c1605614821,decodeHints 0x2c85907208c020230200100d81b0180101183904603c1482901e0300200b00803c118340460e40000000802c0200b0120241880f⟩,
  ⟨26,5,decodeBank 5 0x5d1705815852,decodeHints 0xaa0c20d0118610460320200c0001e0000003dc000060780180003080003a08c1181d5000740002300002e0180b00812c020043d80100584b0160103080402008c118104fe040020230080100601b0160000d80b01803002000008184308090621840486104608c188aa06218430861062000000aa0180313e0000000c40600c062010020aa01602d3c0040080c40580b⟩,
  ⟨26,4,decodeBank 5 0x5c1605614844,decodeHints 0x2307200002023068010020000180102684d0460d0148290000300f81f00802c1a02306808c060000180000580401601004809⟩,
  ⟨26,3,decodeBank 4 0x1805e16852,decodeHints 0x4608c0607800000006061008010058610120300780901e0240480f3d2024049ef⟩
]

def nodesBlock3 : Array Node := #[
  ⟨26,4,decodeBank 5 0x5e1705a16052,decodeHints 0x4608c020040161841a0100681840580c0181e0060343e00300000001e0240480f0120d0188090620240483101203007809⟩,
  ⟨26,4,decodeBank 5 0x601705a15852,decodeHints 0x4608c000000181841c81d0721840600b01812c05c053e002c02004012030078090120e4188090620240483101e0240480f⟩,
  ⟨26,3,decodeBank 4 0x1705815848,decodeHints 0x521341c82903e1341a01f03e0a40601f0121341a04d0120a40602901e07c0481f⟩,
  ⟨26,4,decodeBank 5 0x621705815852,decodeHints 0x1182300000006034072030020040680e41a00b01802c0601080c024048aa0120d0188090120300780901e0240480f⟩,
  ⟨26,4,decodeBank 5 0x5c160561480d,decodeHints 0x2c85903a08c2905202008c0600b0180402684d0460240480c01e0240780901203c1a0230000000601d008010058100120c404831⟩,
  ⟨26,5,decodeBank 5 0x5c1685815852,decodeHints 0x610680d2040230467c41a0340c208c1180c0720303c023046a081c83901808c1184b0f00000606100002c1a03409608c11a810680d0058230461e03c004016184020780180300584b0161e03c07801208c26831068134188230460241a00906301c18809154024049eb0120c4550310121e00480f01803007a7d01e0240600901e12c0780901602404a7901203c0580f⟩,
  ⟨26,4,decodeBank 5 0x5c1605614846,decodeHints 0x2303a00002023068010020000180102684d0460d0148290000300f81f00803c1a02306808c060000180000580402001004809⟩,
  ⟨26,4,decodeBank 5 0x601785815852,decodeHints 0x4608c1a0780000001c81d0721e01a01006812c020043de7bcf80100120d00780901e0240480f01203c0780901e0240480f⟩,
  ⟨26,4,decodeBank 5 0x5c1605614822,decodeHints 0x2c8590720001a03906802c0d81b01600004834062024148290000240780901203c118230680e4060000080100800b01203c0480f⟩,
  ⟨26,5,decodeBank 5 0x5e1705815852,decodeHints 0x4b0c208c1a061046002050000181e00600c3e2030000780000003080003a0d01a01d5060740003400018430804020184020610680d00804b020184308610200300604b0000014080c0180400000001f02407809154024049ec01203c5500f012184048310680d018a7f0620241a0090120001480f0180a4078000000240600901e12c0780902002404a7a01203c0800f⟩,
  ⟨26,4,decodeBank 5 0x5c1605614847,decodeHints 0x2307200002023020010020000160102684d046024148290000240f81f00802c1a02307208c0600003a0000580401601007809⟩,
  ⟨26,4,decodeBank 5 0x5c1605614838,decodeHints 0x6034072030290520680100d81b018010048340620240480c01e0240f81f00803c118230720d00000003a0300580401e02407809⟩,
  ⟨26,5,decodeBank 5 0x601705815852,decodeHints 0x780c208c1c8610461843080003a184000610720e40e87803a184308610090300200b09602c059f101601025804008184020100720e4082830200101c8040081e00200b03a02c05a820160100e80401302c0480f15403c079ee01e02455009012184048310720e418a800620241c8090121e00480f03a03c07a7e01e0240e80901e0100f80901607c0480400803c0580f⟩,
  ⟨26,6,decodeBank 4 0x1705815852,decodeHints 0xc20001c8590f0074118598240741c8390c2000118000c20101a052096040118528220401a0340c2010118040f00100601b09602c0001b82002c0600c0f0010000040c20241184d1540c41a04d81e0c4118230c20241a0090f00240002915403c0602981c03c000000f00240600909603c0201f1540240581f81a0240200409603c0580f⟩,
  ⟨32,4,decodeBank 4 0x2c8b12bca5,decodeHints 0x3aa100e8220540a8112848280741501d0261c0098320540a81907022604c15013026088098ae03a7c85702282604c0e8130580a8640180e03200c02a0540b03802c0300748e02c0444701601d03a060110180580404081402604c0a01005e0b009813⟩,
  ⟨34,3,decodeBank 4 0x304bf2f8bb,decodeHints 0x40941980204a0cc128050040140105104b054128a80042a00107900a2a002879⟩
]

def nodesBlock4 : Array Node := #[
  ⟨34,4,decodeBank 5 0xc12f8bd2ecb9,decodeHints 0x4a0cc128050000941d80000c0001283b04a03c0280f00a1e40000f0001e40102506600802802004144010003e600805002⟩,
  ⟨34,3,decodeBank 4 0x30cc22f4bb,decodeHints 0x4014010510000080300200c000000050040280105c00a03c0285c0007d4001f4⟩,
  ⟨34,4,decodeBank 5 0xc2304bd2ecb9,decodeHints 0x6609403000000014000250440000280f00a1701283704a170000220000dc02802004144010253ec0080100000c00805002⟩,
  ⟨34,4,decodeBank 5 0xc12fcbd2ecb6,decodeHints 0x40941980200c0941d8250000081283b04a0280100a0041e40300a00c1e41283304a014010050042ac0291d3e601407805⟩,
  ⟨34,4,decodeBank 5 0xc3304bd2ecb6,decodeHints 0x4a0080000200c008000330440000100a0041701981406617000022000050010050042ac029ae3ec0140000600001407805⟩,
  ⟨34,3,decodeBank 4 0x2f4b92d807,decodeHints 0xa6178030530a0178000500a014c010500001780005e00414c0105300a14012850⟩,
  ⟨34,4,decodeBank 5 0xc1300bd2e4b6,decodeHints 0x12c1604a1700002507600011000004094198020280080100000c0081283304a0141b805000018000050040140100f⟩,
  ⟨34,4,decodeBank 5 0xc12f4b92d881,decodeHints 0x2f05e076094010250660080c8190140081283304a0141482901e0140100500403c1283b04a0ec000000040280100a00a03c0280f⟩,
  ⟨34,3,decodeBank 4 0x304b92d886,decodeHints 0x321781981905217812829052064010290001781285e0040640101900a0a400029⟩,
  ⟨34,4,decodeBank 5 0xc4304bd2e4b6,decodeHints 0x1d82582e0000007900009411000014008010250660080100000c0080780504a0cc128050000180000500401401037⟩,
  ⟨34,4,decodeBank 5 0xc12f4b92d803,decodeHints 0x2f05e076000298530280080100000c0082805006e01400006000014010050040dc12825000088000220040280101400a03c02837⟩,
  ⟨34,5,decodeBank 5 0xc12f4bb2e4b6,decodeHints 0x76178110250bc0881d83b0000940005c04a0960c83b0767e0128250b80ec1d8790000020c0220447dc000000f2088110020660082882504aa20198330040940100200c00828800000a1c03006004000010ab0a20280105c004014128251560cc19a8604a0940283300a01400000156018032850000000280600a1442880f00a17002851004008028ab00a14428851⟩,
  ⟨34,3,decodeBank 4 0x314c22f8b9,decodeHints 0xcc000790000180005c00a0140785c004000050020140080100f3ea00801159⟩,
  ⟨34,4,decodeBank 5 0xc2304be2f4b9,decodeHints 0x660940280501e1701283704a170078000001e4000253f2000030000140080100f0040940a0020280080103700400005002⟩,
  ⟨34,4,decodeBank 5 0xc12fcbe2e4b6,decodeHints 0x941980004a0cc1280600001800051066094198250040080300a00c1441283304a0cc0000f0002ac028051502a0f980f⟩,
  ⟨34,4,decodeBank 5 0xc12f4b92d89a,decodeHints 0x25076000298530660940c81900c0001283304a014000060000140f01e00a03c1283304a0cc000060000180100201e01407805⟩
]

def nodesBlock5 : Array Node := #[
  ⟨34,4,decodeBank 5 0xc5304be2e4b6,decodeHints 0x4a000000060001701d822076170010000140080103b0280080a0020040500000f0002ac07a893f203c028050040280100f⟩,
  ⟨34,3,decodeBank 4 0x304bd2d89e,decodeHints 0x3214c1d81903c14c1281e03c0640001e00414c128530040640001901e0780101e⟩,
  ⟨34,4,decodeBank 5 0xc6304bd2e4b6,decodeHints 0x1982500c000000250760020d00200414401025028008010000140080280504a0ec1280f00003c000370040280100f⟩,
  ⟨34,4,decodeBank 5 0xc12f4b92d805,decodeHints 0x2f05e04400029853066008010000140082805006e0cc0000f0000dc0100a00403c12825000018000220040500101400a01407837⟩,
  ⟨34,5,decodeBank 5 0xc12f8bd2e4b6,decodeHints 0x5c04a0960e0330667e8128250b80cc198000760003c82504aa301d83b000094000ab0f20180005c00000819853028094298140660cc010250040520d814004144010023ee0080a0510280083c8020140000000a5160280100000403c128251560cc19a8a04a094078330661e43c80501e17002879000000078ab01e1e43c87901e008010ab0140294280200403c0500f⟩,
  ⟨34,4,decodeBank 5 0xc3308bd2e4b6,decodeHints 0x4a0cc128510000940300000c00000006004008198140661440300000c0001283704a2ac02805000018000063e87d0fb037⟩,
  ⟨34,4,decodeBank 5 0xc12f4b92d89c,decodeHints 0x25044000298530660940c81900c0001283304a014000060000140f01e00a0281283304a0cc000060000180100201e0141b805⟩,
  ⟨34,4,decodeBank 5 0xc5308bd2e4b6,decodeHints 0x4a0cc128790000001d8220761e401025014008050020040280100a0140081283704a2ac028052b2564fc8370040280100a⟩,
  ⟨34,4,decodeBank 5 0xc12f4b92d884,decodeHints 0x2f05e076094010250280080c81900c0081283b04a03c1482901e0180100a00403c1283304a0ec000000040280100a00a0141b80f⟩,
  ⟨34,5,decodeBank 5 0xc2304bd2e4b6,decodeHints 0xab0b80cc1285c04a01a0f0060001e4000003f40000307900c0002e0000440941282251c0880002500002a0e80a004144010023f0008050510140082e0020280941281451a05001025004008030190140000c80a00c018010000041702e00506e1700285c04a0941b8ab06e1702e05c06e000000ab00c019450000000dc0300606e008010ab014029430020040dc0500a⟩,
  ⟨34,4,decodeBank 5 0xc12f4b92d8a8,decodeHints 0x25076000010250660080100000c0082805004a0cc148290000180f01e004028198250660940300000c0000500201400802805⟩,
  ⟨34,3,decodeBank 4 0x314c32fcb6,decodeHints 0x4a094030790000000305c0040080505c00a0180780501e0140280f3ea014029fb⟩,
  ⟨34,4,decodeBank 5 0xc3304bf2f4b6,decodeHints 0x4a09401002014170198140661700500600c1e4030333f80180000001e0140280f00a0cc1b80506e0140283700a01807805⟩,
  ⟨34,4,decodeBank 5 0xc5304bf2e4b6,decodeHints 0x4a0940000000c1701d8220761700300a00c1440541f3f80280100200a0180780500a0ec1b80506e0140283701e0140280f⟩,
  ⟨34,3,decodeBank 4 0x304bd2e4ac,decodeHints 0x521401d82903c1401981e03c0a40301e00a1401985000a0a40302901e0780281e⟩,
  ⟨34,4,decodeBank 5 0xc7304bd2e4b6,decodeHints 0x1282500000003033076018010020660ec1980a00c02803014840014028ab00a0cc1b80500a0180780501e0140280f⟩
]

def nodesBlock6 : Array Node := #[
  ⟨34,4,decodeBank 5 0xc12f4b92d806,decodeHints 0x2f05e044094298530280940300a00c0502805004a0140280601e0140780500a03c19825000000030220040080501400a0dc02837⟩,
  ⟨34,5,decodeBank 5 0xc12fcbd2e4b6,decodeHints 0x5c0660ce1102504a7f4198330b8094128060760183c82504aa401d83b00c094128510f20000305c000028198330a209412a8f0660cc0502504a1e43c8020141700107900c018050510141e43c87900a094280370661401b82504a0141980506f0841b805156014029f700a0dc5583700a1e40280f00c01807a8b01e0140300501e1440780501401402a8700a03c0500f⟩,
  ⟨34,4,decodeBank 5 0xc12f4b92d8aa,decodeHints 0x25044000010250660080100000c0082805004a0cc148290000180f01e00403c198250660940300000c0000500202800802805⟩,
  ⟨34,4,decodeBank 5 0xc530cbd2e4b6,decodeHints 0x4a094198790000001d8220761e419814066144010023f67ecfe01400a0cc0780501e0140280f00a03c0780501e0140280f⟩,
  ⟨34,4,decodeBank 5 0xc12f4b92d885,decodeHints 0x2f05e0760001983b0660280c8190140000283306e014148290000140780500a03c128250660ec030000040080a00a00a03c0280f⟩,
  ⟨34,5,decodeBank 5 0xc3304bd2e4b6,decodeHints 0x510b80941985c04a0021200000c1e4030063fa018000790000002e0000440cc19822522088000330001702e0020281700105c0660cc0a0510281702e05c028018030510000014780600c0500000001f08c07805156014029f800a03c5580f00a170028370660cc1ba8d06e0141980500a0001480f00c0a4078000000140300501e1440780502801402a8800a03c0a00f⟩,
  ⟨34,4,decodeBank 5 0xc12f4b92d8ab,decodeHints 0x2507600001025028008010000140082805004a014148290000140f01e00402819825076094030000440000500201400807805⟩,
  ⟨34,4,decodeBank 5 0xc12f4b92d89d,decodeHints 0x3033076018298530660080c81900c0080283306e0140280601e0140f01e00403c128250760cc000000440180500201e01407805⟩,
  ⟨34,5,decodeBank 5 0xc5304bd2e4b6,decodeHints 0x790b80941d85c04a1702e0000441700005c0760ec110790441702e05c0050980100a0a2028051fd01400828802004170010140760ec0a2910280081d8020041e40100a044028052900140081100200b0940280f15603c079fa01e0145580500a170028370760ec1ba8e06e0141d80500a1e40280f04403c07a8c01e0141100501e0080f0050140780280200403c0500f⟩,
  ⟨34,6,decodeBank 4 0x304bd2e4b6,decodeHints 0xb80001d85e0f20881285e8580881d83b0b8000128000b8008198530a205012853856050198330b8008128020f2008030190a202800019854028030060f2008000020b8014128501560dc198508520dc128250b8014198050f20140002915603c0302985003c000000f2014030050a203c0101e1560140501e84e014010020a203c0500f⟩,
  ⟨47,3,decodeBank 4 0x705bf6f9bb,decodeHints 0x941d80004a0ec1280f00003c0008504b0b41291b00046c0005101e46c07851⟩,
  ⟨47,4,decodeBank 5 0x1c16f9bc6edba,decodeHints 0x4a0ec1280f0460942f82307208c1285f04a0c40783101e144118310461440002507600007800000214000233fc0000e800⟩,
  ⟨47,3,decodeBank 4 0x70dc26f1bb,decodeHints 0x3c000850460001c80007208c1180f0000740004b01e0c40784b0467fc11959⟩,
  ⟨47,4,decodeBank 5 0x1c2705bc6edba,decodeHints 0x760941c82304603c118250e608c0783101e12c1283704a12c118730460dc0780000021400025400000000230720000e800⟩,
  ⟨47,4,decodeBank 5 0x1c16fdbc6eda7,decodeHints 0x941d8000720942f8250460001285f04a0740001d0001441c81d0721441283b04a03c0000f0002b407a7b3fc03c1880f⟩,
  ⟨47,4,decodeBank 5 0x1c3705bc6eda7,decodeHints 0x4a000118000720001183b0e608c0001d00012c1d82207612c118730460880000f0002b407a8940003c1183904603c1880f⟩
]

def nodesBlock7 : Array Node := #[
  ⟨47,3,decodeBank 4 0x6f1ba69c39,decodeHints 0xbc2941c85e0a0294118500a017800050046294118a50001780005e01e14012850⟩,
  ⟨47,4,decodeBank 5 0x1c1701bc6e9a7,decodeHints 0x12c2e04a12c118250be08c398230000941d800044000000230720001283b04a03c1b80f0460e41180f00003c00031⟩,
  ⟨47,4,decodeBank 5 0x1c16f1ba69c9a,decodeHints 0x528a50be094000250760002c85903a0001283b04a03c2684d06203c0000f0000c41285f04a17c118230000740001d01e0c407831⟩,
  ⟨47,3,decodeBank 4 0x705ba69c9e,decodeHints 0xb22941d85909a2941284d09a1640004d046294128a50001640005901e1341184d⟩,
  ⟨47,4,decodeBank 5 0x1c4705bc6e9a7,decodeHints 0x2f82585e08c118510460943982303a00000025076000000230720001880f04a0ec1280f0460e41180f00003c00037⟩,
  ⟨47,4,decodeBank 5 0x1c16f1ba69c35,decodeHints 0x528a50be08c2f05e044000000230720002805006e03c1183904603c0000f0000dc128250461cc118730000740002201e0c407837⟩,
  ⟨47,5,decodeBank 5 0x1c16f1bb6e9a7,decodeHints 0x230be2943982514a1cc2f85f0460941184b04a0961885f0be8081282509617c2f85104608e180730e6804118230a21cc398000760004282504aa541d83b0000940000007200042823046a501c83900008c000ad10a0740004b00003c1282515a0ec1da9304a0940783b01e03c1182315a0e41ca9204608c0783901e2144283101e12c07885000000078ad01e21442885⟩,
  ⟨47,3,decodeBank 4 0x715c26f9ba,decodeHints 0x460ec118510460e41184b01e03c1884b00008c0e80003a000000313fe00000203⟩,
  ⟨47,4,decodeBank 5 0x1c2705be6f1ba,decodeHints 0x760940780f06212c1283704a12c188230461441182540808c1c82303a00000031000094110000440000003700008c0e800⟩,
  ⟨47,4,decodeBank 5 0x1c16fdbe6e9a7,decodeHints 0x460941d82304a0ec128390460e4118850760941d8250000001c81d0722141283b04a0ec118310462b40780f23646cff031⟩,
  ⟨47,4,decodeBank 5 0x1c16f1ba69d18,decodeHints 0x118250be08c2f05e0760942c85907208c1283b04a03c1183904603c1482901e0c41283b04a0ec118390460e40000006203c1880f⟩,
  ⟨47,4,decodeBank 5 0x1c5705be6e9a7,decodeHints 0x4a08c1183904612c2f8730be12c0002303a0000005f04400011000000088118310462b418c324080c40780f00007400031⟩,
  ⟨47,3,decodeBank 4 0x705bc69d1c,decodeHints 0xb21782f85905217812829052164118290001781285e000164118590620a400029⟩,
  ⟨47,4,decodeBank 5 0x1c6705bc6e9a7,decodeHints 0x1d82507208c118250be08e19800000214000250440000002303a0000780f04a17c128310460c41183700007400031⟩,
  ⟨47,4,decodeBank 5 0x1c16f1ba69c37,decodeHints 0x528a50e608c2f05e0760000002303a0002805006e0ec118310460dc0001d0000c4128250460e4118730000880002201e03c18837⟩,
  ⟨47,5,decodeBank 5 0x1c16f9bc6e9a7,decodeHints 0x4b04a0961a83b076814128250960ec1d8230be08c2882504aa602f85f046094118ad0a20e41184b0460001d85e0440942f0220760ec0002500008a1a02200021400000402000110850440002880003a08c1181d52e074000230000c41282515a0ec1da9604a0941883b0761442880f06212c0785104608c188ad06214428851062000000ad03a075490000000c40e831⟩
]

def nodesBlock8 : Array Node := #[
  ⟨47,4,decodeBank 5 0x1c3709bc6e9a7,decodeHints 0x4a0ec128850460941c82307208c118390000001d8220762141c82307208c1283704a2b40780f0460e4118392b256500037⟩,
  ⟨47,4,decodeBank 5 0x1c16f1ba69d1a,decodeHints 0x118250e608c2f05e0760942c85907208c1283b04a03c1183904603c1482901e0741283b04a0ec118390460e40000006203c1b80f⟩,
  ⟨47,4,decodeBank 5 0x1c5709bc6e9a7,decodeHints 0x4a0ec1285104608c2f8730be1440002503a0000e8000000740001d03a0001283704a2b40780f40680d020370000740001d⟩,
  ⟨47,4,decodeBank 5 0x1c16f1ba69c9c,decodeHints 0x528a50be094000250440002c8590720001285f04a0c42684d0620e40001d0000c41283b04a17c118230000740001d01e03c1b831⟩,
  ⟨47,5,decodeBank 5 0x1c2705bc6e9a7,decodeHints 0xad0960ec1284b04a0e61b8390461441182340a08c1c85107208c258230e6094128735341cc118250460761b01d000214000004040000e88503a0002580004409412822532088000250000001c85903a08c2c81d0720e40002300012c2580f06e12c0784b04a0941b8ad06e12c2584b06e08c118ad0720e54b0230460dc1c83906e000000ad03a075498000000dc0e81d⟩,
  ⟨47,4,decodeBank 5 0x1c16f1ba69d7c,decodeHints 0x118250be08c00025076000000230720002805004a0ec2684d0460e4148290000741d8250760941c82307208c0e80003a0000780f⟩,
  ⟨47,3,decodeBank 4 0x715c36fda7,decodeHints 0x4a0941c85104608c1c84b0000000e84b01e0e41880f06203c078313fe03c07a06⟩,
  ⟨47,4,decodeBank 5 0x1c3705bf6f1a7,decodeHints 0x4a0940000003a12c1d82207612c0e8390721441c83b40e0e41182306203c0783101e0ec1b80f06e03c0783701e0e41880f⟩,
  ⟨47,4,decodeBank 5 0x1c5705bf6e9a7,decodeHints 0x4a0941182307212c2f8730be12c1c81d0722140ec3840e0740000001e0e41880f01e17c1b80f06e03c0783706203c07831⟩,
  ⟨47,3,decodeBank 4 0x705bc6e980,decodeHints 0x9a1402f84d0521401d8290521341c82901e1401d85001e1341c84d0620a407829⟩,
  ⟨47,4,decodeBank 5 0x1c7705bc6e9a7,decodeHints 0x1282504608c1c83b0be0e40000007617c1d81d0720741c82287203c078ad01e0ec1b80f01e0e41880f06203c07831⟩,
  ⟨47,4,decodeBank 5 0x1c16f1ba69c38,decodeHints 0x528a50e60942f05e0440941c81d0720882805004a03c0783906203c1880f01e0c41d82504608c1c8730000000e82201e0dc07837⟩,
  ⟨47,5,decodeBank 5 0x1c16fdbc6e9a7,decodeHints 0x4b0760ee1d82504a8201d83b096094128390be0e42882504aa702f85f072094128850a208c1c84b0460741d83b10a09412a9b0760ec0e82504a1442880003a12c000510720e40e88503a1442885101e094280370761401b82504a03c1d80f06f0e81b80f15a03c07a0101e0dc5683701e144078310720e418a9706203c1c80f0622141880f03a03c07a9401e0c40e831⟩,
  ⟨47,4,decodeBank 5 0x1c16f1ba69d7e,decodeHints 0x118250e608c00025076000000230720002805004a0ec2684d0460e4148290000c41d8250760941c82307208c0e8000440000780f⟩,
  ⟨47,4,decodeBank 5 0x1c570dbc6e9a7,decodeHints 0x4a0941d85104608c2f8730be1441d8220762140000040c8190382201e0ec1880f06203c0783101e0c41880f06203c07831⟩,
  ⟨47,4,decodeBank 5 0x1c16f1ba69c9d,decodeHints 0x528a50be08c1d85f0760742c85903a08c0783b06e03c2684d04603c1880f01e0c41282507617c1c8230000001101d01e0c407831⟩
]

def nodesBlock9 : Array Node := #[
  ⟨47,5,decodeBank 5 0x1c3705bc6e9a7,decodeHints 0x850960941d84b04a08e1e8230721441c8394100e41185104608c258230e60ec1d87353a1cc1183b04612c2580004412c0004b0760ec1108504412c2584b0440e41c88504608d4d839072088118230630f01880f15a03c07a0201e0c45683101e12c078370760ec1ba9906e03c1d80f01e08c268310721341882304603c1c80f0622141880f04403c07a9501e0c411031⟩,
  ⟨47,4,decodeBank 5 0x1c16f1ba69d7f,decodeHints 0x118250be08c000250440000002303a0002805004a03c2684d04603c148290000741d8250be0941c8230e608c0e80003a0001880f⟩,
  ⟨47,4,decodeBank 5 0x1c16f1ba69d1b,decodeHints 0x1c83b0be0e42f05e0760002c8590720000783b06e03c0783906203c148290000c4128250be0ec118230e60e40e80006203c1880f⟩,
  ⟨47,5,decodeBank 5 0x1c5705bc6e9a7,decodeHints 0x510960942f84b04a12c258230e612c1184b0be17c398510e612c2584b0010fc0001d10a0740ea0803a0004280000012c000220be17c1129d0440002f8000001440001d0e60740ea9c03a0003980001f0f80783115a0c418a0506203c5680f01e12c078370be17c1ba9a06e03c2f80f01e144078310e60c418a9806203c3980f0620001480f03a0a4078000000c40e831⟩,
  ⟨47,6,decodeBank 4 0x705bc6e9a7,decodeHints 0x9608c2f8a50a21cc128a588a1cc2f85f09608c128230960001d85e10a0881285e8880881d83b096000128000a20001c85910a074118598860741c8390a20001180009603c1285015a0dc1d8508840dc1282509603c1d80f0a203c1184d15a0c41c84d8820c4118230a203c1c80f10a0c40002915a03c0e82988003c0000010a0c40e831⟩,
  ⟨49,4,decodeBank 5 0x1465153149925,decodeHints 0x4014010470020080a802070004008050080080800207c0100200501a034040040042c80106000a024028460020200080800804c02013⟩,
  ⟨49,5,decodeBank 6 0x5153d4c5264951d,decodeHints 0xe00c1c0010020140080304c0041f004008014020030940100680d0100100280900a1180181c006180008080020200201300804c0280200411c010034120080100102a008010040200080c002⟩,
  ⟨49,5,decodeBank 6 0x4f531499254741d,decodeHints 0x8070540040200705a0100680d0100100901200e118008080020200201300804c0120a1800080100102a008010040200080c00200600c008380020140203e0080140480500401401047⟩,
  ⟨49,5,decodeBank 6 0x4f5314bd2649516,decodeHints 0x200c1500100400c038020040040400206600c16803074004040010080080184800656800808002020010180041680801405e0bc01807006014008380020140100500418c0287707e01404805⟩,
  ⟨49,5,decodeBank 6 0x4f53a4c52649516,decodeHints 0x400c0380209c00c150030020080200305a010020020260080203a02a0100188000656c010180041540a84905c0b80201300804c018070060140100500411c028a90ac0140203e00801404805⟩,
  ⟨49,5,decodeBank 6 0x5193d4c52649516,decodeHints 0x60080080202a00800807054004020020200080200705a0100680d010010010180041180381800e118008080020200201300804c0100500411c028c0412014008380020140203e00801404805⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d458dd,decodeHints 0x8030540040b00302c00c0680d0100040100300e0080100105c0080101302800801807006014008380020140f81f012014010050040240181600605800808002020020040040600101400a02402809⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d45882,decodeHints 0x400304200c0200305a0100680d0100100100300e008010080920080100405e008018070060140881102e0140203e0080140100500411c018210060840080100804c020130040600104900a02402817⟩,
  ⟨49,5,decodeBank 5 0x1314991d45827,decodeHints 0x802006813002034098080100100080401c054070800021b04001502a0380080e01c0400704800814c240100ce0380200e024004090950101744a801002048040120240100906a02614035004008048098120240080900501c0380280200404807012006004008210100201080100200c04003006010020160260b40b00400800c098030060080100701c0380380200400c0700e00e014028030240480180500601c09012⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d45827,decodeHints 0x88c0e0004020c91d80100680d0100100700e0300080100102a0080100402000809012038014008380020140203e0080140100500411c018030020200080800804c020130040600101800a0240281c⟩,
  ⟨49,6,decodeBank 6 0x4f5314992547516,decodeHints 0x1042004130030060981082a00200c0080402c010250030061280b02d00800c020040100340980101a04c040080080040204600600e2495c8903640180308c57023055002006238080103b4008010aa0200405a008012230130263d8020040b404c0980200e00831003006a880380700400c0100202a00831001002a840a8150040040100202000831004008a80080100040100115c0c4060010460040140180353e01c03a9e00600c0280700a014008010620201c0310020040280800a0140200406a04c1f0350080100281300a1883100900a118028620040080295c00a18831047⟩
]

def nodesBlock10 : Array Node := #[
  ⟨49,4,decodeBank 5 0x13d4991d45889,decodeHints 0x1a1b40b00d01c038038030a40343280d022174018110220340201103c0780281100201c018010080340200d0020b80100201204400811⟩,
  ⟨49,5,decodeBank 6 0x4f5314a92647516,decodeHints 0x8030540040180700601c00c4a0021540200302c010020010100100980401c0380380306800417001030050010020cc0100a00400601c018050020e00080500a024048050080240200503c07802809⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d458d6,decodeHints 0x8030540041980305a00c0680d0100040700e00e00c1a00105c0044081305e04c01807006014008380020140f81f0120140f01e00a0240180700601c00808002020020040040080b805⟩,
  ⟨49,4,decodeBank 5 0x13d4c51d458e0,decodeHints 0x1a1b41080d01c038038030a40343280d03e1400181f03e0340081f03c0780281f00801c018040080340080d0080bc0100202e07c0201f⟩,
  ⟨49,5,decodeBank 6 0x4f5354c52647516,decodeHints 0x180700601c008030420040400100800c168048960100205a0080040980401c0380380303012401002046004248011020101780400601c0180500a0240b80500205c008050080f80200503c07802817⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d45876,decodeHints 0x2700305400c0200305a0100680d0100100700e00e00c1a00805c0204080405e010018070060140881102e0140203e0080140f01e00a05c0180700601c0080100804c0201300400804805⟩,
  ⟨49,5,decodeBank 6 0x5013d4c52647516,decodeHints 0x38030100040080800200c130010260100201300800c2500401a034040042ba0600100219400c0c003068004170011020101780400a0240e005006070018050020e0008050080f80200503c0780281c⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d45816,decodeHints 0x8070540040200705a0100680d0100100700e00e5741a00105c0044080405e01009012038014008380020140203e0080140f01e00a070018030020200080800804c0201300400804805⟩,
  ⟨49,5,decodeBank 6 0x5153d4c526474eb,decodeHints 0x38030700040080500200c1300107c0100200500800c2500401a0340400403c078028622ba00c5900306800417001102010178040120140181c006180008080020200201300804c01002⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d3ac1d,decodeHints 0x201c1500100801c1680401a0340400401c0380395d06800417001102010178040240480e0070020200080800804c02013004008018030020e0008050080f80200503c0780281800a02423005⟩,
  ⟨49,6,decodeBank 6 0x4f5314991d458eb,decodeHints 0x1042004130030060981082a00200c0080402c010250030061280b02d00800c020040100340980101a04c040080080040215d00e0380c00301c060038072ba00c0181802a0d0248010021240a82e030004008180202040a0040080500802f0300100200500600d5200700ea8c0180300a01c02805002004188080700c40080100a020028050080101a81307c0d40200400a04c028620c40780295c00a1880c01808c00c01a0d00e01e27003006118038070aa00400a0c01002226801002154040080b40100220b02604e26004008168098130c4570010460300083106201211802805⟩,
  ⟨49,4,decodeBank 5 0x13d4ed394b91d,decodeHints 0x800c0b00400601c018070080240203f00601c018070082b00205600a0140485501c038038020040100a0020980080100954a008010ac⟩,
  ⟨49,5,decodeBank 6 0x4f5394c52e4991d,decodeHints 0x601c0180700200c108010100040180700601c02805012154008170021580200302c010048040080fc0200141c0100980401c038038020980080100900400424802198008010170040100a002⟩,
  ⟨49,5,decodeBank 6 0x4f5314b9264747e,decodeHints 0x2700305400c0180700601c088110101540200302c0100220f1820100980401c0380380200402017002198008010170040100a00200601c01807002004028050080240203f00413001009⟩,
  ⟨49,5,decodeBank 6 0x4f5314bd2e47516,decodeHints 0x200c1500100800c038040080040400400601c018070020e80095e00804c0206200e00c03803068004170010040080801405e0bc0180700601c00808002024020090081b8028050ae15c1f809⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d458ed,decodeHints 0x8030540040200305a010020010100100700e00e00c0a80102a0044080402001001807006014008380020140203e0080140f01e00a0240180700601c00815002054020130080400100201201404805⟩
]

def nodesBlock11 : Array Node := #[
  ⟨49,5,decodeBank 6 0x4f53b4c52e47516,decodeHints 0x800c0b00401000c108030020100180700601c02013008154040130101540700e00e008010040280080100805c0084080200404c0180700601c020090080fc048c141c0240280500413001009⟩,
  ⟨49,5,decodeBank 6 0x51d3d4c52e47516,decodeHints 0x6010008040100100088c0e0004020130081180b04a05a0b4008af002678010040300080104802c0080100105c0080c002004060020090080fc048c70c0024008080020240280500413001009⟩,
  ⟨49,5,decodeBank 5 0x13d4991d4588a,decodeHints 0x1a058068af0061b45781602c0340180d00401c070180060380c00700e008018020040e82901401a0340a03a0ca0080680d02200c088c200e17461003006044038110220100880901a0340480400804406811022008088380301341c0020040440c01100200c0082600e01c13003006004038010020100200801a034040040080040680d002008010150300b80a8020040040c001010024028010220440080900202008811⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d4588a,decodeHints 0x2700305400c0200302c0100680d0260100700e00e0080111e1dc0080100405e0080180700601c0881102e024020090080fc0104c0040240180700601c0080100804c020130040600101800a01404817⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d45829,decodeHints 0x80705400402007094010020010100100700e00e0080100105c008010040ec0080901203801c00808002024020090080fc0104c004024018030020980082600804c0204a0040600101800a0140481c⟩,
  ⟨49,6,decodeBank 6 0x4f5314b92647516,decodeHints 0x1042004130030060981082a00200c0084600600e2900700e3640180308c01c03855002006288f68a03b4008010aa3d82a80402c0102d003006aa80b01600800c020040100102d001002aa404008008004020f60b404c020460080080380e03000c0701800e01c010030040080a8020920040084902a0b80100100406227818004188010021ec0080c0620300082d00202801002014550050010040040240180306e01c0383700600c0480700e0240080154e020042a6002004048080121682d0050121180285a008010048f60121682d03f012008010350301301a8020040240c009⟩,
  ⟨49,4,decodeBank 5 0x1314991d45826,decodeHints 0x1a0340400101c1b00a80e01c14c3380e0241740081203e07c0481202403801012002020008030060b4020040040380100e00a04801812⟩,
  ⟨49,5,decodeBank 6 0x4f5314992147516,decodeHints 0x8030540041980305a00c0680d01000401c5300611800808002020080130080100100300e0080100102a008010660200080c00200601c018050020e00080503e07c048050120140280900401401009⟩,
  ⟨49,5,decodeBank 6 0x4f5334c52647516,decodeHints 0x180700601c008030420040400106600c168032be04c020041860040980101c03803802030008010180040042480200404c1780200601c0180700a0140b80900205c0080903e07c0481700413001009⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d45871,decodeHints 0x2700305400c1980305a00c0680d01057c0700e00e0080100805c0080101305e0080180700601c0881102e0240f81f01205c0104c0040240180700601c008010080100101800406002805⟩,
  ⟨49,4,decodeBank 5 0x13d4c526458f3,decodeHints 0xd80386400e0a60383380e01a0340400103c0380181e03c1340081e03c07c2b81e0040380180e0040200080200404c0200202e0780101e⟩,
  ⟨49,5,decodeBank 6 0x4fd3d4c52647516,decodeHints 0x38030100040080800200c130010261280200404a00c2500301a034040018a80080106200400c0c0020040041700200404c1780200a0140e009006070018090020200080903e07c0481300413001009⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d45815,decodeHints 0x8070540041980705a01c0680d0100040700e00e0080100105c0080101305e0080901203801c008080020240f81f01204c0104c00402401803002020008080080100101800406002805⟩,
  ⟨49,5,decodeBank 6 0x4f5394c526474db,decodeHints 0x180700601c008030420040400106600c1680303e07c0485a2be0045600101c03803802098008010090040042480200404c1780200601c0180700a014008170021580200400433001017⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d36c7e,decodeHints 0x9c00c1500306600c1680301a0340415f01c038038020040201700200404c1780200601c018070220440b808008010010cc00405c0180700601c0080103e07c048130041300100900a0142a809⟩,
  ⟨49,6,decodeBank 6 0x4f5314991d458db,decodeHints 0x1042004130030060981082a00200c0081302c0cc250030061280b02d02600c0195f0100340980101a04c040082be0040080200e0380c00301c0600380700400c0100202a008248010021240a82e004004010020200080a0130260500802f00404c0100900600c1b80700e0dc0180301201c0380900200556008010aac008010120200485a0b407c048f601216809813012008010350301301a8020040240c00908c00c01a1100e01e2b803006118038070aa00400a100100222b001002154040080b43d8020460260103100200482c0c0188aa008010620300602d05a00a11804805⟩
]

def nodesBlock12 : Array Node := #[
  ⟨49,5,decodeBank 6 0x4f53a4e52647516,decodeHints 0x200c0380100601c018070020200086200800c16804008004098040740100221200e00c038030040080a84905c0b84080405e0100180700601c008170023ac0280500804c020171742e82b017⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d458ef,decodeHints 0x8030540040200305a0100200102a0100700e00e00c1a00102a0040800402001001807006014008380020140203e0080140f01e00a05c0180700601c0080800205402010008040010020120140b805⟩,
  ⟨49,5,decodeBank 6 0x4f53b4e52647516,decodeHints 0x200c0b00100601c018070020200085a02c00c0b003008010040130101680700e00e008010010280081a0020040200101305e0080180700601c00817002158028051582b10701700433001017⟩,
  ⟨49,5,decodeBank 5 0x13d4c51d458e1,decodeHints 0x1a084068af0061b4578210420340180d00401c070180060380c00700e008018020040e82904901a0342483a0ca0080680d03e00c0f99f00e140cf80300607c0381f03e0040f81701a0340b80100207c0681f03e0080f83e0303741f00200407c0c01f00800c0204a00e01c25003006010038040080040201301a034098010020100680d008008010100300bc080020040100c00402605c0280403e07c0201700804c0f81f⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d458e1,decodeHints 0x8030420041980305a00c0680d0100040700e00e0080100105c008010cd0ec0080180700601c008080020240f81f01205c0104c0040240180700601c00808002020020040040600101800a0140b809⟩,
  ⟨49,5,decodeBank 6 0x5253d4e52647516,decodeHints 0x600400808002118108260540a802001026010020c91d801057804008ab401001030008010800420080c0020040600100405e008008170021580b91217605c0280500804c0201700433001017⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d4582c,decodeHints 0x80704c0040200705a010020010260100700e00e008010011dc0080100405e0080901203801c008170021580201300805c010cc00405c01803002020008260081280204a0040600101800a0140b81c⟩,
  ⟨49,6,decodeBank 6 0x4f5394c52647516,decodeHints 0x4600600e2d80700e3640180308c01c038010420042a803006ac01082100200c008ed0aa020008460020100b00409400c0184a02c0b4020030083b62d459008168020041da0107685a0b40102a8040260040081355e04c020010080080380e03000c0701800e01c010030040622c018004188010021da0080c0620300082a8020920040084955c1240100100400808002028010020140200bc0100400405c018030a801c0385400600c0b80700e1542a80502e118028550020040b8ed02e1542a85602e010022ab02604d5300400805c0981702e008010310303301880200405c0c017⟩,
  ⟨49,4,decodeBank 5 0x1314991d45825,decodeHints 0x1a0340400401c1b00a80e01c14c3380e0220440b8120241400201202403801012006020008010080b4020030040380100e00a04801812⟩,
  ⟨49,5,decodeBank 6 0x4f5314992047516,decodeHints 0x2700305400c0200305a0100680d01001001c5c0061180a8080020040201300804c0100300e0080102302a008010040200080c00200601c018050220440b8050080f8020050120140281700401401047⟩,
  ⟨49,5,decodeBank 6 0x4f5314a12647516,decodeHints 0x2700305400c0180700601c0420f0020040200302c010020c30100100980401c0380380200402017002030008010180040100a00200601c018070220440b80900a014048170080240203f00413001009⟩,
  ⟨49,4,decodeBank 5 0x13d4c526458f2,decodeHints 0xd80386400e0a60383380e01a0340400403c0380181e03c0445d01e03c3740201e0040380180e0040200080200404c020020120780101e⟩,
  ⟨49,5,decodeBank 6 0x4f93d4c52647516,decodeHints 0x3803010098008011bc00c130030260100201300800c2500401a034040048ba0080106200400c0c002004020170020040101780200a0140e017006070018170220440b80800804c0201700433001017⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d45800,decodeHints 0x2700705401c0200705a0100680d0100100700e00e0080100805c0080100405e0080901203801c0881102e0200201300805c010cc00405c018030020040201300804c0101800406002805⟩,
  ⟨49,6,decodeBank 6 0x4f5314991d4587e,decodeHints 0x8042138130030060981082a01000c0180402c010250030061280b02d00800c0200401003409a0f01a04c040080081540200200e0380c00301c0600380700400c0100202a008248080101240a82e004020010020200080a0040080500802f0040100101700600c2a00700e1500180302e01c038550aa0440b8ed02e1540400802e010022ac02604d5380400805c0981702e008010310303301880200405c0c01708c00c01a1300e01e30003006118038070aa3b4008460100042d004008840098138be0100205a02604c310020048300c0188bc008010620300602a85500a1180b805⟩,
  ⟨49,5,decodeBank 6 0x519454c52647516,decodeHints 0x601c0186200200c0a80109c0040080700800c080040660100200701a034040040040080381800e1880a80102a004080040200100181c006180028050020200080800804c020131642c90481c⟩
]

def nodesBlock13 : Array Node := #[
  ⟨49,5,decodeBank 5 0x13d4c526458f4,decodeHints 0x22003602601c038130801900040700e0081202984a01c038250480ce0100700e00802006813002034098080100100080403c00c0f01c01c0380e0030060780701e03c0040f0cc010134660010020780401e03c0100f04c026374260040080780981e00400c0101801c0380c0030060080700e0040040104901002024801002008040020040100101402604c0a004008008098020300700480203c0780101c0040600f01e⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d458f4,decodeHints 0x8030540040200305a0100680d0100100700e00e00c1a00105c0044080405e01001807006014008380020140203e0080140f01e00a0700180700601c008080020200201300804c010020120140e005⟩,
  ⟨49,5,decodeBank 6 0x51d454c52647516,decodeHints 0x601c0185a00200c04001010004008080080100b04a05a0b4040010100040100303000824002004ac40100105c008010cd0ec0080181c0062ec02805002020008081a23443001c0040600101c⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d458e4,decodeHints 0x8030e00041980302c00c0680d0100040100302c0080100105c0080101305e0080186a006024008080020240f81f01204c0104c0040240180700605800808002020020040040500101400a0140e009⟩,
  ⟨49,5,decodeBank 6 0x525454c52647516,decodeHints 0x601c01855002004108260540a8020030260100980400804c020130260100100303000840002004ac80111e1dc0080100405e0080181c006180028051a83505d81c00804c020130040600101c⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d4588d,decodeHints 0x2700304200c020031d80100680d010010010030420080100805c0080100405e0080189500605c0881102e0200201300805c010cc00405c018070060840080100804c020130041240104900a0140e017⟩,
  ⟨49,6,decodeBank 6 0x5153d4c52647516,decodeHints 0xd908c01c0184600602232008002154008011b2004040550100042300104c00c0182656a0980080300204e31813008168020041b20100985a0260102300409400c0184a568128020030080100400d026004068130100200200100836631461004188010021b20086c8620c40082300203000c01818566060010030040080a8020920040084902a0b80100100400808002028010020140200bc01004004118230050381180284600600c0e0d903811823060038004008540100202a001002070040080380100203702604c1b80400807009813038008012a30300614f0020040700c01c⟩,
  ⟨49,5,decodeBank 6 0x4f5314991e47516,decodeHints 0x8070540040200705a0100680d01001003a0a00600c008080020200201300804c010ca00e0080100102a008010040200080c0020240480e0050020e0008050080f8020050120140281c00401401047⟩,
  ⟨49,4,decodeBank 5 0x13d4991d45888,decodeHints 0x1a1b40b00d01c038038020a40343280d0220486a011022034020110221340101100201c018010080340200d0040b80100100a04400811⟩,
  ⟨49,5,decodeBank 6 0x4f53149d2647516,decodeHints 0x8070540040b00700600c00c650021540202502c010020010100100980401c0380380200400417002030008010180040100a0020240480e0070020200080900a0140481c0080240203f00413001009⟩,
  ⟨49,4,decodeBank 5 0x13d4c51d458df,decodeHints 0x1a1b41080d01c038038020a40343280d03e0486881f03e0340081f03e3740101f00801c018040080340080d0040bc0100400a07c0201f⟩,
  ⟨49,5,decodeBank 6 0x4f5324c52647516,decodeHints 0x1080700600c008de0420040400100801c168048cc0100205a0080040980401c038038020300080101800400424802004010178020240480e00700a0140b81c00205c0085600804c0201700433001017⟩,
  ⟨49,6,decodeBank 6 0x4f5314991d4581d,decodeHints 0x10420041300700e0981082a00201c0080402c0102500700e1280b02d00801c020040100340980101a04c040080080040200200e0380c20a01c060038070041180100202a008248010021240a82e004004010020200080a0040080500802f0040100104608c0480e0d903811803807038004008540100202a001002070040080380100203702604c1b80400807009813038008012a40300614f8020040700c01c08c3640184600e00c2a80100284c040088d2004008550100202d004008844098138d00100205a02604c310020048340c0188ce008010620300602304600a1180e005⟩,
  ⟨49,4,decodeBank 5 0x13d4d92647516,decodeHints 0x200c1500106600c1680301a0340400101c038038030040081700110204c1781302404801807022044008081582b0370171742e82b017⟩,
  ⟨49,4,decodeBank 5 0x1424c52647516,decodeHints 0x200c150010080101680301a0340400101c038038030680041700110204c17813024048018070220440080802e04c3001702e2c831817⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d45910,decodeHints 0x8030540041980305a00c0680d0100040700e00e00c1a00105c0044081305e04c0901200601c088110020200b8130dc05c0b8180c605c230038d600c2a8018d4004020040c404c010020b406002805⟩
]

def nodesBlock14 : Array Node := #[
  ⟨49,5,decodeBank 6 0x4f5314991d458fe,decodeHints 0x8030540040200305a010020010100100100300e0080100105c0080100405e0080901200601c088110020200f81f00805c0f01e00405c0380300e00c04001010004098040200100c00202800802805⟩,
  ⟨49,5,decodeBank 6 0x4f53a4c52f49916,decodeHints 0xe00c0380309c00c150030020040380300e00c010020281541704905c3b81980305a00c0a02f05e1d83286505c57802004024048018050120140280900a0e00b80502e0140281700a0f804805⟩,
  ⟨49,5,decodeBank 6 0x51d3d4c52f47516,decodeHints 0x600c0083a0100040088c0e0004020040201181684a05a3b0040010100040807605e0bc3386705a5681a00105c0040100200a0f80480500a1a80e0050220440080502e0140281701201402809⟩,
  ⟨49,5,decodeBank 6 0x4f53c4c52647516,decodeHints 0x380300e00c2700305400c0080106600c168030080101d03a0105780380300e00c010020680201700810204c17813024048018050380140281c00a0e00b80500a0f80480501201402809⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d4588b,decodeHints 0x8030420041980305a00c0680d0260040380300e00c118010920044081305e04c09012006014088110020140283e0120140480500a0240380300e00c04001008010af0130040080a04900a05c02817⟩,
  ⟨49,5,decodeBank 6 0x5213d4c52647516,decodeHints 0x18030020200400100201c150010080101980705a01c1d0010100040100200e1200395a068004170010203341782f02e0140281700a01c0e0050220440080500a0f80480501201402809⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d4582a,decodeHints 0x80304c0041280309400c1d0010100040700e03000c1a00105c004080cd05e0bc09012006014088110020140283e0120140480500a02403803010004040010080100804a004008ad01800a05c02817⟩,
  ⟨49,6,decodeBank 6 0x4f5314bd2647516,decodeHints 0x1042004130030060981082a00200c0084600e01e378030068540380708c00c0185501002237001002850040080aa0040081002c0cc2d003006adc0b02d02000c0195e0100e808001002040040082bc004008620b4010080460085680380702800c0181400e01cad0030060500a8340c400400ab602a0b80a0010021682d0020281180105a0200400a0620281682d02f00a00c0901c00e0480e0030060140380500a004088170100440b8010020140400502f1b40b805416014028f600a05e3601700a168028090200f804aa8012014080050121880480502801402aa000a0240a009⟩,
  ⟨49,4,decodeBank 5 0x13d4c52b47516,decodeHints 0x9c00c1500300800c1680401a0340400401c038038030680201700800400817804024048018070123047580903e07c020130ae15c1f809⟩,
  ⟨49,4,decodeBank 5 0x1434c52647516,decodeHints 0x20041500300800c1680401a0340400401c038038030680201700810201017804024048018070120205d80903e07c020130122c823809⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d45911,decodeHints 0x2700305400c0200305a0100680d0100100700e00e00c1a00805c0204080405e0100901200601c048081d60240f81f00804c0481808e024230038e200c008010c40202d0048e0010010020aa06002805⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d45901,decodeHints 0x8030540040200305a0100200102a0100100300e0080100105c0080100405e0080901200601c088110020240f81f00804c0f01e0040240380300e00c0400102a004098040260100c00209200802805⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d458e2,decodeHints 0x2700305400c0200302c0100680d0100100380300e00c1a00805c02033004028010090120060140283802e0140f81f0080140480500a0240380300e00c00801424020098040040082481400a02402809⟩,
  ⟨49,5,decodeBank 6 0x5253d4e92647516,decodeHints 0x600c0080102a118150260541c00203a02a010020c91d8010020130260100a8ee05c0b8640c805456c010021020101780400a0e00b80500a2540e0050120140280903e07c0200501201402809⟩,
  ⟨49,5,decodeBank 6 0x5293d4c52647516,decodeHints 0x18030020042700705401c020130260100200705a0100203a02a0100100200e2000395b02a4781702e102010178040120140280900a01c0e00500a0e00b80503e07c0200501201402809⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d4582d,decodeHints 0x6f00304c00c020030940100203a02a0100700e03000c0a91e05c0b84080405e010090120060140283802e0140f81f0080140480500a024038030020040a82602601009804004008ad81800a02402809⟩
]

def nodesBlock15 : Array Node := #[
  ⟨49,6,decodeBank 6 0x4f53a4c52647516,decodeHints 0x4600e01e3a8030068580380708c00c018150421382a803006ae01082a02a00c018620aa0040a8460020100b00409400c0184a02c0b4020030080123a0040261680981342804c0205a0080100a8040268481d01302a0540205500856c0380709200c0184900e01cad8030061542a8020921180105502a054248620921542a82e092040408620080115b01005e1240200400a00c0901c00e0480e003006014038050131cc04805418014028ed00a0263900900a1540281702a0e00baae02e0140a80500a0100f80902607c04804008014098050121880480509201402aa100a02424809⟩,
  ⟨49,4,decodeBank 5 0x13d4c52c47516,decodeHints 0x201c1500100800c1680401a0340400401c03803c76068004170010040081780401201c300070220440080903e07c020170ae15c1f809⟩,
  ⟨49,4,decodeBank 5 0x13d4dd2647516,decodeHints 0x200c1500100801c1680401a0340400401c03803c77004008170011020101780401201c300070220440080903e07c020170122e823809⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d45913,decodeHints 0x8070540040200705a0100680d0100100700e00f1e81a00105c0044080405e010048070c001c088110020240f81f00805c0481808e024018030c401c2a8018f20042d0048f00100100208c06002805⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d45904,decodeHints 0x8030540040200305a0100680d0100100100300e0080100102a008010040200080901200601c088110020240f81f00805c0f01e0040240380300e00c0a80102a004080040200100c00203000802805⟩,
  ⟨49,4,decodeBank 5 0x13d4d12647516,decodeHints 0x200c038010080940b00401a0341d00400e12003c7b004008170010cc0103280400a01c6a0050220440080903e07c02005012014028a9⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d458e5,decodeHints 0x8070540040202502c0100680d0100100384800f1f41a00105c0043300402801002807038014088110020140f81f0080140480500a0240180300e0582a8018f8004080040040080c01400a02402809⟩,
  ⟨49,4,decodeBank 5 0x13d4c52947516,decodeHints 0x23781080100800c0380401a0341d00400e19c03c7e046004328010040081780400a01c688050220440080503e07c020170ae01402877⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d4588e,decodeHints 0x8de0420040200705a0100680d0100100388000f200118010920044080405e01002807038014088110020140f81f0080140480500a0240180300e0840a8010b40123f8040040080c04900a02402809⟩,
  ⟨49,6,decodeBank 6 0x5193d4c52647516,decodeHints 0x6208c00c038460060064200102a1540a81542c054008550020041080104c01c038260420a800807002012418040201680801042a0400205a0080100b00409401c0384a02c0b4020070080100400d0260040681301002002001008118230020301180104600e01c0c062030118230460300540a8490020042481502a06000801030040080140080100a010020060020040132080480541a014028d900a0264080900a1180281c00e01c0e2b30380140380500a004088170100440b8010020140400500a0100f80902607c04804008014098050121880480503001402aa200a0240c009⟩,
  ⟨49,4,decodeBank 5 0x13d4c52648916,decodeHints 0x9c00c1500306600c1680301a0340448501c0380380200400417002004010178020240480180500a2a42b00500a1dc1f80503c0780101c⟩,
  ⟨49,4,decodeBank 5 0x1444c52647516,decodeHints 0x2004150030080101680301a0340448601c038038020040201700200404c178020240480180500a0202b00500a04c1f80503c0780101c⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d45912,decodeHints 0x2700305400c1980305a00c0680d0112240700e00e0080100805c0080101305e00809012006014028080ac0140281307e0140f01e0040702300391000c008010b4020020040aa04c3100290e00804805⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d45902,decodeHints 0x8030420040200302c010020010100100700e00e0080100105c0080100405e00809012006014088110020140f81f0080140f01e0040700b00302c00c04001010004098040260100a00202800804805⟩,
  ⟨49,4,decodeBank 5 0x1414c52647516,decodeHints 0x200404003008010168030740e80448a01c0380380200408c0a802004198338020240480180500a0e00b80500a0f80480503c07801009⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d458f0,decodeHints 0x2700305400c1980305a00c1d03a0112300700e00e0080102302a00801066020008090120060140283802e0140283e0120140f01e0040242300391600c00801010054020040260400a00201201404805⟩
]

def nodesBlock16 : Array Node := #[
  ⟨49,5,decodeBank 6 0x52d3d4c52647516,decodeHints 0x18030020040408c0540200200402c3241682d01004c0419e0040600c0020041200b0020040201700200404c1780200a0240480500a1a80e00500a0200b80500a0240480503c07801009⟩,
  ⟨49,4,decodeBank 5 0x13d4c52647d16,decodeHints 0x1bc00c6400304a00c338030ca1940448d01c0380380200400404002004010098020240480180500a2a45d00500a1dc2b80503c0780101c⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d4582e,decodeHints 0x6f00304c00c1280309400c0401301123c0700e00e0080100805c0080101305e008090120060140280802e014028090120140f01e0040240b003002004040260080100984a0c400a4700201201404805⟩,
  ⟨49,6,decodeBank 6 0x4f53b4c52647516,decodeHints 0x4602c05a4980300685c0b01608c00c01808042020130030060981082101000c0185a0aa0040404600204c0b01609400c0184a02c058098030061542a804026118020550100200985a0261542a85500401c070180060380c00700e00801802005248010140c40500a21402800831002004054010490100202481505c008040020040400101402604c0a01005e0080980200a00c0901c00e0480e0030060140380500b24402809420024048ed0120164800500a154028170100200baaf02e0140400500a1680280902602404aa9012014098050120080f005030078028020040240c009⟩,
  ⟨49,4,decodeBank 5 0x13d4c52648d16,decodeHints 0x201c1500106601c1680701a0340400101c03803802004004170020040101780200a3005d8050220440080500a1dc1f80503c07801017⟩,
  ⟨49,4,decodeBank 5 0x13d4e12647516,decodeHints 0x200c1500106601c1680701a0340400101c038038020040041700200404c1780200a01c5d8050220440080500a2b01f80503c07801017⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d45914,decodeHints 0x8070540041980705a01c0680d0100040700e00e0080100105c0080101305e00802807176014088110020140281307e0140f01e00405c018030b401c2a80192a0040200408c04c3100292800804805⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d45905,decodeHints 0x8030e00040200305a010020010100100100302c0080100105c008010040ec00809012006014088110020140f81f0080140f01e00405c0380302c00c04001010004098040940100c00203000804805⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d458f5,decodeHints 0x8070540041980705a01c1d0010100040700e00e0080100102a0080106602000802807038014088110020140283e0120140f01e004024018030b401c04001010004020040940400c00201201404805⟩,
  ⟨49,5,decodeBank 6 0x525474c52647516,decodeHints 0x600c0b055002004108700540a80b0ec05a0b40200422644c3819e0041200b00200420010802004478770020043343b00200a1a80b80500a0240480500a05c0b80500a0240480503c07801009⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d4588f,decodeHints 0x8de0420040b0c905a0b40680d0260040104802c008010010920080101305e0080286a03801408811002014028090120140f01e0040240180302c08404001008010230130300080c00201201404805⟩,
  ⟨49,6,decodeBank 6 0x51d3d4c52647516,decodeHints 0x5a08c00c0b0460060064c8010101540400842e020008550020042300104c058460265721c000816002118230040941180204602c0582505a0941182302d33c0200404a0020042500801067800801005260010180c40600c21503000831002004058010185621200c01602c00823002004054010490020042481505c00800802004168010140943340a2b70ec0082500200b25c02809422024048d90120164b00500a1180281c02c1a80e2b40380140b00500a004088170100440b8010020140400500a1680280909402404aaa012014250050120080f005030078028020040240c009⟩,
  ⟨49,4,decodeBank 5 0x13d4c52649116,decodeHints 0x9c01c1500700801c1680401a0340400401c03803802004004170020040101780200a3003000500a2a42b00503e07c0200503c07801009⟩,
  ⟨49,4,decodeBank 5 0x13d4c52d47516,decodeHints 0x9c01c1500700800c1680401a0340400401c03803802004020170020040101780200a01c3000500a3042b00503e07c0200503c07801009⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d45915,decodeHints 0x2700705401c0200705a0100680d0100100700e00e0080100805c0080100405e008028070c0014028080ac0140f81f0080140f01e004024018030aa01c0080108c0202d004936010310029340080b805⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d45906,decodeHints 0x803054004020031d80100200102601001003042008010011dc0080100405e00809012006014088110020140f81f0080140f01e0040240380304200c0400104c004098040260100c0020300080b805⟩
]

def nodesBlock17 : Array Node := #[
  ⟨49,5,decodeBank 6 0x4f5314991d458f6,decodeHints 0x2700705401c0200705a0100203a02a0100700e00e0080102302a00801004020008028070380140283802e0140f81f0080140f01e004024018030aa01c0080104c054098040260100c00202e0140b805⟩,
  ⟨49,5,decodeBank 6 0x4f5314991d458e6,decodeHints 0x408c0540200202502c0100680d0100100104802c0080100805c008010040280080286a0380140280802e0140f81f0080140f01e004024018030420580080108c020098040300080c00202e0140b805⟩,
  ⟨49,6,decodeBank 6 0x5253d4c52647516,decodeHints 0x5508c00c108460061182300104c118008460420841305504c1182302a00927c020130b404c09a170260102d0040081180204a042324252b91d8010108040080980201355a04c098260260102a804005278010180c40600c21603000831002004084010185642000c021042008230020041540104904c47824ab81dc00813002004040010140080100a01005e0080200200b2740281742605c0b8d902e0164e00500a1180281c0422540e2b50380141080500a1540281704c05c0bab002e0141300500a0100f80902607c04804008014098050120080f005030078028020040240c009⟩,
  ⟨49,7,decodeBank 5 0x13d4c52647516,decodeHints 0x8c004108010aa0980180395a0981082a08c0040180108c0100b0040b4128018039581280b02d08c010018040aa0100400d0b404c0080d95604c040080aa0100080408c0080380e0c40600180e9540600380708c008018020aa0080a8020c4124008019521240a82e0aa008008020b4008080020c4050020049500500802f0b40080200208c0140181294e0700381294c0700180308c014038050aa0140081194a05c0401194805c008010aa014040050b40140201f9460240981f944024020040b4014098050c40240101e9420140c01e940014010020c40240c009⟩,
  ⟨60,5,decodeBank 6 0x8aa097cdd56cccc,decodeHints 0xc1400001a1b40b00d01a1f40600d01c03803803032064030000a40343280d0221740181102222c000110220340201103c0780281100201c01801000018000010080340200d0020b80100201204400811⟩,
  ⟨60,6,decodeBank 7 0x22a85e097edf3755b3,decodeHints 0x803054004000030500000000104e0000180700601c0091f0020c0000060000180200302c01002001010010020000180100580401c038038030680041700103206403000014050010020cc0100a00400601c018050020e0008050000180000500a024048050080240200503c07802809⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cd68,decodeHints 0x1042004130030060981082a00200c00800240000110030060889002800000c000002400000e801002074900270000040000402c010190030060c80b02d00800c020040100340980101a04c040080080040200401806c0580003602c0600c0080000200a00e0380c00301c0600380701400c0180a02a0d0160010020b00a82e0140040081800c06405000032028030060300000000a0200280a0040080500802f0140100200500600c2080700e1040180300a01c02805002004188080700c40080100a020028050000009000600c4800000000a018028050080101a80b07c0d40200400a02c028200400780286b00a0800500a04800c0184100e01c20803006090038070840040084501002022801002108040080560000012000c018900000000ac030060340100203601602cb00040080680580b0401ac0102b014008100200120ac02805⟩,
  ⟨60,5,decodeBank 6 0x8aa097f9d56ccce,decodeHints 0xc1400001a1b40b00d01a1f40600d01c03803803032064030000a40343280d0221740181102222c000110220340201102215c5481100201c01801000018000010080340200d0020b81a00101204400811⟩,
  ⟨60,6,decodeBank 7 0x22a85e09809fe755b3,decodeHints 0x40182a002000018280000000082700000c0380300e004d780119c0000300000c01001816008010008080080100000c00802c0200e01c01c018340020b8008190320180000a028050050020040500200300e00c038010100040480000c0000300f0120100486e0ae15c1f809⟩,
  ⟨60,6,decodeBank 7 0x22a85e097f9d56cd90,decodeHints 0x40182a002000018280000000082700001001816008010008080080100000c008038070070060d00082e0020640c806000008010140080480900300e044088010100a41480000c07c0200f01e0283180f02c00c0b00301000404001018000060000160100a00a02802804809⟩,
  ⟨60,7,decodeBank 6 0x8aa17825fe755b3,decodeHints 0x2420041080119c098018030820981082a2420040180111a0004680011a0880180311a0884682811a0000180011a0004680011a0740080111a0744682711a000008003600100b0040820c8018030820c80b02d2420100180419c0100400d08a04c0080d08a04c0400819c0100080411a0100601b11a02c0001b11a02c0600c11a010000042420280380e0400600180e04006003807242028018035740280a8345740b0008010400b00a82e19c0280080111a0600301911a0280001911a0280300611a0600000004002808002040050020020400500802f040028020042420240181208207003812082070018032420240380719c0240081108a05c0401108a05c0080119c0240400911a0240002911a03c0302911a03c0000011a0240300643003c0201f06c0240581f3400240200406c03c0580f040024100570400fc050570400fc3583f04002405009⟩,
  ⟨60,7,decodeBank 7 0x22a85e097f9f3755b3,decodeHints 0x8210020980180304c084150010060040008d00008801803044234140000060000008d0000740080103a234138000020002181602c104018030820580b04300600c180080101140080108a020040300020041580c0182340000011a0300602b000000d801602c6c0018030820580b12100600c670080101140080108a020040ce0020044680c0182340000011a0300608d000000100200082341580401401c070180060380c00700e028018030140541a02c0020041601505c028008010300180c80a0000640500600c06000000014068010140400080a01a0280281000a014080050140400500a0200280281000a01200c0901c00e0480e00300602403807012004088170100440b801002024040090120001480f00c0a4078000000240300601e0680280906c0140481a01203c1b00f01e8600780906c024049a001203c1b03f012080048350141301a86b08e02405009⟩,
  ⟨60,7,decodeBank 6 0x8aa17825d56cda5,decodeHints 0x244004108012c2098018030780981082a2440040180116600059800166088018031660885982816600001800166000598001660740080116607459827166000008002440080380e0400600180e04006003807244008018025760080a8025760b0008010400b00a82e2c20080080216600803019166028000191660280300616600800002244014018120780700381207807001803244014038052c20140081107a05c0401107a05c008012c2014040051660140002916603c0302916603c00000166014030050400240101e0400140501e04001401002040024050092440100b00495c0c8018030340c80b02d244010018042c20100400d03404c0080d03404c040082c2010008041660100601b16602c0001b16602c0600c166010000040340100a004034040010020340400a02f0340100100203402c0481f0340100281f0340100480403402c02805⟩,
  ⟨60,5,decodeBank 6 0x8aa0a7cdd56ccce,decodeHints 0xc1400001a1b40b00d01a1f40600d01c03803803032064030000a40343280d0221740181102222c00011022034020110220285481100201c01801000018000010080340200d0020b81a00101204400811⟩,
  ⟨60,6,decodeBank 7 0x22a85e0a809f3755b3,decodeHints 0x40182a002000018280000000082700000c0380300e0055e0012280000300000c01001816008010008080080100000c00802c0200e01c01c018340020b8008190320180000a0280500500a0080500200300e00c038010100040480000c0000300f0120100486e01202823809⟩,
  ⟨60,6,decodeBank 7 0x22a85e0a7cdd56cd90,decodeHints 0x40182a002000018280000000082700001001816008010008080080100000c008038070070060d00082e0020640c806000028020140080480900300e044088010100a41480000c07c0200f1502a03180f02c00c0b00301000404001018000060000160100a00a02802804809⟩
]

def nodesBlock18 : Array Node := #[
  ⟨60,7,decodeBank 6 0x8aa17829f3755b3,decodeHints 0x22a00410801228098018030820981082a22a0040180122a00020800082088018030820883102822a000018002280002280008a0740080108a07431027228000008005800100b0045800c8018030820c80b02d22a010018042280100400d08a04c0080d08a04c04008228010008040c40100601b0c402c0001b0c402c0600c0c40100000422a0280380e0400600180e0400600380722a0280180357e0280a83457e0b0008010400b00a82e22802800801104060030190400280001910402803006104060000000400280800a040050020040400500802f0400280200422a02401812082070038120820700180322a024038072280240081108a05c0401108a05c00801228024040091040240002906c03c0302910403c000001040240300657c03c0201f06c0240581f57a0240200406c03c0580f04002410009040080050a80400803584710402405009⟩,
  ⟨60,5,decodeBank 6 0x8ca097cdd56ccce,decodeHints 0xc1400001a1b40b00d01a1f40600d01c03803803032064030000a40343280d0221740181102222c00011022034020110220285481100201c01801000018000010080340200d0020b81a00101204400811⟩,
  ⟨60,6,decodeBank 7 0x23285e09809f3755b3,decodeHints 0x40182a002000018280000000082700000c0380300e0056080119c0000300000c01001816008010008080080100000c00802c0200e01c01c018340020b8008190320180000a0280500500a0080500200300e00c038010100040480000c0000300f0120100486e01202823809⟩,
  ⟨60,6,decodeBank 7 0x23285e097cdd56cd90,decodeHints 0x40182a002000018280000000082700001001816008010008080080100000c008038070070060d00082e0020640c806000028020140080480900300e044088010100a41480000c07c0200f01e0283180f02c00c0b00301000404001018000060000160100a00a02802804809⟩,
  ⟨60,7,decodeBank 6 0x8ca17825f3755b3,decodeHints 0x1de0041080119c098018030820981082a19c004018011680005a000168088018031680885a028168000018001680005a000168074008011680745a027168000008000820100b0043600c8018030820c80b02d0820100180419c0100400d08a04c0080d08a04c0400819c010008041680100601b16802c0001b16802c0600c168010000041de0280380e0400600180e04006003807040028018035880280a8345880b0008010400b00a82e19c02800801168060030191680280001916802803006168060000000400280800a040050020040400500802f040028020041de0240181208207003812082070018030820240380719c0240081108a05c0401108a05c0080119c024040091680240002916803c0302916803c000001680240300658603c0201f06c0240581f5840240200406c03c0580f040024100090400800500a0400803584704002405009⟩,
  ⟨60,5,decodeBank 6 0x8aa097cdd56ccb5,decodeHints 0xc1400001a1b40b00d01a1f40600d01c03803803032064030000a40343280d0221740181102222c000110220340201103c0780281100201c01801000018000010080340200d0020b80100201204400811⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cda6,decodeHints 0x200c1500100000c140000000041380000800c0b004008004040040080000600401c0380380306800417001032064030000140100a00400601c018050020e000805000018000050080f80200503c0780280900601c01807002b14008300000180000600802c0201a0280280100201201404805⟩,
  ⟨60,6,decodeBank 7 0x22a825f3755b36a8ce,decodeHints 0x18280000343681601a0343e80c01a038070070060640c8060001480686501a0442e8030220444580002204406804022044050a91be00d608030e80015e00012c034d780d0040081c01100201c01801000018000010080340200d0020b81a00101204400811002b1422001⟩,
  ⟨60,7,decodeBank 8 0x8aa17826027cdd56cdaa,decodeHints 0x200c1500100000c140000000041380000601c01807002b1c009160000180000600800c0b00400800404004008000060040160100700e00e00c1a00105c0040c81900c00005014028028050040280100180700601c0080800202400006000018078090080243700901411c5a80358400c220013620044480057a0016302b034010d00040040081a809⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cde1755b3,decodeHints 0x200c1500100000c140000000041380000800c0b004008004040040080000600402c00c0b00301000404001018000060000160101000401c0380380306800417001032064030000140100a0040040080a00a02404801807022044008080520a40000603e07c0203f00a014048090981301a80f⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f3755b36a990,decodeHints 0x200c1500100000c140000000041380000800c0b004008004040040080000600401c0380380306800417001032064030000140100a00402404801807022044008080520a40000603e0100780f01418c7b80358600c8b8014320044700057c0000d0044300100100200a0140b00302c00c0400101000406000018000058040280280a00a0120256402b⟩,
  ⟨60,8,decodeBank 7 0x22a85e097cdd56cdaa,decodeHints 0x1de0041080122c098018030820981082a1de0040180110400041000104088018031040884102810400001800104000410001040740080110407441027104000008005980100b0045980c8018030820c80b02d1de0100180422c0100400d08a04c0080d08a04c0400822c010008041040100601b10402c0001b10402c0600c104010000041de0280380e0400600180e040060038071de028018034340280a8344340b0008010400b00a82e22c02800801104060030191040280001910402803006104060000000400280800a040050020040400500802f040028020041de0240181208207003812082070018031de0240380722c0240081108a05c0401108a05c0080122c024040091040240002910403c0302910403c000001040240300659603c0201f06c0240581f5940240200406c03c0580f040024100090400800500a040080358471de0901002404008001803040104104b31de0900180322c0c010030434108008010401081004222c0c0008011040ac4102b10420800000104208104b21040ac00000040068104b1040080020040412c0104af04006802004040080100021040ac05002040b24100051040ac04805⟩,
  ⟨60,5,decodeBank 6 0x8aa097cdeb6cccc,decodeHints 0x30500000686d02c0340687d0180340700e0060280c8190000302900d00803401807006014000060000140200d0080340f01e00401c01802004018000020040340200d0100080100801000801005⟩,
  ⟨60,6,decodeBank 7 0x22a85e097edf37adb3,decodeHints 0x200c1500100000c140000000041380000401c0180200486c008020040180000200800c0b00400800404004008000060040160080700e006028008080020200c819000030010140040280201400802801807006014008380020140000600001401047004014020470080140f01e⟩,
  ⟨60,6,decodeBank 7 0x22a87217825f37adb3,decodeHints 0x401c0180200200c1080101000800003050000030020000080000103a0000200305a01005802008008020010260100d81b0180100700e0060280102c0040280082c0020280c8190000300200b008028018070060140104700401400863002014000060000140203e0080140f01e⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdeb6cd68,decodeHints 0x8210020980180304c08415001006004001230000880180304448c14000006000001230000740080103a48c13800002000020160080c801803064058168040060100200801a04c0080d026020040040020100200c03602c0001b016030060040000100500301c0603580e03000c0180a0d6028050010020b0040080580040080a0100200c0000320280601901400000018018030050040080500580b0280100200a016028028030061a0038070d000c0180500e014028010020c404038062004008050100140280000048c030062460000000500c014028040080d40583e06a010020050160141002003c0140501e00400c0106800e01c3400300600803802004004010360100210e801002008040020040000112300c01891800000008030020040100103601602d0e004008008058020401e8158020140081002008e00802802⟩
]

def nodesBlock19 : Array Node := #[
  ⟨60,6,decodeBank 7 0x217825f3755b35a068,decodeHints 0x8270000340680800806c0d80c0080383601501c0383f00601c0382986701c0041c00100a0000300000a0101f00400a4900280e002020008080000180000600802c0200b0040380901200202000803000030000030080b4020030060380380e00a00c0180700e00c01807⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f37add56cd68,decodeHints 0x10060a8008000060a00000000209c000040060b40200d01a0200201b0360300200343c00c3880101000404000018000060040160100580700601c0181500205400806000018000100080400200a00601c018050020e000805000018000050080f8020050400141002000601c01807002020008080000180000600802c0200b05600810005⟩,
  ⟨60,5,decodeBank 6 0x85e097cde76cc68,decodeHints 0x41380001a0340400103606c0600001c1b00a80e01c1f80300e01c14c3380e02417400812024244000120241dc638120240380101200202000803000030000030060b4198030040380100e00a04801812⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdeb79db3,decodeHints 0x40182a00200001828000000008270000cc0182d0060340680800206c0d80c00000cd9003196004040010100000600001804005810016008018070040080081500400800006004008020100040280100300e00c028010700040280000c000028050ee0fc0280f00a00802863⟩,
  ⟨60,5,decodeBank 6 0x85e097cdd56cc4b,decodeHints 0x41380001a0340400103606c0600001c1b00a80e01c1f80300e01c14c3380e024174008120242440001203e07c048120240380101200202000803000030000030060b4020040040380100e00a04801812⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cd8c,decodeHints 0x200c1500100000c140000000041380006600c1680301a0340400103606c0600000400c038020040040a8020040000300200402c0800200601c018050020e0008050000180000503e07c0480500401401009006b3401824002020008080000300000c02002c020040040280101a00a02402809⟩,
  ⟨60,5,decodeBank 6 0x85e0b7cdd56cc68,decodeHints 0x41380001a0340400103606c0600001c1b00a80e01c1f80300e01c14c3380e024174008120242440001202402c638120240380101200202000803000030000030060b4198030040380100e00a04801812⟩,
  ⟨60,6,decodeBank 7 0x22a85e0b7cdeb755b3,decodeHints 0x40182a00200001828000000008270000cc0182d0060340680800206c0d80c00000d670031f6004040010100000600001804005810016008018070040080081500400800006004008058100040280100300e00c028010700040280000c000028050160fc0280f00a00802863⟩,
  ⟨60,5,decodeBank 6 0x87e097cdd56cc68,decodeHints 0x41380001a0340400103606c0600001c1b00a80e01c1f80300e01c14c3380e024174008120242440001202402c638120240380101200202000803000030000030060b4198030040380100e00a04801812⟩,
  ⟨60,6,decodeBank 7 0x22a87e097cdeb755b3,decodeHints 0x40182a00200001828000000008270000cc0182d0060340680800206c0d80c00000d67803196004040010100000600001804005810016008018070040080081500400800006004008058100040280100300e00c028010700040280000c000028050160fc0280f00a00802863⟩,
  ⟨60,6,decodeBank 7 0x217825f3755b36b868,decodeHints 0x8270000340680800206c0d80c0000383601501c0383f00601c0382986701c0482e80102404848800024048058c7024038010121e0005678010ea001670000080104b80e3640383501200202000803000030000030060b4198030040380100e00a04801812006b3420003⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f37add56cdae,decodeHints 0x200c1500100000c140000000041380006600c1680301a0340400103606c06000006b4c018fc002020008080000300000c02002c0800b00400c038020040040a8020040000300200402c080020140080180700601400838002014000060000140280b07e03c0280200a18c2000336600c5e8015a4004450005a2000020045a00ac100023420081a805⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981e027adb3,decodeHints 0x200c1500100000c140000000041380000400c03802004004040020040000300200601c018070020e8009b50000180000600402c01020006120019b4002020008080000300000c0040280101a0200501782f00601c0180700202000808000018000060040fc0103600a0142b857⟩,
  ⟨60,5,decodeBank 6 0x825f3755b333868,decodeHints 0x1a1f40600d01c1f80300e01c0341d00d0bb2d00005d0ba0340200d0ba0380100e000018000010080340200d0040380100e0240480085d000030000030080340200d0040380100e0220440185d00200c00807⟩,
  ⟨60,6,decodeBank 7 0x217826027cdd56cc68,decodeHints 0x8270000056a0011e00000300000c010008080080100000c00802c0200e0d80540700e0fc0180700e0040080700e008120070010100040400000c00003012024010350c70040380100e002020008030000300000300e00c01807008058020030040380100e00e00c01807⟩,
  ⟨60,6,decodeBank 7 0x22a825f37add56ccce,decodeHints 0x18280000343681601a0343e80c01a00d6a0031be000060000180100680401a00801807004008000060040080683a01a0280100300e00c1c00000c0000300401a010068110220081c0a900201c01801000018000010080340200d010004008080040540100100a00400838⟩
]

def nodesBlock20 : Array Node := #[
  ⟨60,7,decodeBank 8 0x8aa17826027cdeb755b3,decodeHints 0x803054004000030500000000104e0000180700601c00ad60022f4000060000180200302c010020010100100200001801005804006b54018b5002020008080000300000c0340802781a00813c0201a00400c038020040040a802004000030020d6008010200040110f8020140080180700601c0080800202000006000018028050080d41f8090120081a847⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cde5755b3,decodeHints 0x200c1500100000c140000000041380006600c1680301a0340400103606c0600000e00c0380302a0040a80100c000030000080100800b00400c038020040040a8020040000300200402c080020040280d00202404801807022044008080520a40000607c0f81a80f0120240280503c07801047⟩,
  ⟨60,6,decodeBank 7 0x217825f3755b354868,decodeHints 0x8270000340680800206c0d80c0000383601501c0383f00601c0382986701c004040010100000300000c1403500b0040380100e00202000808000018000060080100100e0040380901200202000803000030000030060b4198030040380100e00e00c0180700e00c01807⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f37add56cd52,decodeHints 0x200c1500100000c140000000041380006600c1680301a0340400103606c06000006b60018da002020008080000300000c02002c0800b00400c038020040040a8020040000300200402c080020140080180700601c00808002020000060000181f0350160240480206a11c0180700601c0080800202000006000018020045ae0ac0103600408002805⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981deb6cd90,decodeHints 0x803054004000030500000000104e0000100300e008010010100080100000c00801848006880008080020200000c0000300100a0040680180700601400838002014000060000140100500418c0780506600c16803074004040010b6000060000160080a01005e0bc1f805⟩,
  ⟨60,6,decodeBank 7 0x22a85e09755b36415b,decodeHints 0x200c1500100000c140000000041380000400c03802004004170020040000300203e1400181f03e4940081f03e52c0001f03e3740101f02c00c0b00301a0340400103606c060000160080a00201207c02016006010020080020100200c0000100100a0040100281f00807c08004⟩,
  ⟨60,6,decodeBank 7 0x217825f3755b364068,decodeHints 0x827000010008080080100000c0080383601501c0383f00601c0380204801c0482e80102404848800024140020120240380101201000404001018000060000160102400e090038350120020200080300003000003008058020030040380100e00a048018120060580b003⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f37add56cd90,decodeHints 0x803054004000030500000000104e0000200302c010020010100100200001801001ada0063dc008080020200000c000030022d90080680100300e0080100102a0080100000c008010044420080500200601c018050020e0008050000180000507c0100280f00a0080286302c00c0b00301000404001018000060000160101001a09e068100020d60081a805⟩,
  ⟨60,6,decodeBank 7 0x22185e097cdd56cc68,decodeHints 0x2000806000000030000020740000b0080100580400204c0201b0360300200e0040080700e0022000700e0fc0180700e0a619c070120240044a9120000180000600802c0200b0040380100e00e00c0180700208400803000030000030080b4020030040380100e00e00c01807⟩,
  ⟨60,7,decodeBank 8 0x8aa2185e097cdeb755b3,decodeHints 0x180700601c008030420040400100000c1400000c000000060000040e80000800c168040160100200b0080040980403606c06004006b6c018400841083d87b0022180087b0000300000c00802c0200b00400c038020d60080107b0040043d80200400003002004010080020140080180700601c028050020c42b00000c000030040160100581702e00818863⟩,
  ⟨60,6,decodeBank 7 0x217825f3755b32dc68,decodeHints 0x348270000340680800806c0d80c0080383601501c0383f00601c0382986701c1744a8080000180000600802c0200b0040380100e002004000060000180200b00802c0100e0040380901200602027003000030000030080b4020030040380100e00e00c0180700e00c01807⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f37add56ccb7,decodeHints 0x9c00c1500300000c140000001a41380000800c1680401a0340400403606c06004006b700187102a0200a8080000300000c00802c0200b00400c038020040200a80200400003002004010080020140080180700601c1c0310100000300000c0100580401605c0b80206218c0180700601c008010000180000600802c0200b0840ac010360041ec02805⟩,
  ⟨60,5,decodeBank 6 0x8e23485e0981deb,decodeHints 0x61dc0180500200c040010700040080500000c0600000c00000005000004138000040100800200a008014b500400404002004000030020060700182f00a02402858002020008080000300000c0040280101c⟩,
  ⟨60,5,decodeBank 6 0x8ea3485e097cdeb,decodeHints 0x100500418c008020100081c0010020140000200c008030000000140000104e000020020ee0141f805074004040010b600006000004028010fa00a024028c4002020008080000300000c0203441782f⟩,
  ⟨60,6,decodeBank 7 0x2348aa17826077cdeb,decodeHints 0xe00c1c0010020140080304c00403000000014000030440000000104e0000280200418c01003344008010010100080100000c0083b80507e0140800336c00c1d0010100042d8000180000200200a0240285800607001860002020008080000300000c0040280101c0200dc1782f⟩,
  ⟨60,6,decodeBank 6 0x8d63485e097cdeb,decodeHints 0x40008010050d0014028020040816f847002100008150040080a84002a004010020100c41c00100a0040083100202002805000588000060040080316200c0000100200c5880300000a00000162000018028050005880001d0020040e96204e0000080000810402010004008081a2020010010020160d41f00400a0100203500802c028050080200681300203409808010010008040080300d80b00006c0580c01801000004048008010b20d00285900200409020060048014028b20400245900500a090200c416400400ade0100216f0010022c804008164000002dd0180316e8000002c80600c164010021a301602cd18040082c80580b⟩
]

def nodesBlock21 : Array Node := #[
  ⟨60,6,decodeBank 7 0x2388d217825f37add5,decodeHints 0x601c0180500200c040010700040080500000c0600000c00000005000004138000080101a80506a01404001010004060000180000181c0063e80280900a090008080020200000c000030688d10c0070010033440080280200411c0100102a0080100000c0080103236c00805002⟩,
  ⟨60,6,decodeBank 7 0x23d8d217825f37add5,decodeHints 0x601c01805002004188050620140000303a000030000000140001d03a000020030260101f004008014020130260100d81b0180100181c0061800280900a0906a0d41760700000c0000300200b00802c010030800080280200411c010260800080100000c0080100402000805002⟩,
  ⟨60,7,decodeBank 7 0x2348aa17825f37add5,decodeHints 0x1601000380300a00c04031070004028010020c40080800a014008400020980180304c894130010060040312600c000028000004980000600a014001260000880180304449811000006000001260000740080103a498138000020000583507c010028040080d40200b00a014024b70080c801803064890190040060100200801a04c0080d026020040040020100200c03602c0001b016030060040000101200500a0701000903801402824080090120030060703401c03800c018240801800e001002150040080a80040081c0100200e0000001fc0600c0fe0000001c0180300e0040080dc0580b06e0100201c01602c3400500a008100020040140104104011c010400041000180308010511802006008010150052d8008010800540a802002008010060044980000024c01803002000008010100041040200444404008002008008340410140080e002⟩,
  ⟨60,6,decodeBank 7 0x2358d217825f37adb3,decodeHints 0x401c010200020080a80209c004008070000080300200c0000000600000413800008008080020660100200701a0340400403606c060040040280102400e060038c4002020008080000300000c00802c0200b0041a0010e000a01400808002020000060000180200b00802c590b2⟩,
  ⟨60,7,decodeBank 8 0x8d22a85e097cdeb755b3,decodeHints 0x38030100040080800200c1300100c0000000600000c11000000004138000160100200b00800c1900401a0340400403606c060040480802002400621c01824002020008080000300000c00802c0200b0d60080102000400d130020040040a8020040000300200401008002014008028050062c0200010100040400000c000030040160100581c038008342df⟩,
  ⟨60,5,decodeBank 6 0x85e097cdeb1b054,decodeHints 0x104e0003686d0100042f05e0180000905d002048090910000480905005e048010015c00080100000c0080100435c008050120040480083800200c0000600000c0187704a00c0481200401401003⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981df37ac54,decodeHints 0x807054004000070500000000104e00001227180008010010100080100000c008d700705a01c1d0010100042d8000180000200202404803858002020008080000300000c0040280101c0200dc1782f00600c00838002014000060000140100500418c0287707e01404805⟩,
  ⟨60,6,decodeBank 6 0x85e097cdeb18c54,decodeHints 0x58c0001d0020040e96304e000008000080200681300203409808010010008040080300d80b00006c0580c01801000004024004090950101744a80100204804012024000090d50182446a800000048060120240100906a0161403500400804805812004054012e1002005708155c00080080200401801163000000b180600c00800002004040012280080111401035c008020020d025c05002024048018010020c4040380620040080301000c0180000058c030062c60000000300c00c018040080d40583e06a0100200301600e5ccb801200c09012006008010051800140280200400c60003⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdeb75454,decodeHints 0x8210020980380704c0841500100e004001270000880380704449c1400000e000001270000740080103a49c13800002000020160080c8038070640581680400e0100200801a04c0080d026020040040020100200c03602c0001b01603006004000010120070240703401203801c038240800900e001002150040080a80040081c0100200e0000001fc0600c0fe0000001c0180300e0040080dc0580b06e0100201c01602c010070041004ba2a08001c60002080008010150052e8008010800540a8020020080100600449c0000024e01803002000008010100041040200445204008002008008340410140080e0020802c00180500e00c028010020c404038062004008050100140280000049c0300624e0000000500c014028040080d40583e06a01002005016014208410120140e005040008010050d00140280200408171047⟩,
  ⟨60,6,decodeBank 7 0x217825f37adb318c54,decodeHints 0x41380001a0340400403606c0600401c1b00080e01c1f80000e01c14c0200e002020008080000180000600802c0200b0240480100109c0080100000c008010040660080500e00e008010c0002020008030000180000300802c020039760387000300401c01003⟩,
  ⟨60,6,decodeBank 7 0x217825f3755b31a054,decodeHints 0x8270000340680800806c0d80c0080383601501c0383f00601c0382986701c0482e8010240484880002404828004024048070020240040400100e0000600000e0101680400e0080700201c01c090e9002020008080000180000600802c0200b0040380100e00a04801803⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f37add56cc54,decodeHints 0x201c1500100001c140000000041380000801c1680401a0340400403606c0600400e69003824002020008080000300000c00802c0200b0048ac038020040040a8020040000300200401008002014008748b000e004040010100000300000c010058040160700e0020d0b8801803002020008080000180000600802c0200b0820ac0106800408002805⟩,
  ⟨60,5,decodeBank 6 0x8aa17832077cdeb,decodeHints 0x80305400400003050000000010ac0007000318000c040011520040100200a0001980305a00c1d0010100043b8000180000580b0240480180f022044008080520a40000c1502a03180f01e0501780f⟩,
  ⟨60,5,decodeBank 6 0x8ce17826077cdeb,decodeHints 0x8030ac004000030500000000104e0000100200a00c04001152004db80023a0003b80307e00c1d0010100042d8000180000580b0240480180f022044008080520a40000c01e0283180f01e1801780f⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981df37adb0,decodeHints 0x803054004000030500000000104e0007000318000c04001152004db80023a0001980305a00c1d0010100042d8000180000580b0240480180f022044008080520a40000c01e0283180f01e0501780f00a00d7200300a0042b00100a001718000040080287707e01404805⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981df37ad94,decodeHints 0x200c1500100000c140000000041380000400c03802004004040020040000300206600c16803074004040010b6000060000080080901200603c08811002020148290000300f01e00403c0781405e03c0280300e00c028010700040280000c0003180200a0fc3b80502801402809⟩
]

def nodesBlock22 : Array Node := #[
  ⟨60,6,decodeBank 7 0x22a85e0981deb78db3,decodeHints 0x803054004000030500000000104e0000100300e0080680d0100080d81b00c008018670060bc00808002194001ba0006e40100a00402c1980305a00c1d00102a0042d800370000020020280bc0180700601400838002014000060000140100500402c2b80500a1dc1f805⟩,
  ⟨60,4,decodeBank 5 0x21783e076cd5b,decodeHints 0x41380001a0340400203606c030020020e0008050000180000503e07c0100b002020008650006e8001b90040280100400a15c02877⟩,
  ⟨60,5,decodeBank 6 0x85e0981dea6cd5b,decodeHints 0x41380001a0340400203606c0300200600415001006001160000a614c038020020e0008050000180000503e07c0100b00601c01805002020008650006e8001b90040280100400619c0183300a15c02877⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981deb6cd5b,decodeHints 0x200c1500100000c140000000041380000400c0380201a0340400203606c0300200612001a2d002020008080000300000c00402c0100b00601c018050020e000805000018000050040140100b0120140182d0060cc008080020e80000c00016c0100b0040101782f00a0fc02877⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981df36ccbc,decodeHints 0x1000c1080300000c140000000200e80000400c038020040e4040020040000300206600c168030100bc044bc0b600006000008008018070060140881102e014000060000140100500405c0287707e01401848006084008010000300000c0040280102c0340bc3b02f00a02402817⟩,
  ⟨60,5,decodeBank 6 0x85e0f81df37adb3,decodeHints 0x4138000040040400200400003002074004040010b600006000008008008080020200000c0000300100a0040f00822c05e0bc00838002014000060000140100500418c0287707e01404805⟩,
  ⟨60,6,decodeBank 7 0x217826077cdeb7a9b3,decodeHints 0x104e000010010100080100000c0081d0010100042d80001800002002002020008080000300000c004028010cb0208b41782f0060041500100600172800006008038020060cc1680309000c00838002014000060000140100500418c0287707e0140480500601c01805⟩,
  ⟨60,6,decodeBank 7 0x217826077cdeb6cc68,decodeHints 0x104e000010010100080100000c0081d0010100042d80001800002002002020008080000300000c01c038011b2020120338670020e000805000018000050040140106300a1dc1f8050240480080800200c0000c00000c0100700400c0182d06600c2c00300a00c01807⟩,
  ⟨60,6,decodeBank 7 0x2388aa17826077adb3,decodeHints 0x600c0083a0100040088c0e00040005b018000000db0500000000104e000010040200080103205a008010010100080100000c0080807605e0bc3386705a160008080020200000c0000300100a0040c80287707e0140282d36c01400838002014000060000140100500418c04805⟩,
  ⟨60,6,decodeBank 7 0x22a89e17825f37adb3,decodeHints 0x100300e0082700305400c0080200000c14000000008030020001a41380006600c168030080081d03a0103142d800018000018480060b00100a0040f41a00805c0200000c0000304081305e04c01807006014010050040d8028a90ac014000060000140287707e01404805⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdeb6cccf,decodeHints 0x200c1080100000c140000000040e80006600c1680301a034098010b6000060000061200182c0020e4008140000300000c10204c1781300601c0180500218c008050000180000500a1dc1f8050120140100300e00804002004000030020040103d8020140080102c00a00801063⟩,
  ⟨60,6,decodeBank 7 0x23a8aa17825f37adb3,decodeHints 0x18020020080400200201c150010000080300200001c14000000004138000080081980705a01c1d0010100042d8000180000100a0040f00384800e310008080020200000c000030080cd05e0bc0100500418c028c034401400838002014000060000140287707e01404805⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdeb6cc6c,decodeHints 0x200c1300100000c110000000041380004a00c19003074004040010b60000600001c03801858002020008080000300000c0203341782f00689c018e00020e0008050000180000500a1dc1f805012014038020040040400200400003002004010080020140080101800a00801063⟩,
  ⟨60,7,decodeBank 7 0x22a85e0981df37adb3,decodeHints 0x20840082600600c13021054004018010003c40002200600c110f1050000018000003c40001d0020040e8f104e0000080000401c012ee00600cde00700e00801802004020012ed002004dd80801000800802004018010f10000007880600c0080000202005819cbd00600d1701605a0400180336a0201d010002004080080106d4008010200302d8f10000007880c01804000000040080020100040082c0030060517604802800c018585d61600a001002ba804008162004008140100200a0000003c40600c1e2000000140180300d0020040501b00a0280080101a3420680d010020051748140280401781a5d00bc028030068a40380744400c0180500e014028010020c40403806200400805010014028000003c4030061e20000000500c015738020040141b00500a008012e606c18c02a2100a11c0807708e87c1f805020014100200120140a005⟩,
  ⟨60,5,decodeBank 6 0x8aa17831f37add5,decodeHints 0x80305400400003050000000010ac0001980305a00c0680d0100040d81b0180000901200603c0881100202014829000030538a702003c7000318000c0a8011520040100200a0003180b02002c540a8⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdeb755b0,decodeHints 0x200c1500100000c140000000041380006600c1680301a0340400103606c060000240480180f022044008080520a40000c01e02c0800f1c000c6000302a0045480136e0008e8000c602c0800b01403c0280325000c028010ac004028005de0000200407e0140480500400802847⟩
]

def nodesBlock23 : Array Node := #[
  ⟨60,6,decodeBank 7 0x22a85e0981dd56cd5b,decodeHints 0x803054004000030500000000104e0000380300e00c0680d0100040d81b00c0000380300e00c1a00105c0040300000c0000100200601c018050020e0008050000180000503e07c0280b012014028090060b4018330020200083a0000300005b05602c0200405e0bc0801400a0240283e⟩,
  ⟨60,6,decodeBank 7 0x217826077cdd56cc68,decodeHints 0x82700002000808002018000060000e80080800216c0000c00001002048002054008060000180000e01c040240670241740081202424400012024014028120240f83501202401402812002020008030000300000300601c038030060b41980300601c0380300a04801812⟩,
  ⟨60,7,decodeBank 8 0x8aa17826077cdeb755b3,decodeHints 0x803054004000030500000000104e0000380300e00c040010100040300000c0001980305a00c1d0010100042d80001800002004006bc401858002020008080000300000c0340d82781a0208bc0801a00e00c0380302a0040a80100c00003000004008080200400500a00300e00c028010700040280000c0000286b00a0157800507c0fc0280900a08002847⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdeb791b3,decodeHints 0x200c1500100000c140000000041380000800c0b00401a0340400403606c0600401c0380180a002020008080320640000c00802c0200a00401c01802004020008020040180000200402c02002028008018070060140083800201400006000014020470080140f01e00411c01005⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981df37adb3,decodeHints 0x200c1500100000c140000000041380000400c03802004004040020040000300206600c16803074004040010b60000600000800801848006160008080020200000c0000300100a0040680801405e0bc0180700601400838002014000060000140100500418c0287707e01404805⟩,
  ⟨60,6,decodeBank 7 0x217825f37adb356068,decodeHints 0x41380001a0340400403606c06004002020008080000300000c0a614c0200b0020e0008050000180000500811c02005024048010012980080100000c0080800201c0380280200411c0080800200c0000c00000c0201600800c6b00300a00c0180700401c01003⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdeb6cd58,decodeHints 0x8210020980180304c08415001006004000fd000088018030443f414000006000000fd0000740080103a3f413800002000020160080c8018030640580b0040060100200801a04c0080d026020040040020100200c03602c0001b016030060040000106b0030060517904802800c018d60823580a0010021140400808a004008140100200a0000003f40600c1fa000000140180300d0040080500580b0280100201a01602c028030061040380708200c0180500e014028010020c40403806200400805010014028000003f4030061fa0000000500c0140280400811c0584708e01002005016014100200120140a00500401c0102000600c2080700e008018020040800107b0020043d8200f600800802004018010fd0000007e80600c008000022c80800800200800a5f0200140080a0020d60140280208e0080100500408023847⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdeb755ab,decodeHints 0x200c1500100000c140000000041380006600c1680301a0340400103606c060000061a801809002020008090000300000903e07c0480b00400c038020040065f802004000030020041983b8020140080180700601400838002014000060000140283e0080100780500401401047⟩,
  ⟨60,5,decodeBank 6 0x85e097cdd56cc66,decodeHints 0x41380001a0340400103606c0600001c1b00a80e01c1f80300e01c14c3380e024174008120242440001203e07c048120240380101200202000803000030000030060b4020040040380100e00a04801812⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdde755b3,decodeHints 0x803054004000030500000000104e0001980305a00c0680d0100040d81b01800001929006090008080020200000c0000300800b0080100100300e0080100102a0080100000c008010660200080500200601c018050020e0008050000180000503e07c048050120140280900401401009⟩,
  ⟨60,6,decodeBank 7 0x22a85e09755b35bd5b,decodeHints 0x200c1500100000c14000000004138000a614c038020a41480a80237a6f40300200601c018050020e000805000018000051ba3740100901600c5300301a0340400103606c060000280080f81f0120140182d0060cc008080020e80000c00016c0100a0041980280900a0f802004⟩,
  ⟨60,6,decodeBank 7 0x217825f3755b35bc68,decodeHints 0x8270000e80080800216c0000c0000383601501c0383f00601c14c0800e02417400812024244000120240f8350120240380101201000404001018000060000080102400e0d40483501200202000803000030000030060b4198030040380100e00a048018120064a434003⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f37add56cd6f,decodeHints 0x803054004000030500000000104e0001980305a00c1d0010100042d80001800001af50063f8008080020200000c000030082f40200680100300e0080100102a0080100000c008330100040280100300e00c028010700040280000c0000280507c0fc0280900a0080286308000cd98030100040400101800006000008010b281a09e068b20025e601435805⟩,
  ⟨60,6,decodeBank 7 0x22a88a17825f36cd5b,decodeHints 0x400c0380209c00c15003002008000030500000000200c0080006904e0000b00302c00c058020260081701305c02c0d81b0180000180700601401005004024028a90ac014000060000140f81f012014018160060580100a0040501802e1300b80000c0000300200400a02402809⟩,
  ⟨60,6,decodeBank 7 0x22285e097cdeb6cc68,decodeHints 0x802000008030020001a413800008008098020080e80a80403606c0600401c0380114c02a2000a8c80000300000c00802c0200b0040140104700a2a42b005000018000050080f8020050240480100700400c0182a09c00c0000c00000c0202d00800c1600300a00c01807⟩,
  ⟨60,6,decodeBank 7 0x22a88a097cdeb6ccc8,decodeHints 0x400c0380200000c140000000080300207400c0b00301a0341d0020740000600000632001898004028010f80000300000c07404c3286500601c01805004014010470000180000500b3001a8050120140a80302c00c3d802010008060000180000200405c0b80a89806a0141a805⟩
]

def nodesBlock24 : Array Node := #[
  ⟨60,7,decodeBank 7 0x22a88a17825f37adb3,decodeHints 0x401c0104000600c2000700e0080180202a0842704000600c20021054054018030f61ec008150040080012a000088018030444a8140000060000012a0000180100200c4a8030000040080012a0000740a86903a4a81380002a000020160080c801803064058168040060100204500804c010020266ec098040040080201500804d1803a0260540a80417a0100200c03602c0001b01603006004000010160030061257b88009200c0182c0800b0210020040b01b00a058008010420f61082101502a0b06902c058054170420f60b8248000000b00600c0580000004901803016004008bd80580b1060100202c01602c028030061000380708000c0180500e014228020040141b00500a0080104508a11c028bd00a18c0a8a90c61ec2b00502a014028000004a8030062540000000500c014028040080d40583e06a010020050160141002001201416005⟩,
  ⟨60,7,decodeBank 7 0x2358aa17825f37adb3,decodeHints 0x4010001807004008008400020540100202a1000a801004008008210020980380704c0841500100e0040012b0000180100200c4ac030000040080012b000088038070444ac1100000e0000012b0000740080103a4ac1380000200002041008040010020206f008004004008020160080c8038070640581680400e0100200801a04c0080d026020040040020100200c03602c0001b01603006004000010120020040603400a030008010240800901200700e0603401803001c038240803100c00100212404008092004008180100200c0000002d80600c16c000000180180300c0040080500580b0280100201801602c208020040143400500a0080104108211c0284000a100038c00808991180500e014028010020c40403806200400805010014028000004ac030062560000000500c014028040080d40583e06a01002005016014100200120140c005⟩,
  ⟨60,6,decodeBank 7 0x22a85e097ddf37adb3,decodeHints 0x200c3800100000c140000000041380000400c03802004004040020040000300206600c0b003074004040010b6000060000080080700e006160008080020200000c0000300100a0040600801405e0bc01a2800638000838002014000060000140100500418c0287707e01404805⟩,
  ⟨60,6,decodeBank 7 0x23885e097cdeb6cc63,decodeHints 0x803010004000030180000000104e00002004010004040010180000600001c0380183c002020008080000300000c030120338670060d4018e00020e0008050000180000500a0d41a8050120140100300e0080100102a0080100000c0080102d02c0080500200a00801047⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdeb6cc63,decodeHints 0x8400020980180304c114380010060040012c000088018030444b0140000060000012c0000740080103a4b013800002000024c10080c8018030648c4530040060100200801a04c0080d026020040040020100200c03602c0001b016030060040000101200301c0603400e03000c018240800900c00100212404008092004008180100200c0000002d80600c16c000000180180300c0040080500580b0280100201801602c0280300610115a2a08000c01805080380028010020c40403806200400805010014028000004b0030062580000000500c014028040080d40583e06a01002005016014100200120140c00508008003802006008010150041ec008010f60540a802002008010060044b0000002580180300200000801010004080020045f004008002008008340200140080c0020d6014028020400080100500408010047⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cd5b,decodeHints 0x803054004000030500000000104e0000b00302c00c0680d0100040d81b0180000100300e0080100105c0080100000c0080100b0280080180700601400838002014000060000140f81f0120140100500402401816006058008080020200000c000030020040040280101400a02402809⟩,
  ⟨60,6,decodeBank 7 0x217825f378dd56cc68,decodeHints 0x104e0000680d0100040d81b0180000a80102a004790001e40000200401c1b00a80e01c1f80300e01c02c3380e01c120d900e02417400812024244000120240d4638120241a81a8120240380101200202000803000030000030060580b0030060580b0030040380100e00a04801812⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f37ade3755b3,decodeHints 0x803054004000030500000000104e0000b00302c00c0680d0100040d81b01800001af90060f0008080020200000c0000300d00b0d605801816006054008150023c8000f20000100216605600801807004008008150040080000600400805ae8004028010020406840100300e00c028010700040280000c0000280506a0d40280f00a0141a83500a00802847⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cd94,decodeHints 0x803054004000030500000000104e0000200305a01002001010010020000180100100300e0080100105c0080100000c0080100405e0080901200601c08811002020148290000180f81f00803c0f01e00403c0380300e00c040010100040300000c000058040200100500202800802805⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cd72,decodeHints 0x803054004000030500000000104e0000200305a01002001010010020000180100700e00e00c0a80102a0040c81900c000050040200100180700601400838002014000060000140203e0080140f01e00a0240180700601c00815002054000060000180200b0080400100201201404805⟩,
  ⟨60,6,decodeBank 6 0x8aa177cdd56cd30,decodeHints 0x20840082600600c13021054004018010360580dafd0061797e81605a06c0181b0360200d9f20021f4f900801006c0081b03201c0cafc0061f97e00700e064018190320540c91c0021648e01505c064008190320400c81403606c0a01005e0640d81905200c14afb00e2457d8030060a40382905200414afa01022d7d0010020a4040290520101480903606c048040080a40d82905200814805032064028020040a40c82900000c000221ec0a011003006000340000000040001d1ec09c0e801002000418000000100200c03606c060040080000d81b00000801006032064030020040000c81900c014028000520a40000500001814829⟩,
  ⟨60,6,decodeBank 6 0x8aa097cdd56ccd0,decodeHints 0x6f80002200600c111be0500000180001a058068af0061b45781605a0340180d01a030068e10001f47080c0180340000d00401c3611e0061b08f00700e008018020040182c8390001641c80600c008000020040402901401a0340a01005e0080680d02200c088c200e1746100300604403811022000088d700c22c6b800000044030110220100880901a034048040080440681102200808805072134028020040441c81100200c008260420a81300300600410801002000001be03a09cdf0000000040e8010020100200801a034040040080040680d002008010150720b80a8020040041c801010014028010220440080500202008811⟩,
  ⟨60,6,decodeBank 6 0x85e097cdd56cc6d,decodeHints 0x6fc0001d0020040e9bf04e00000800008020368c90021b464808010010008040080302f03b0001781d80c0180100000401c054070800021b04001505c0380080e01c018070e20001f87100600c0380000e01c0400701400814c0a01005e0380200e024004090950101744a80100204804012024000090d500c2446a8000000480301202401009009076140048040080481d8120240080900501c03802802004048070120060040082104c0a81080100200c13003006000001bf0440a0df80000000c11003006010020160760b40b00400800c1d8030060080100701c0380380200400c0700e00e014028030240480180500601c09012⟩,
  ⟨60,7,decodeBank 7 0x22a85e09821f3755b3,decodeHints 0x8210020980180304c08415001006004000ea000088018030443a814000006000000ea0000740080103a3a813800002000218030061a027cc610e00c0184309e10c2100100220c27cc510c0040084209e108158000003a827cc41d40000002b1d40ac0201600930c018030d0058168040060100200800804000801020020040040020100200c0083a8000001d403006004000010279660160101580400401c0101400600c0a00700e00801802004054014c20020044181505c00800802004018010ea0000007500600c0080000209e5a005002056008010100040500200402804017802008008028030060dc0380706e00c0180500e014028010020c40403806200400805010014028000003a8030061d40000000500c0142796701e0141580500a010020090200f8048040080140800501200801005028014028020040240a009⟩,
  ⟨60,6,decodeBank 7 0x22f8aa17825f3755b3,decodeHints 0xb0030100040080800200c150010180000000c00000c11000000004138000160c80200404a00c1900301a0340400103606c060000140080104300400c03802004004170020040000300200402c3b0020120140280900601c018050020e0008050000180000503e07c0480500401401009⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cc3b,decodeHints 0x22303800100036c140000000041380002c0ec1682d01a0340400103606c0600001c0380b002004004170020040000300200402c3b0020240480e0050020e0008050000180000503e07c048050040140100900600c008080020200000c000030020040040280101800a02402809⟩
]

def nodesBlock25 : Array Node := #[
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cd5b,decodeHints 0x8210020980180304c08415001006004000ff000088018030443fc14000006000000ff0000740080103a3fc138000020000581602c0c8018030640580b00b00600c0580801a04c0080d0260200400b0020040980c03602c0001b01603006013000000010070040500180302801c0380200600801015005320008015ec05417002002008010060043fc000001fe01803002000008012f40040500580b0288bc0a002016008028030060dc0380706e00c0180500e014028010020c40403806200400805010014028000003fc030061fe0000000500c01402ad903e0240581f01213c04805016014048020040140a00500a00801009028024218030068c80b01698e00c0184302c058180010023480400816200400830010020158000003fc0600c1fe0000002b0180302784f0080ac0580403400801036028028b28020040680a014034014028200120241000500a06804809⟩,
  ⟨60,5,decodeBank 6 0x85e0f7cdd56cd5b,decodeHints 0x104e0000680d0100040d81b0180000100105c0080100000c0080100b45800800838002014000060000140f81f01201401005004024008080020200000c00003002004004028011a500a02402809⟩,
  ⟨60,6,decodeBank 7 0x217825f37a9d56cd5b,decodeHints 0x104e0000680d0100040d81b01800001801054004018005fc0000181602c00c0100105c0080100000c0080100b45a0080100300e00800838002014000060000140f81f0120140180700601401005004024008080020200000c0000300200400605801816004028010d600a02402809⟩,
  ⟨60,6,decodeBank 7 0x217825f3755b356c68,decodeHints 0x104e0000680d0100040d81b0180000100102a0080100000c008298530900080083800201400006000014280500d4014010050041a8008080020200000c0000300200401c038010480240480286a00202000803000030000030060580b00300401c0100300a00c0180702c00c01816⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f37add56cd5b,decodeHints 0x803054004000030500000000104e0000b00302c00c0680d0100040d81b01800001b00006bfc008080020200000c0000303584f01600801807004008008150040080000600400805ae90040500100300e00c028010700040280000c0000280506a0d40280900a0080284700605801816002020008080000300000c0080100d02b0040d80102000a0d402835⟩,
  ⟨60,6,decodeBank 6 0x85e097cdd56cc70,decodeHints 0x7000001d0020040e9c004e00000800008230368130021b40988c118010008040080300d80b00006c0580c0180100000401c0540702c0021b01601505c0380080e01c018070e20001f87100600c0380000e01c0400704800814c240100ce0380200e024004090171181740b80100204846012024000090d500c2446a800000048030120240100906a01614035004008048058120240080900501c0380280200404807012006004008211180201080100200c46003006000001c0018030e000000000c06003006010020160160b40b00400800c058030060080100701c0380380200400c0700e00e014028030240480180500601c09012⟩,
  ⟨60,7,decodeBank 7 0x22a88e17825f3755b3,decodeHints 0x12003006100434c908000c01824080090008210021000180308008415001006004430bd010004158010005a40002200600c11169050000018000185a406000056000001690000301580c0005a40001d0020040e96904e000008000080580203200600c1901605a010018040162c4058040340100208600802c0d00b008054020130020040981502a010008040080300d80b00006c0580c0180100000400401c0104900600c2480700e0080180210c11405002056008010150040b00080105805417002002008010060040b0000000580180300200000801010004114020041620401780200800802803006150038070a800c0180500e014430450120141580500a0040081702a0e00b8010020140a80500a0000006f00c018378000000140300500a010020350160f81a8040080140580502e008010050580140280200405c16047⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56ccbc,decodeHints 0x40210100980180304c0841080800600c0016a000088018030445a8140000060000016a0000740400803a5a80e800010000020160080c801803064058168040060100200801a04c5880d0260200400417a0100200c03602c0001b01603006004000010010070041240180309201c03802006008013010040b00400805811416002010008010060040b0000000580180300200000801010004114020045d40401780200800802803006150038070a800c0180500e014028bd02205c0401102e2180b805010014028000001bc030060de0000000500c014028040080d40583e06a010020050160140b8020040141600500a0080101705811c120030062dc1082118c00c018240420843d8860020ac040010560000016a018030b50000000ac0600c034010020d201602c418040080680580b084008010450580285e8020041081602c0600140284202e0242100500a0c00b817⟩,
  ⟨60,5,decodeBank 6 0x85e0f7cdd56ccbc,decodeHints 0x803a0000680d0100100d81b018010010080580080100000c0080100405e0080881102e014000060000140203e0080140100500411c008010000300000c00802c0200b0040280102c00a02402817⟩,
  ⟨60,6,decodeBank 7 0x217825f37a9d56ccbc,decodeHints 0x803a0000680d0100100d81b0180100180804200c018006040000180405a010010080580080100000c0080100405e0080100300e0080881102e014000060000140203e008014018070060140100500411c008010000300000c00802c0200b006084018210040280102c00a02402817⟩,
  ⟨60,6,decodeBank 7 0x217825f3755b32f068,decodeHints 0x803a0000680d0100100d81b0180103606c1000080100000c008010040200082e85d12a014000060000140203e0080140100500411c008010000300000c00802c0200b01c038010800240480289500602010803000030000030080b40200300401c0100300a00c0180704200c01821⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f37add56ccbc,decodeHints 0x400304200c000030500000000803a0000200305a0100680d0100100d81b01801001b04006c0d80886010000060000180100580401600801807004008040d200400800006004008020100040b00100300e00c028050100c40280000c0000280407c0100281700a00802847006084018210020040000c0000300200b00802c2102b0040d80107b00a0c402831⟩,
  ⟨60,6,decodeBank 6 0x85e097cdd56cc68,decodeHints 0x7040001d0020040e9c104e000008000080200681300203409808010010008040080300d80b00006c0580c0180100000401c054070800021b04001502a0380080e01c018070e20001f87100600c0380000e01c0400704800814c240100ce0380200e024004090950101744a80100204804012024000090d500c2446a800000048030120240100906a01614035004008048058120240080900501c0380280200404807012006004008210100201080100200c04003006000001c1018030e080000000c06003006010020160160b40b00400800c058030060080100701c0380380200400c0700e00e014028030240480180500601c09012⟩,
  ⟨60,4,decodeBank 5 0x217846107cdeb,decodeHints 0x40040a8020020e0008050040140104701a034040040080080580207c01002005002020008080042a00130600a024029c2008c14020a8⟩,
  ⟨60,4,decodeBank 5 0x229841f37add5,decodeHints 0x60000140680d0100101f004008014000080000200280900b3280200b00803c0100002a0080280200411c0100402000805002⟩,
  ⟨60,5,decodeBank 6 0x85e1083df37add5,decodeHints 0x20e0008050000058400000c0000680d0100101f00400801402000016010008080020200280900b32c0000f000c180200b00803c0100102a0080280200411c0100060e0080100402000805002⟩
]

def nodesBlock26 : Array Node := #[
  ⟨60,5,decodeBank 6 0x85e0f7cdeb7541d,decodeHints 0x300104e0040680d0100100d81b018010008080020201482900c0300200b00803c0100102a0080100c23a00801004020008050020020e0008050000000203e0080140480500401401047⟩,
  ⟨60,5,decodeBank 6 0x85e1183df37adb3,decodeHints 0x40040a80200c004138010000080680d0100100200201600802006370010008080020200100a0053300300a00c7080200b008028008380020140100500411c0291d60e0140203e00801404805⟩,
  ⟨60,4,decodeBank 5 0x2297cdd56cc27,decodeHints 0x3606c060040320640a802004010080020520a4008050080f802005004014010470020300000000802c0200b0040280100a00a0240280f⟩,
  ⟨60,5,decodeBank 6 0x85e0f7cdd56cc27,decodeHints 0x60016120040680d0100100d81b0180100100102a0080c81901400801004020008008380020141482901e0140203e0080140100500411c008080020200000000802c0200b0040280100a00a0240280f⟩,
  ⟨60,5,decodeBank 6 0x8a60f7cdeb755b3,decodeHints 0x34068080080100580b0080040400101009d8482799c010058040160080081500400a6682700400802010004028010010700040280504ec200280407c0100280900a00802847⟩,
  ⟨60,5,decodeBank 6 0x83df37add56cce9,decodeHints 0x1b036030020000180000600401601005802000018010020080400100a0040000300000a0101f00400a0240280200a11c1380001a03404004010004008080020080a80207000400805⟩,
  ⟨60,6,decodeBank 6 0x85e0f7cdeb755b3,decodeHints 0x9a80000e80100207669827000004000040100340980101a04c040080080040200401806c0580003602c0600c0080000230a0020058100801010000801048020040be0000026900c0182f80000017c030061a60080117f00b0166980200407802c0580202a009850010021000a8150040040100200c00820800001344030060040000100202000820804008b9408010004010011a6082028010be004014008010620201c0310020040280800a014000009a0018034cf0000000280600a0140200406a02c1f0350080100280b00a694d280900a2f8029a5004008029a600a694d3047⟩,
  ⟨60,7,decodeBank 7 0x217825f37adea755b3,decodeHints 0x5f00003a0040081d17c09c000010000100400d02600406813010020020010080100601b0160000d80b01803002000008c2c0080160602004040002004120080102f80000017c030060be0000005f00c0181ac020045fe02c0586b0080101e00b01600c20003042004008210800a80180100200c5f00317c000000be0813540180000000c2000302c010020160800b4018040081ac2016b0062f80180202a009858010021000a8150040040100200c0085f0000002f8030060040000100202000820804008bac080100040100106b0e2028010be0040080380208000c0184000e01c01003004014008010620201c0310020040280800a0140000017c018030be0000000280600a0140200406a02c1f0350080100280b00a70ce180900a2f80280500600c2000700e1000180300a01c029c30040080286b00a70c35847⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cd62,decodeHints 0x803054004000030500000000104e0000b00302c00c0680d0100040d81b0180000100300e0080100105c0080100000c0080100b0280080180700601400838002014000060000140f81f0120140100500402401816006058008080020200000c000030020040040280101400a02402809⟩,
  ⟨60,7,decodeBank 7 0x2378aa17825f3755b3,decodeHints 0x438402d600c158030103180400108400400840002020210080020840082600600c13021054004018010185b0060000560000016c0000301580c0005b00002200600c1116c044000018000005b00001d0020040e96c04e00000800017358058040860100208700802c2180b0080580203200600c1901605a010018040080200681300203409808010010008040080300d80b00006c0580c0180100000410e10405002056008010070040600180303001c0380200600801015004124008010920540a802002008010060042d80000016c01803002000008010100040500200402804008002008008438410120141580500a00c0181c00e01c0e0030060140380500a004008310100e0188010020140400500a0000007f00c0183f8000000140300500a010020350160f81a8040080140580503800801005030014028020040700c047⟩,
  ⟨60,6,decodeBank 7 0x217825f3755b31a03e,decodeHints 0x209c0000d01a0200201b0360300200e0d80540700e0fc0180700e0a619c070120ba00409012122000090120a00100901201c01409001010004038000180000380405a0100380a00e0380281200a04800808002020000060000180200b00802c0100e08204801803⟩,
  ⟨60,6,decodeBank 7 0x217825f3755b31a03b,decodeHints 0x8270000340680800206c0d80c0000383601501c0383f00601c0382986701c0482e80102404848800024048280c70240480700202400404001010000060000180b40b00b0040380100e00a04802812002020008080000300000c0080100100e0040380281200a04801803⟩,
  ⟨60,6,decodeBank 7 0x217825f3755b31a011,decodeHints 0x401d0000340680800806c0d80c008038360c801c0383f00601c0382986701c0482e9120240484880002404828004024048070020240a8108080000300000c00802c0200b0040380100e00a048028120020040000c0000300200b00802c0100e0040380281200a04801803⟩,
  ⟨60,6,decodeBank 7 0x22485e097cdd56cc68,decodeHints 0x4008000180300000001007400004008020098c50180000600001c1202400e01c0200a80e01c1f80300e01c1202400e0241a8350120240204a812024244000120241a835012024038010120060580b0030060200a803000030000030060580b0030040380100e00a04801812⟩,
  ⟨60,6,decodeBank 7 0x217825f3755b332068,decodeHints 0x827000034098010180000600001c1b06400e01c1f80300e01c1202400e02417400812024244000120241a8350120240380101201000406000018000020040900382400e0d4048350120020a800803000030000030060580b0030040380100e00a048018120060580b003⟩,
  ⟨60,7,decodeBank 6 0x85e097cdd56cc68,decodeHints 0xea0003a8000ea074008010ea0743a8270ea000008001e00100400d61a04c0080d61804c040081e0010008040ea0100601b0ea02c0001b0ea02c0600c0ea010000042980380a80e2982000086c2da2000a8151e00380080e0ea0380300e0ea3880007e0ea388030060ea0380000e5ea0380800e12e120020535e21200806712e0380200e1e0048008125b82540405d5b6254008011e0048040120ea048000120ea354030910ea354000000ea048030125b4048020125b01a8058505aa1a8020045a60480581212e0480101243c0140700e0d60140100212e0480701208000c008019b2084040080d0084008011e000c040030ea00c000000ea1d40600c0ea1d4000000ea00c060030d000c020049b00580582d0d00580200446600c0580308000c010029ae01c0700e0d001c0100212e00c0700e08001c0280512e00c090120d000c0280334801c09012⟩
]

def nodesBlock27 : Array Node := #[
  ⟨60,7,decodeBank 7 0x217825f37add56cc68,decodeHints 0x3a80003a0040081d0ea09c000010000100400d02600406813010020020010080100601b0160000d80b01803002000008530008016080200406b002004780080101d4000000ea030060750000003a80c0181ac0200460002c0586b0080117c80b0160080a80229800400af702a05401001004008030020ea0000007500c01801000004008080025e4010022ec020040010040041ad0f00e0041d407005002004188080700c40080100a020028050000003a80600c1d40000000a018028050080101a80b07c0d40200400a02c0289712e0480287502425c0100200a1ac028970d611c01801002084040080420040080301000c018000001d40600c0ea0000000301800c018040080580582d02c0100200301600c2004004800c3a803006008010070d001c0380200400c3400300e0140280312e00c0180500601c34007⟩,
  ⟨60,6,decodeBank 7 0x23885e097cdd56cc68,decodeHints 0x8080100040000c0180000000104e00002004010004040010180000600001c038240020040040a8020040000300200412033802024048350050020e0008050000180000500a1a8638050040140106a08605801803002020008080000300000c05a0b40b0a60041200104800a0240286a⟩,
  ⟨60,6,decodeBank 7 0x23d85e097cdd56cc68,decodeHints 0x80100036c0e8000000740e8000080ec0980400804c0980403606c0600401c038400020042006400200400003002004010080020240484a80500a25489005000018000050080f80200500401401047084084018030540a8108700000300000c00802c0200b0040280108000a02402895⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cc68,decodeHints 0x8400020987808c04cc3c38001080004000750000883a8db0441d4140000ea000000750000740080103a1d413800002000022330080c91983b064c38530040800100200801a04c0080d026020040040020100200c03602c0001b016030060040000100104001c0604b80e0301040c00208000801015004124008010920540a802002008010060042d80000016c0180300200000801010004050020040280400800200800802840024070d201203821c0e005080014028010020c40403806200400805010014028000001fc030060fe0000000500c014028040080d40583e06a010020050160140e0020040140c00500a0080101c03011c200870060ac3a803048004008b70100202000100209004008056000000750180303a8000000ac0600c0860100223201602c3400400810c0580b04800801041030028200020040900c018048014028200380242000500a0900e01c⟩,
  ⟨60,7,decodeBank 8 0x8aa2485e097cdeb755b3,decodeHints 0xb00302c00c0400304200c0080100000c14000000030060000000200e80002c00c0b0030080100401318a0300000c00000d860032301ac6908607a054040150100000600001804009810026008018070040083d9bb0040080401500400800006004008098100040280100300e00c0280506a0d4028050100c40280000c0000280506a0d40280900a00802847⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdeb771b3,decodeHints 0x803054004000030500000000104e0001980305a00c0680d02a0042d800018000018480068d0008340020500000c0000300801302004c0100300e008010010100080100000c00801004020008050020040680180700601400838002014000060000140287707e0140480500401401063⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cde8755b3,decodeHints 0x200c1500100000c140000000041380002c00c0b00301a0340400103606c0600000605801816002020008080000300000c02002c0200400400c03802004004170020040000300200402c080020140080101400601c018050020e0008050000180000503e07c048050120140280900401401009⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f37add56ccc8,decodeHints 0x803054004000030500000000104e0000b00302c00c068130020300000c00000d868031e6004588011f000006000018040098100260080180700400800a3000400800006004008098100040280100300e00c028010700040280000c0000280506a0d40280900a0080284702c00c0b00301000406000018000020049b40683581a0f60098800206a0141a805⟩,
  ⟨60,7,decodeBank 8 0x8e22a85e097cdeb755b3,decodeHints 0x180300202004001002230380010000300600000036c14000000004138000080100b03205a020008080020300000c0001ad1908707805987016048004040010100000600001806819068064008101bc0040091881600400800815004008000060040081922e0040280100506a0d40280502c890028010700040280000c0000280506a0d40280900a00802847⟩,
  ⟨60,7,decodeBank 8 0x8f62a85e097cdeb755b3,decodeHints 0x1803002004108260540000e81d000000108220000000e81d00001009813008010648320080100981300806c0d80c0080905b840048085878210484001304004c00006000018010058040160083d84000400822821004008130400040080000600400802010004028010050620c402805042894028050620c40280000c0000280407c0100280900a00802847⟩,
  ⟨60,8,decodeBank 7 0x22a85e097cdeb755b3,decodeHints 0x800041080117a0980180364a0981082a0800040180111400045000114088018031140884502811400001800114000450001140740080111407445027114000008003660100b0043660c8018036480c80b02d0800100180417a0100400d64604c0080d64404c0400817a010008041140100601b11402c0001b11402c0600c11401000004080090018030d138e714e10d68dc01803080092700240f6108008019bf378040080d68d80080117a108040081140ac000001142280600c114228000001140ac0600c0d6068020049bb3700580b0d68d4020049b60680580b08000803802040c8401803082c8003807080008018020f60080a8020f61ec0080108ac7c0a81517a008008021140080300211422800000114228030061140080000263c00808002040c7402004638c6c080100400080200238a7116480a1140081580208001401803634c6403807630c5c018030800140380517a0140080162c0c40403862a0c40080117a0140400511401400000114228030061142280000011401403005628014020046260d40583e6240d4020046220140580504008010009114014158050400800100238a014e200504008035847⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdeb755b3,decodeHints 0x1042004130030060981082a00200c00800202000110030060888082800000c000002020000e801002074808270000040000402c010190030060c80b02d00800c020040100340980101a04c040080080040200401806c0580003602c0600c0080000202400600c2006b2d610001803048100120420020045e8080101ec008010840200402b0000008080c018404000000560300601a008010b300b01613c0200403402c0580200e008200030061000380700400c0100202a0083d8010021140a8150040040100200c00880800000404030060040000100202000810004008590080100040100106b0f40280102b0040140180308001c0384000600c0280700a014008010620201c0310020040280800a01400000202018031010000000280600a0140200406a02c1f0350080100280b00a0801000900a0ac028200040080286b00a08010047⟩,
  ⟨60,5,decodeBank 6 0x8aa097cdb3618cc,decodeHints 0x30500000686d02c0340687d0180340f1240060780f14d0000780f00d0080780700e00e00c0c81900c0002900d0ca0340281e00401c01802004018000020040340200d0120780101e0040b81a002⟩,
  ⟨60,6,decodeBank 7 0x22a85e097edf36cd86,decodeHints 0x200c1500100000c140000000041380000401c01802004c98008020040180000200800c0b00400800404004008000060040160080f1240060780f04d0020780f14d0000780f0090040780f0090080780700e00e00c1a00105c0040c81900c00005002028008050040280100281e⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981dfb755b3,decodeHints 0x803054004000030500000000104e0000200300e010020010100100200000c0100180700601c0083a002190000060000180200b0080ac0380300e00c1a00105c0040300000c000330040200501782f00601c018050020e000805000018000050080140206e00a0f80480501201402809⟩,
  ⟨60,6,decodeBank 7 0x22a85e097edd56cd6f,decodeHints 0x200c1500100000c140000000041380000601c018070020e8008dc0000180000601c038038660cc0040a866032064030660141980100200601c018050020e0008050000180000500a0f80480503c0783300900800d1c00400800404004008000060040160100a00401201002005⟩
]

def nodesBlock28 : Array Node := #[
  ⟨60,6,decodeBank 7 0x22a89217825fb755b3,decodeHints 0x200302c0100400304200c0080400000c14000000010060040000200e80000601c0180700802c0204201004c040c50000180000601c038038030cc01016004068020170080320640300001404c0100200601c018050080240200500a304188050000180000500a0240480503c07802809⟩,
  ⟨60,6,decodeBank 7 0x22a85e097edd56ccc8,decodeHints 0x200c1500100000c140000000041380000601c0180701a034008300000180000601c038038039c80044c0010320640300001404c0100200601c018050020e0008e30000180000500a0240480503c0780280900800c0b00401001002000018010058040081980a00401201002005⟩,
  ⟨60,6,decodeBank 7 0x2388aa17825fb755b3,decodeHints 0x180400201004004002230380010000100600400036c140000000041380000802c0204302c0c81682d0022bc00832000018000060cc0100c0040901200b00a0680041700103206403000014334010020080240200500a31c300050020e0008050000180000500a0240480503c07802809⟩,
  ⟨60,5,decodeBank 6 0x8aa137edf3755b3,decodeHints 0x30500000180700601c000060000180200302c010020000180100580401c0380380303206403000014050010020cc0100a00400601c018050000180000500a024048050080240200503c07802809⟩,
  ⟨60,6,decodeBank 7 0x22a825fb7e9f3755b3,decodeHints 0xc1400000601c018070000180000600200c380010020027280023e0040200302c01002000018010058040080040400401c038038030320640300001405001002068004170010cc0100a00400601c018050000180000500a02404805002020008050080240200503c07802809⟩,
  ⟨60,6,decodeBank 7 0x22a89617825f3755b3,decodeHints 0x601c0180700200c1080123e00400003050000030000000180000103a0000200302c01005804008004040040080000600401c038038030140b00100204600417001032064030000cc0101780400601c0180500a0240480500202000805000018000050080240200503c07802809⟩,
  ⟨60,6,decodeBank 6 0x8aa097cdd56cccc,decodeHints 0x7180002200600c111c60500000180001a058068af0061b45781602c0340180d01a030068e10001f47080c0180340000d01401c070180060380c00700e028018030300180c80a0000640500600c060000000140e82901401a0340a03a0ca0280680d02200c088c200e1746100300604403811022000088d700c22c6b800000044030110220100880901a0340480400804406811022c980f00501407802a1b00a0440501100200c0082600e01c1300300600403801002000001c600c018e3000000004030010020100200801a034040040080040680d002050008150140b80a81400400405002010024048010220440080900202008811⟩,
  ⟨60,6,decodeBank 7 0x22a825fb7cdd56cccc,decodeHints 0xc1400000601c018070000180000600800c0b0040080000600401a0340700e00e00c0c81900c0000501402802833004028010018070060140000600001408811012014020090080140f01e00a024008070060040000600000418001008020020010020b81a00101200400805⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cccc,decodeHints 0x2700305400c000030500000006904e0000200302c0100680d026010020000180100700e00e00c050391300280c81900c0003300405e010018070060140881102e01400006000014020090080140f01e00a0240180700601c008010000180000600802c020130280280100201201404805⟩,
  ⟨60,7,decodeBank 7 0x22a85e097edf3755b3,decodeHints 0x8210020980180304c08415001006004001020000880180304440814000006000001020000740080103a408138000020002180300634c0380716000c0184300e01c180010033a6744e7474004008309cc0c015800000408030062040000002b00c018020160088e0018036560580b00400601002008008ca800801652020040040020100200c00840800000204030060040000101b0360160101580401401c070180060380c00700e028018030140541a02c0020041601505c028008010300180c80a0000640500600c060000000145a0050140340500a04f0040280d002014ca0330140080100a2390280280200400a00c0183700e01c1b8030060140380500a004008310100e0188010020140400500a0000010200c018810000000140300500a068028090400240481a0120141000500a0100200906c024048040080141b005012c9c0f00501407802a1c00a02405009⟩,
  ⟨60,6,decodeBank 7 0x22a825f3755b35a0cc,decodeHints 0x18280000343681601a0343e80c01a038070070060640c8060001480686501a00c0380300a0000300000a0100680401a0780280a00601c01807000018000060080340200d4360280881100201c01801000018000010080340200d0020b81a0010100040080501000400808⟩,
  ⟨60,7,decodeBank 8 0x8aa17825fb7cdd56cd68,decodeHints 0x803054004000030500000000104e0000180700601c00cea002390000060000180200302c01002001010010020000180100580401c0380380306800417001032064030000140500a00a0140100a00400601c018050020e0008050000180000500a0d41a8050080d40200503c0140500300e00c038010100040400000c0000301a0560101b03643802804805⟩,
  ⟨60,6,decodeBank 7 0x22a86a17825f3755b3,decodeHints 0x180700601c008030420040400100000c1400000c000000060000040e80006600c1680301604c020041860040980103606c0600001c038038030140b001002046004160010320640300001402c1780a00601c0180500a03c0b80500205c008050000180000503e07c0480503c07802809⟩,
  ⟨60,6,decodeBank 7 0x22d8aa17825f3755b3,decodeHints 0x38030100040080800200c1300100c0000000600000c11000000004138000160c80200404a00c1900301a0340400103606c060000140600100219400c0c003068004170010320640300001402c1780a00a03c0e005006070018050020e0008050000180000503e07c0480503c07802809⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cd4c,decodeHints 0x8210020980180304c084150010060040012d000088018030444b4140000060000012d0000740080103a4b413800002000058160660c8018030640581680b00600c0580801a04c0080d0260200400b0020040980c03602c0001b016030060130000000500701c0600180e03001c0380a00600c050150680b0008010580541700a0020040c0060320280001901401803018000000050100140500580b0280401780a016028028030060dc0380706e00c0180500e014028010020c40403806200400805010014028000004b40300625a0000000500c0140283603e0240581f0120d8048050160140483603c0140501e00a0d802809014024218030060d8038079d800c0184300e01c210010020d8040089d600400842010020158000004b40300625a0000002b00c018b00360080ac058042ca0d80102b0140081b03601e0ac02805⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f3781d56cd68,decodeHints 0x803054004000030500000000104e0000200302c01002001010010020000180100b00302c00c04001010004060000180000580401c0380380306800417001032064030000140100a0040140500a00a00601c018050020e000805000018000050080d40200500a0d41a80503c0140500300e00c038010100040400000c00003036008068b002b00400807805⟩
]

def nodesBlock29 : Array Node := #[
  ⟨60,6,decodeBank 7 0x22a8921c825f3755b3,decodeHints 0x80302c0040180700601c008080020680000305000000001018000030000000180b00302c00c0200401004c040c50180000600001c0380380304600416001068020010020320640300001404c1780a00601c018050020d40080500a0240b8050000180000500a0d41a80503c0780280a⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cd5e,decodeHints 0x803042004000030500000000103a0001980305a00c0680d0100040d81b0180000700e00e00c1180105c0040c81900c0000500b0ec0280180700601400808002014000060000140f81f0120140f01e00a0240180700601c0080800202000006000018020040580280100201e0140b805⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cc6e,decodeHints 0x80704c004000070500000000103a0000200705a010020010260100d81b0180100700e00e028118010580040c81900c0000500405e0100901203801400817002014000060000140203e0080140f01e00a02801803002020008260000180000600802c0200b058028010020120140b805⟩,
  ⟨60,7,decodeBank 7 0x22a87217825f3755b3,decodeHints 0x120030073b80380716e00c0182400e01c008210023900180306c084108010060041b045010004158010005b80002200600c1116e0500000180000c5b8030000560000016e000018158060005b80001d0020040e96e03a000008000080580203200600c1901605a010018040173b4058040340100223a00802c0d00b0083900201300200409b2c026010008040080300d80b00006c0580c0180100000401401c070180060380c00700e028018030141140502c0840b01607b0040282100201471c1182c00200416045058028008010300180c80a0000640500600c06000000014040050140080100a01005e0280200400a00c0185400e01c2a0030060140380500a0c0028170840240b83002e0142100500a0040081706c05c0b8010020147200500a0000006f00c018378000000140300500a010020350160f81a8040080140580502e1140f00501407802a1d00a05c0500a⟩,
  ⟨60,7,decodeBank 8 0x8aa1c85e097cdd56cd68,decodeHints 0x180700601c008030420040400100000c1400000c000000060000040e80000800c168040160100200b0080040980403606c0600401c038038030140b01600a01400416001032064030000140101780400601c0180500a0c4188050020c400805000018000050080f80200503c0140500300e00c038420560041b1c70000180000600802c0200b43a0280b805⟩,
  ⟨60,6,decodeBank 7 0x22a85e097e1f3755b3,decodeHints 0x2700305400c000030500000006904e0000180700601c0411f002004000060000180200302c010020c3010010020000180100580401c038038030680201700803206403000014050010020cc0100a00400601c018050220440b8050000180000500a024048050080240200503c07802809⟩,
  ⟨60,6,decodeBank 7 0x22a825f3755b332098,decodeHints 0x30500000686d02c0340687d0180340700e00e00c0c81900c0002900d0ca0340885d0060440888b0000440880d06a0440f01e00a0440400311800c060000180000200d0100b81a0080100448c81100201c01801000018000010020346180d004008048110020208f801⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cc98,decodeHints 0x402109c0980180304c0841500800600c0016f000088018030445bc140000060000016f0000740406903a5bc13800010000020160080c801803064058168040060100200801a04ce400d026020040041c80100200c03602c0001b016030060040000100500701c0600180e03001c0380a00600c050150680b0040080580541700a0100200c006032028000190140180301800000005010014050020040280401780a00801002803006150038070a800c0180500e014028e402205c0401102e0d80b805010014028000001bc030060de0000000500c014028040080d40583e06a010020050160140b84503c0140501e00a0d802817014028120030061c4038070e200c0182400e01c228360020ac040010560000016f00c018b78000000ac030060340100203601602e778040080680580b17a0d80102b014008228450120ac02805⟩,
  ⟨60,6,decodeBank 7 0x2388c217825f3755b3,decodeHints 0x180700610c008030100040400100202000003018000030000000180000104e0000200402c0c81682d010004040010180000600019400c0c0030901200100206800417001032064030000143343b00a0060d40180500a0240e0050020e0008050000180000500a0d41a80503c0780280a⟩,
  ⟨60,7,decodeBank 7 0x2308aa17825f3755b3,decodeHints 0x1b04100e00c158030101c404001048004008b7002020120080021c40082600600c1303604c0040180100c5c00300005600000170000018158060005c00002200600c11170044000018000005c00001d0020040e97004e0000080001634c05804086010020b000802c2180b0088e00203200600c1932d064010018040080200681300203409808010010008040080300d80b00006c0580c01801000004014104050180480600c040004028120020141c46501800600c0c041030028018030140541a02c0020041601505c028008010300180c80a0000640500600c06000000014040050140080100a01005e0280200400a0900281c0400240e0240380143880500a00c0181c06c0700e0030060143880500a004008310100e0188010020140400500a0000007f00c0183f8000000140300500a010020350160f81a804008014058050381040f0050140780286800a0700500a⟩,
  ⟨60,7,decodeBank 8 0x8c22a85e097cdd56cd68,decodeHints 0x38030100040080800200c1300100c0000000600000c11000000004138000160100200b00800c1900401a0340400403606c060040140600c00a01400c0c00306800417001032064030000140101780400a080208050060d8018050020e000805000018000050080f80200503c0140502405600c1b071002020008080000180000600802c0200b0d00280e005⟩,
  ⟨60,5,decodeBank 6 0x8aa097cdd56ccc9,decodeHints 0x1c1400001a1b40b00d01a1f40600d01c0380380a032064030000a40343280d0220486a01102222c000110220340201103c0780281100201c01801000018000010080340200d0020b80100201204400811⟩,
  ⟨60,6,decodeBank 7 0x22a85e097d5f3755b3,decodeHints 0x807054004000070500000000104e0000b00700600c00cf00020c0000060000180202502c01002001010010020000180100580401c0380380a0680041700103206403000014050010020cc0100a0040240480e0050020e0008050000180000500a024048050080240200503c07802809⟩,
  ⟨60,6,decodeBank 7 0x22a86217825f3755b3,decodeHints 0x1080700600c008de0420040400100001c1400000c000000060000040e80000801c168040160100200b0080040980403606c0600401c0380380a0140b0010020460041600103206403000014010178040240480e00500a0240b80500205c00805000018000050080f80200503c0780280a⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cc3e,decodeHints 0x8210020980380704c0841500100e00400171000088038070445c41400000e000001710000740080103a5c413800002000020160080c8038070640581680400e0100200801a04c0080d026020040040020100200c03602c0001b016030060040000100500701c0604b80e03001c0380a0e2028050150680b0008010580541700a0020040c006032028000190140180301800000005010014050020040280401780a00801002871024070038120380d80e00500e014028010020c40403806200400805010014028000001fc030060fe0000000500c014028040080d40583e06a010020050160140e04103c0140501e00a1a00281c014028208360060ac038030840040087101002279001002108040080560000017100c018b88000000ac030060860100203601602e7880400810c0580b0801a00102b014008208410120ac02805⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdb361968,decodeHints 0x8210020980180304c0841500100600400172000088018030445c814000006000001720000740080103a5c813800002000020160080c801803064058168040060100200801a04c0080d026020040040020100200c03602c0001b016030060040000100f00303c8ec0392447600c0181e00e0780f00103c3300404d1980040081e0100780f00003ccb80314d65c0000001e00c0780f00403c130058dd0980100201e0160780500701c0600180e03001c0380a00600c050150680b0008010580541700a0020040c006032028000190140180301800000005010014050020040280401780a0080103582000a0280f01e00400c0104100e01c20803006008038020040040104501002022801002008040020040000117200c018b9000000008030020040100103601602d93804008008058020400800480203c0781006b0d600805002⟩
]

def nodesBlock30 : Array Node := #[
  ⟨60,6,decodeBank 7 0x22a825f3755b35a0ce,decodeHints 0x18280000343681601a0343e80c01a038070070060640c8060001480686501a00c038030700000300000c0100680401a1341c00a00601c01807000018000060080340200d0040080881100201c01801000018000010080340200d0020b81a00100a0040083801000400808⟩,
  ⟨60,7,decodeBank 8 0x8aa17826027cdd56cd68,decodeHints 0x200c1500100000c140000000041380000601c01807002cbc008e40000180000600800c0b00400800404004008000060040160100700e00e00c1a00105c0040c81900c00005014028028050040280100180700601c0080800202000006000018028050080d41f84c06a0280180700601c00808002020000060000196402b0080d80201a00400804809⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f3755b364168,decodeHints 0x200c1500100000c140000000041380000800c0b004008004040040080000600401c0380380306800417001032064030000140100a00400601c018050020e0008050000180000507c0100281e00a0280b00302c00c0400101000406000018000058040280280a00a06a0140180700601c0080800202000006000018020360080680100201e0156302b⟩,
  ⟨60,7,decodeBank 8 0x8aa2185e097cdd56cd68,decodeHints 0x601c0180700200c1080101000400003050000030000000180000103a0000200305a0100580400802c020010260100d81b0180100700e00e00c0502c058028050010580040c81900c0000500405e0100180700601c028050020c42b00000c00003004016010058cc0620280180700601c2102b0020d80087b0000180000600802c0200b0040080b817⟩,
  ⟨60,6,decodeBank 7 0x2388d217825f375568,decodeHints 0x1807006014008030100041c00100201400003018000030000000140000104e0000200406a0141a805010004040010180000600001400c5900303c0780280a06800417001032064030000153ccd180a006070018fa0120140080800202000006000018688d10c007001002⟩,
  ⟨60,7,decodeBank 7 0x2348aa17825f375568,decodeHints 0x1b04100e00c028030100c41c00100a00400831002020028050021c40082600600c1303604c0040180100c5cc0300000a00000173000018028050005cc0002200600c11173044000018000005cc0001d0020040e97304e000008000160d41f00400a0100203500802c028050093d00203200600c1923c064010018040080200681300203409808010010008040080300d80b00006c0580c018010000040140140f0180400780c00500a0281000a0141c40501800600c0c041164028018030140541a02c0020041601505c028008010300180c80a0000640500600c06000000014040050140080100a01005e028020040821040481c00a014120030060701b01c03800c018240e21800e001002150040080a80040081c0100200e0000001fc030060fe0000001c00c0180e0040080dc0580b06e0100201c01602c2006800407005002⟩,
  ⟨60,7,decodeBank 8 0x8d22a85e097cdd56cd68,decodeHints 0xe00c040010020200080304c00403000000018000030440000000104e0000580400802c020030640100680d0100100d81b018010050180300280500303000c1a00105c0040c81900c0000500405e010028050060d8388010100040400000c0000300401601005a3b0d00282082b0060d801824002020008080000180000600802c0200b0040080e01c⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd55a054,decodeHints 0x20840082600e01c13021054004038010005d00002200e01c11174050000038000005d00001d0020040e97404e000008000080580203200e01c1901605a010038040080200681300203409808010010008040080300d80b00006c0580c0180100000401401c0701812e0380c00700e0283880a0140541a02c0020041601505c028008010300180c80a0000640500600c06000000014040050140080100a01005e028020040481c40901c00e0480e03603809003807038004008540100202a001002070040080380000007f00c0183f800000070030060380100203701602c1b8040080700580b0801a00101c014008208360060140380300a004008310100e0188010020140400500a0000017400c018ba0000000140300500a010020350160f81a804008014058050401040f0050140780286800a0800500a00a09002820038024388240480140e005⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd565168,decodeHints 0x200c1500100000c140000000041380000800c16804008004040040080000600403c4900381e03c1341701e03c5340301e03c3741781e00a00c0380300a0041c00100a0000300000a0101f0040140780281e02404801807022044008080520a40000603e07c0200f00407804805⟩,
  ⟨60,7,decodeBank 8 0x8aa17826077cdd56cd68,decodeHints 0x803054004000030500000000104e0000380300e00c040010100040300000c0001980305a00c1d0010100042d8000180000200400e00c038030680041700100c000030000140280801405e00c0380300a0041c00100a0000300000acc00280506c0141f03f00a1300281400601c0180700202000808000018000060340d82781a0340411c8102c805004805⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56e568,decodeHints 0x200c1500100000c140000000041380000800c16804008004040040080000600401c038038030980040a801032064030000140102b80400601c018050020e000805000018000050080f80200503c0780280a00601c0180700202000809000018000060080240201000400807805⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f3755b35bd68,decodeHints 0x803054004000030500000000104e0001980305a00c1d0010100042d8000180000700e00e00c0a80102a0040c81900c000e481001400c0380300a0041c00100a0000300000a0141f03f00a0780280a0e200d1e80301000404001018000060000080100a00a06c0159880500601c01807002020008080000180000603404194010004008048050340d8b401a⟩,
  ⟨60,7,decodeBank 8 0x8aa2485e097cdd56cd68,decodeHints 0xb00302c00c0400304200c0080100000c14000000030060000000200e80002c00c0b0030080100401318a0300000c000038070070060281602c0140d00402e0100640c8060000280982f01400c0380300a0141a83500a0140403100a0000300000a0141a83500a0780280a00601c0180707a0d91d03d394021960080000180000603404d9481300400804805⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cd6a,decodeHints 0x200c1500100000c140000000041380000800c0b00401a034098040080000600401c038038030140044c001032064030000cc0101780400601c018050020e000805000018000050080240200503c0780280900601c0180700247c008080000180000600802c020130280280100201201404805⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f3755b35a0c8,decodeHints 0x803054004000030500000000104e0000b00302c00c068130020300000c00003807007006028008980020640c8060000280982f01400c0380300a0041c00100a0000300000a0141a83500a0780280a00601c01807002720008f80000180000603404d950130040080480502c00c0b00301000406000018000020040280280a00a06a0141a80506c06a7a81a⟩,
  ⟨60,7,decodeBank 8 0x8e22a85e097cdd56cd68,decodeHints 0x180300202004001002230380010000300600000036c14000000004138000080100b03205a020008080020300000c0000280c018014120240160140d00082e0020640c806000028668760140141a83500a0140b23c00a0041c00100a0000300000a0141a83500a0780280a0780d85803c0480599681600202000808000018000060340c99583200400804805⟩
]

def nodesBlock31 : Array Node := #[
  ⟨60,8,decodeBank 7 0x22a85e097cdd56cd68,decodeHints 0xe2004108011c80980180306c0981082a0e2004018010f40003d0000f4088018030f40883d0280f4000018000f40003d0000f4074008010f40743d0270f40000080047a0100b00447a0c80180367c0c80b02d0e2010018041c80100400d67a04c0080d67804c040081c8010008040f40100601b0f402c0001b0f402c0600c0f4010000040e20280380e0400600180e082060038070e20280180329c0280a83429c0b00080108a0b00a82e1c8028008010f4060030190f4028000190f4028030060f4060000006760280800a040050020046740500802f040028020040e20140180306cce403807670cdc018030e2014038051c80140080106c0c40403866c0c4008011c8014040050f4014000000f41e8030060f41e8000000f40140300566a0140200406c0d40583e6680d40200406c014058050400819981e38a014e20050400800500a0e20900180306c900038079f93ec018030e2090038071c81080080106c8fc040089f53e40080129c108040080f40ac000000f41e8030060f41e8000000f40ac030069f00680200406c8f80580b9ef3d80200406c0680580b38acc8e20020f40ac05002040080100090f40ac02805⟩,
  ⟨60,6,decodeBank 7 0x22a85e097f5d56cd90,decodeHints 0x200c1500100000c140000000041380000800c03804008004040040080000300400400c0380200400417002004000030020040100a0020240480183e0220440083e0520a40003e03e07c0200503c0780107706600c16803074004040010b6000060000160100a00205e0080483e⟩,
  ⟨60,7,decodeBank 7 0x22a85e097f5f3755b3,decodeHints 0x8210020980180304c08415001006004001030000880180304440c14000006000001030000740080103a40c138000020002180700e1040180308201c0384300600c180080101140080108a020040300020041580600c40c000002060180302b000000080160673f8018030820581681000600da000807404000801020020043400020040800c0b640c0000020603006010000000100200080401580400401c0101400600c0a00700e00801802004054014fd0020042281505c00800802004018011030000008180600c00800002004068010140400280a01a02800810002004040010140400500a01005e0081000201200c0901c00e0480e00300602403807012004088170100440b801002024040090120001480f00c0a4078000000240300601e59c078090340240484f00a03c0d00501ecfc1f0090200f80484f01203c0800f0120080f0350280781a8020040240a009⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cde76cd86,decodeHints 0x40182a00200001828000000008270000cc0182d0060340680800206c0d80c000008018070040080081500400800006004008020100040480900300e044088010100a41480000c03c0586e01e0780100f00e00c0380302a0040a80100c0000300002002c0800b01400802805⟩,
  ⟨60,6,decodeBank 7 0x22a85e0b7cdd56cd86,decodeHints 0x40182a00200001828000000008270000cc0182d0060340680800206c0d80c000008018070040080081500400800006004008058100040480900300e044088010100a41480000c29c5386e01e0780100f00e00c0380302a0040a80100c0000300002002c0800b01400802805⟩,
  ⟨60,6,decodeBank 7 0x22a87e097cdd56cd86,decodeHints 0x40182a00200001828000000008270000cc0182d0060340680800206c0d80c000008018070040080081500400800006004008058100040480900300e044088010100a41480000c03c0586e01e0780100f00e00c0380302a0040a80100c0000300002002c0800b01400802805⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f3755b36b986,decodeHints 0x200c1500100000c140000000041380006600c1680301a0340400103606c0600000400c038020040040a8020040000300200402c0800202404801807022044008080520a40000601e02c3701e00403c8280348400c820016840044780068200002004040009208020120240380300e00c0a80102a0040300000c0000800b02002c0500200a0156b82b⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981e026cd86,decodeHints 0x803054004000030500000000104e0000100300e008010010100080100000c0080180700601c0083a00290c000060000180100b0040800180700601c0095800215c00006000018010570041b80785700e00c038030680041700100c000030000140080801405e0bc1f857⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdb361972,decodeHints 0x200c1500100000c140000000041380000800c16804008004040040080000600403c4900181e03c1340081e03c5340001e03c3740201e01c0380380302a0040a801032064030000140100800400a0780100700600801015002008010060000080100b0080080481e0040780a002⟩,
  ⟨60,6,decodeBank 7 0x22a825f3755b3618ce,decodeHints 0x18280000343681601a0343e80c01a00801807004008000060040080683a01a0442e80302204445800022044068040221340101100e00c0380300c000030000740341d00d0140081c01100201c01801000018000010080340200d00405401001012044008110020540a801⟩,
  ⟨60,7,decodeBank 8 0x8aa17826027cdd56cd86,decodeHints 0x803054004000030500000000104e0000180700601c00b44002410000060000180200302c01002001010010020000180100580400400c038020040040a80200400003002686008010200040112200200601c01807002020008090000180000601e024020090dc1300100900e00c0380302a0040a80100c000030000340802781a034010278040140081a809⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f3755b361952,decodeHints 0x200c1500100000c140000000041380006600c1680301a0340400103606c0600000400c038020040040a8020040000300200402c0800200601c01807002020008090000180000603e0240584c0040240380300e00c0a80102a0040300000c0000800b02002c0500206a0240180700601c0080800202000006000018020040040d80102001e0256802b⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cde26cd86,decodeHints 0x200c1500100000c140000000041380000800c16804008004040040080000600400400c03802004004040020040000300200401008002024048018070220440084c0520a40000603e07c0205703c0780100900e00c038030680041700100c000030000200101780401400802805⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981db364186,decodeHints 0x200c1500100000c140000000041380000400c03802004004040020040000300202404801807022044008080520a40000603c0780100f06600c16803074004040010b6000060000160082b85700e00c038030680041700100c00003000014008028050200501782f⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f3755b364186,decodeHints 0x803054004000030500000000104e0000200302c01002001010010020000180100100300e0080100102a0080100000c0080100448a0080901200601c08811002020148290000180f80401e0780100f02c00c0b00301000404001018000060000160101000268a0080480900e00c0380302a0040a80100c000030000340119f80401400802805034080b381a⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981df36e1b3,decodeHints 0x200c1500100000c140000000041380001c03803803010004040010320640300006600c16803074004040010b6000060003920282c00309000c04001010004060000180000100205e0bc0a01002404801807022044008090520a40000601e0240480f01e0242b85700a0140480f⟩
]

def nodesBlock32 : Array Node := #[
  ⟨60,7,decodeBank 7 0x22a85e0981df36cd86,decodeHints 0x8210020980180304c08415001006004001060000880180304441814000006000001060000740080103a41813800002000010070041040180308201c03802006008010080041140080108a02004002002008010060044180000020c0180300200000808016067400018030820581681000600d2180807404000801020020042430020040800c0b64180000020c03006010000000100200080400100201200c0901c00e0480e00300602403807012004088170100440b801002024040090120001480f00c0a4078000000240300601e0080f00906c0780480200403c1b00f01e9140780902002404a440ae03c080570b001c0381400600c0a00700e160018030280541a0cf0020046781505c05000801028018031060000008300600c050000009fe080050140040080d010020050100140280401781a0400bcb202000a05004805⟩,
  ⟨60,8,decodeBank 7 0x22a85e097cdd56cd86,decodeHints 0x20a00410801208098018030820981082a20a0040180111e0004780011e0880180311e0884782811e0000180011e0004780011e0740080111e0744782711e000008004840100b0044840c8018030820c80b02d20a010018042080100400d08a04c0080d08a04c040082080100080411e0100601b11e02c0001b11e02c0600c11e0100000420a00803802040080018030401040380720a008018023960080a80239672c008010401140a8152080080080211e0080300211e23c0000011e23c0300611e008000020400080800204008002004040d28080100400080200220a02401812082070038120820700180320a024038072080240081108a05c0401108a05c008012080240400911e0240002911e03c0302911e03c0000011e0240300669203c0201f6900240581f68e0240200468c03c0580f0400819981e040080010020400241000920a09003807040080018030401040380720a090018032080c00a815396108008010401080a8152080c00080111e0ac0300611e23c0000011e23c0300611e0ac00000040068080100400800200404140408010040068020040400801000a11e0ac01002040cc81000511e0ac04805⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cd52,decodeHints 0x1042004130030060981082a00200c0080025c000110030060889702800000c0000025c0000e801002074970270000040000b02c0cc190030060c80b02d01600c0180b0100340980101a04c040080160040081301806c0580003602c0600c0260000000200e0380c00301c0600380700400c0100202a008160010020b00a82e0040040100200c0640500003202803006004000010020200080a00b0160500802f00402c0100900600c1b80700e0dc0180301201c038090020041e8080100f400801012020048090000009700600c4b8000000120180301a03407c0484f0120680580b012008010350141301a8020040240500908600c0183c00e01c1e00300610c038070600040083d0100201e8010020c0040080560000012e00c018970000000ac0300603413c0202b016010100020040d80500a2ca008010200140280d01a00a0ac04805⟩,
  ⟨60,7,decodeBank 6 0x8aa17825f379db3,decodeHints 0x1960041080129e098018030780981082a19600401801120000480001200880180312008848028120000018001200004800012007400801120074480271200000080069602c0b0336960c8018030340c80b02d19602c0180329e02c0400d03404c0080d03404c0400829e02c0080112004c0601b12002c0001b12002c0600c12004c000001960080380e0780600180e07806003807196008018023980080a80207a0b00080107a0b00a82e29e008008021200080301912002800019120028030061200080000203400808002034050058040340500802f034008058021960140181207807003812078070018031960140380529e0140081107a05c0401107a05c0080129e014040051200140002912003c0302912003c00000120014030050340140d00503411c0587703411c2783f0340140580548203c0101e06c0140501e3420140100206c03c0500f⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cde7755b3,decodeHints 0x8210020980180304c08415001006004000900000880180304424014000006000000900000740080103a24013800002000058160660c8018030640581680b00600c0580801a04c0080d0260200400b0020040980c03602c0001b016030060130000001200700e0f00180307801c0382400600c2101502a0f40080107a0540a8420020041580600c240000001200180302b0000000d010008068058040340400801a01602c6580700e0f00180307801c038cb00600ce601502a7300080107a0540a94f0020044800600c24000000120018030900000000d0100200680580b0340400801a01602c0d01a0042401580200a00c0901c00e0480e0030060140380500a004088170100440b8010020140400500a0001480f00c0a4078000000140300500a068028350160f81a84f07e0140580501e0800480506c0140282000a03c1b00f01e9040780506c014029a100a03c1b047⟩,
  ⟨60,7,decodeBank 6 0x8aa17825f36cd8b,decodeHints 0x2a2004108012a0098018030780981082a2a2004018011700005c000170088018031700885c028170000018001700005c000170074008011700745c027170000008006980100b0046980c8018030340c80b02d2a2010018042a00100400d03404c0080d03404c040082a0010008041700100601b17002c0001b17002c0600c170010000042a20140181207807003812078070018032a2014038052a00140081107a05c0401107a05c008012a0014040051700140002917003c0302917003c00000170014030050340140201f0340240581f03402402004034014058052a20080380e0400600180e040060038072a2008018022a00080a802a040b0008010400b00a82e2a0008008021700080301917002800019170028030061700080000203400808002034050020040340500802f034008020020400280281e0400080481e0400080280204002804809⟩,
  ⟨60,7,decodeBank 6 0x8aa1782df3755b3,decodeHints 0x1f60041080125e098018030780981082a1f6004018011f60001e000078088018030780882d0281f60000180025e0001e80007a0740080107a0742d02725e0000080069c02c0b03369c0c8018030340c80b02d1f602c0180325e02c0400d03404c0080d03404c0400825e02c0080110804c0601b03402c0001b10802c0600c10804c000001f60080380e0780600180e078060038071f60080180269a0080a80269a0b00080107a0b00a82e25e008008020b4008030190b4028000190b4028030060b400800002034008080020340500580b0340500802f034008058021f60140181207807003812078070018031f60140380525e0140081107a05c0401107a05c0080125e014040051080140002906c03c0302910803c00000108014030050340140d005034068058a70340682783f1080140580568203c0101e06c0140501e5a20140100206c03c0500f⟩,
  ⟨60,7,decodeBank 6 0x8aa1f825f3755b3,decodeHints 0x196004108011f2098018030780981082a196004018011720005c800172088018031720885c828172000018001720005c800172074008011720745c8271720000080069e02c0b03369e0c8018030340c80b02d19602c018031f202c0400d03404c0080d03404c0400803402c0080117204c0601b17202c0001b17202c0600c17204c000001960080380e0780600180e078060038071960080180207a0080a8023980b00080107a0b00a82e07a0080080217200803019172028000191720280300617200800002034008080020340500580b0340500802f03400805802196014018120780700381207807001803196014038051f20140081107a05c0401107a05c0080107a014040051720140002917203c0302917203c00000172014030050340140d0050340680580b0340682783f0340140580568403c0101e06c0140501e5a40140100206c03c0500f⟩,
  ⟨60,8,decodeBank 7 0x22a85e097cdd56cdae,decodeHints 0x1f8004108011f2098018030780981082a1f800401801108000420001080880180310808842028108000018001080004200010807400801108074420271080000080048c02c0b03348c0c8018030340c80b02d1f802c018031f202c0400d03404c0080d03404c040081f202c0080110804c0601b10802c0001b10802c0600c10804c000001f80080380e0780600180e078060038071f8008018026a20080a8026a20b00080107a0b00a82e1f20080080210800803019108028000191080280300610800800002034008080020340500580b0340500802f034008058021f80140181207807003812078070018031f8014038051f20140081107a05c0401107a05c008011f2014040051080140002910803c0302910803c00000108014030050340140d0050340680580b0340682783f68c03c0101e06c0140501e6220140100206c03c0500f1f80900d02448c10c0180303410c0d0431f8090018031f20c00d030034068008010340f40d5071f20c0008011080ac4202b108210000001082100d5061080ac000000340680d0041080ac058040340800d505034068010020354100d50303406801002034d400d0091080ac02805⟩,
  ⟨60,5,decodeBank 6 0x85e09809d56cc66,decodeHints 0x104e0000680d00202c0d81b0000180706c02a0380707e00c0380705300403800808002024000060000180f81f0040380100e008020008040080300000400e010020070040380100e00e01002007⟩,
  ⟨60,6,decodeBank 7 0x22a85e09809de755b3,decodeHints 0x200c1500100000c140000000041380000601c0180701a0340080b03606c0000600891c0180400802000804008030000040200100200b00400c038020040040a802004000030020200080100b0140080180700601c00808002024000060000180f81f0080fc020090040fc01009⟩,
  ⟨60,6,decodeBank 7 0x22e8aa1782602755b3,decodeHints 0xe010040040020100080304c00403004000010000030440000000104e0000203200802c0183200602c0680d00202c0d81b00001805002004010010030300080100105c0080c81900c008050020040280203f0080240186e00602400808002024000060000180f81f00413001009⟩,
  ⟨60,7,decodeBank 7 0x22a85e09809d56cd52,decodeHints 0x8210020980180304c0841500100600400130000088018030444c014000006000001300000740080103a4c013800002000058030060c80380706400c0180b00e01c0580101a04c2780d0260040080b09e02c0980003602c0301b0160000001300c0180100701c0600180e03001c03802006008010150040b0008010580541700200200801006032028000190140180300200000805010014008058020040400100a016028048030060dc0380706e00c0180900e01c048010020d80400810600400809010024048000004c0030062600000000900c0180d01a03e0240581f012008010350141301a8020040240500900800c0203600e01d24803006010038040080040203601002041801002010040040080000213000c018980000000100300403406815804016010020020040d80500a490008010040140100d01a07e01004804⟩,
  ⟨60,6,decodeBank 7 0x22a825f3755b3548ce,decodeHints 0x18280000343681601a0343e80c01a038070070040640c8060041480686501a00c0380300e0000300000c4940480d0041300100900601c01807000018000060080340100a0040280881100201c01801000018000010020340400d0040b8010010120040080801000400808⟩,
  ⟨60,7,decodeBank 8 0x8aa17826027cdd56cd52,decodeHints 0x10060a8008000060a00000000209c0000300e00c038014940043900000c00003016006058018080020200080c0000300000b01c0380380200400417002032064030020140080100a0040500a00200601c0180700202000809000018000060340240d01a0041300100900601c0180700202000808000018000060560100100a0040280d009⟩,
  ⟨60,5,decodeBank 6 0x8aa228860981e02,decodeHints 0x200c0380100601c0180700215c0080900000c140000000040300000c0000000600800c0380400400816004012010025080080000300400601c0180700205c009ad00a014048640000180000600802c02017⟩
]

def nodesBlock33 : Array Node := #[
  ⟨60,5,decodeBank 6 0x8aa2788609809d5,decodeHints 0x200300e0100180700601c020090081b8000030500000000400c010030000000180180700601c0200b0083d402805012314000060000180380300e00c010020ae15c1f80900c000030001742e82b0ac⟩,
  ⟨60,6,decodeBank 7 0x22a8861782607809d5,decodeHints 0x601c0180700200c1080101000400003050000030000000180000103a0000200300e010048040081b80200134e0100200000c0100180700601c0280501219000817002158000060000180200b00805c0380300e00c2b85707e0240a00139a0040300000c0000100206205c18817⟩,
  ⟨60,6,decodeBank 7 0x22a88a21826027cdd5,decodeHints 0x200c0380100601c018070020200080900000c140000000040300000c0000000600601c0180700205c008f500a014048300000180000600800c0b004008004d38040120100203f008000060040160100380300e00c0100206a0241a80900c000030001742e82b017058010e6804⟩,
  ⟨60,6,decodeBank 6 0x8aa2488609809d5,decodeHints 0x80580204400600c2201602c0100180401200c0183700e01c1b803006024038070340100200906c02404804008069aa03f0005d40002200600c11175050000018000005d40000c008010061750180000200400c5d403000012000001750000180480615800c01b5300e01da98030062b003807060010020ac06c02c560040080c022056060024028ac034014560090120c0220c51580000035200c019a90000002b00300600401c070180060380c00700e008018020040f40102c008010161a7058008020020140d42600201200801035004028048090040180c80a0000640500600c008000020146a005002158008011a80040285600a⟩,
  ⟨60,6,decodeBank 7 0x23d8aa21826027cdd5,decodeHints 0x600400808002024048370540240000103a0000002104400003000000018008170021580b91217605c028050120c0000060000180200108801002021088010048040080fc0200001801005804004004160020042001080209800801009032064030020140080100a0040100a002⟩,
  ⟨60,7,decodeBank 7 0x22a88617826027cdd5,decodeHints 0x1200c0183700e01c1b803006024038070020840084400600d27021042004018011621100400101200400131000088018030444c4140000060000313100c000048000004c400006012018001310000740080103a4c40e8000020000b803006150038070a800c0181700e01c1800900a05c0d00502e024048300880c01800100205c4181702e004008300881580b8000001bc030060de0000001700c01802016009428018030880580b004006010418090120100d0040080240203d0340fc02044008110008010880f5268040020100200c0084c400000262030060040000104183d0160100b80400401c070180060380c00700e008018020140d42600201200801035004028048090054240102c0020041624c058008008020040180c80a0000640500600c008000020140c40500202e008010310040280b80a0040f4010140080100a24b02800802002⟩,
  ⟨60,6,decodeBank 7 0x22a8922182602755b3,decodeHints 0x800c0b00400601c018070080200201a00000c140000000100600400c0000000600601c0180700802c0203001004c040c50000180000601c038038020040101600206800801008032064030020140080100a00601c018070080d8020e301202400006000018560ac0040280100a⟩,
  ⟨60,7,decodeBank 8 0x8aa2185e09809f3755b3,decodeHints 0x180700601c008030420040400100000c1400000c000000060000040e80000601c0180706006822030002218008300000180000600800c0b00409e0100201a00800527804008000060040160100700e00e00805002004028010010580080c81900c00805002004028010040280080180700601c048090022c42200000c0000301702e01041b540040280100a⟩,
  ⟨60,5,decodeBank 6 0x8aa09809d533cb7,decodeHints 0x30500000885d0060440888b0000443606c00e00c2c85900c000268110c60440200300e0100200000c01005811008044010022b001000807006004000060000040281100215c1180100802402001⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981e02754b7,decodeHints 0x2700305400c000030500000006904e0000200300e010022501820100200000c0100180700601c08811010190000060000180200b00805c0380300e00cac1583520200300000c0000100206205c1881700601c0180700200400006000018020090081b8028050ae15c1f809⟩,
  ⟨60,6,decodeBank 6 0x8aa09809d5320b7,decodeHints 0x5d80002200600c111760500000180002200c088c200e1746100300604403811022000088d700c22c6b8000000440301100401c070180060380c00700e008018020040180c80a0000640500600c008000020140e02680202204401038004028088110080580235500600daa816a1a0100180400803002176000000bb00c0180100000410625805804022044020140086a401002352050ac004004008008030020dc0380706e00c0180100e004008000005d8030062ec0000000100c0068650b00a00408811002008010350141301a80200400405001002010020091820240480400800460801⟩,
  ⟨60,7,decodeBank 7 0x22a85e09809f3754b7,decodeHints 0x402109c0980180304c0841500800600c00132000088018030444c814000006000001320000740406903a4c8138000100000b803006150038070a800c0181700e01c1800802205c4181102e020040300880c00b8000001bc030060de0000001700c01802016009438018030880580b004006010020080081104b252088020608040880100200c0084c800000264030060040000101b03d0160100b80400401c070180060380c00700e008018020040540102c0100201601505c008040020040180c80a0000640500600c008000020140c40500202e008010310040280b80a0040f4010140080100a2510280080200201200c0183700e01c1b803006024038070882c400809010004048000004c8030062640000000900c0181e83d00a0240b8050340100200906c02404804008069ab03f012008010350141301a80200402405009⟩,
  ⟨60,6,decodeBank 7 0x22a82602755b3320b7,decodeHints 0xc1400001a1b40180d01a1f40000d01c03803802032064030020a40340100d00601c01807000018000060220440100a00402802003118010020000180100580d0080081a002010010020c100201c0180100001800001a1e0340100a0040047180100802002001⟩,
  ⟨60,6,decodeBank 7 0x22a825f3755b3338b7,decodeHints 0x18280000343681601a0343e80c01a038070070040640c8060041480686501a0442e80302204445800022044068040220442680202200c0380300e0000300000c0100680401a008170020100200891900601c01807000018000060080340200d0040280100a01204400801⟩,
  ⟨60,7,decodeBank 8 0x8aa17826027cdd56ccb7,decodeHints 0x9c00c1500300000c140000001a41380000601c018070106a8040300000180000600800c0b00400894c04004008000060040160100700e00e0080100805c0080c81900c00805002004028010040280080180700601c8c8b10100000300000c05c0b80406cd580100a0040280180700601c008010000180000607a0ac020360080680100a00402804809⟩,
  ⟨60,6,decodeBank 7 0x2348aa097cdd56ccce,decodeHints 0x1c01806000000030000060880000d0080100680d0062bc0680d0fa0300680a00400805002006060010190320180105201a1940681102200c610d4000018000060080340200d0040280100a0100040080800209801801000018000010080340200d0040b80100101000400808⟩
]

def nodesBlock34 : Array Node := #[
  ⟨60,7,decodeBank 8 0x8d22a85e09809f3755b3,decodeHints 0x38030100040080800200c1300100c0000000600000c110000000041380008610c3e07c00621c0187c002d5c008440000180000609e0100207c00800c3e004008004040040080000600401601005002004028010030300080100105c0080c81900c0080500200402801004028008048090060dc300010100040400000c0000301c0380101b86e0040280100a⟩,
  ⟨60,6,decodeBank 7 0x22a825f3755b333854,decodeHints 0x38280000343681601a0343e80c01a038070070040640c8060041480686501a17461007000018000060080340200d0040280100a00201c46001000018000010080340200d0040b8010010100040080800600c000060000180200d0080340100a0040280881100202000808⟩,
  ⟨60,7,decodeBank 8 0x8aa17826027cdd56cc54,decodeHints 0x201c1500100001c140000000041380002c01c0b007002d60008720000180000600801c0b00400800404004008000060040160100700e00e0080100105c0080c81900c00805002004028010040280083503700e004040010100000300000c0700e00406e1b80100a0040280180300202000808000018000060860ac020360081f00100a00402804809⟩,
  ⟨60,5,decodeBank 6 0x8aa1783207809d5,decodeHints 0x803054004000030c00000000104e0000380300e00c718011820040200400c0000901200601c0881100203c14829000018538a702003c0380300e00c1a00105c0040300000c0000500a02003c1780f⟩,
  ⟨60,5,decodeBank 6 0x8aa2082607809d5,decodeHints 0x803054004000030500000000104e0000380300e00c02004012004e700000c0000901200601c0881100203c148290000180780b0ac03c0380300e00c2b80107e0040300000c0000500a0ac03c2b00f⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981e02755b0,decodeHints 0x803054004000030500000000104e0000380300e00c71801182004e700000c0000901200601c0881100203c148290000180780b02003c0380300e00c1a00105c0040300000c0000500a02003c1780f01200c30003012005ad001012001ac800008010028050ae15c1f809⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981e0275594,decodeHints 0x200c1500100000c140000000041380000800c038040080040400400800003004024048018070220440080f0520a40000603e07c0200f00e00c038030680041700100c000030000040080800f05e03c0380300e00c048010100040300000c00037004020024028050120fc2b857⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981e02735b3,decodeHints 0x803054004000030500000000104e0000700e00e010020010100100c81900c0100180700601c008650021d8000060000180200a0080282400302c00c1a00105c00688000384000010020200bc0180700601c0080800202400006000018020090080283b8770ae15c1f809⟩,
  ⟨60,4,decodeBank 5 0x22a852076cd72,decodeHints 0xc1400001c038038040320640300400601c018050000180000503c0780200a00601c0180700001800006008028010020ee0142b805⟩,
  ⟨60,5,decodeBank 6 0x8aa0981dff6cd72,decodeHints 0xc1400001c038038040320640300400200c380010020012a0000a41481d00400601c018050000180000503c0780200a0020e00080500601c0180700001800006008028010020021940083a0ee0142b805⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981e026cd72,decodeHints 0x200c1500100000c140000000041380001c03803804008004040040320640300400601c018070020e800a55000018000060080280200a00601c0180700202000809000018000060080240200a00a0140180700601c0082e0020d0000060000180200a0040081782f0120fc2b857⟩,
  ⟨60,6,decodeBank 7 0x22a88a1782607809b3,decodeHints 0xe00c0380309c00c15003002004000030500000000600c0000006904e0000200300e010010020580100202c05c0100200000c0100180700601c0a02f05e1d83286505c190000060000180200b0080b00180700601c2b85707e024049a939a02400006000018020090080b002805⟩,
  ⟨60,5,decodeBank 6 0x8aa1481e02755b3,decodeHints 0xc1400000800c038040080000300400601c018070000180000600802c0204500e00c0380300c000030000040092a0140ec1d80180700601c00006000018020090081b8028050ae15c1f809⟩,
  ⟨60,6,decodeBank 7 0x22a82607809ff755b3,decodeHints 0x30500000200300e0100200000c0100180700601c000060000180200b008338008030e0004008006b6000008040100101d00100e00c0380300c000030000040092a8140ec1d81a00105c0040180700601c00006000018020090081b802805002020008090ae15c1f809⟩,
  ⟨60,6,decodeBank 7 0x22a82607809d56ccce,decodeHints 0x30500000200300e0100200000c010018070060e8000060000180680d0086bc0380300e00c0300000c000010020740503286500601c01807000018000060080240206e0220442b85707e024008070060040000600000402008008004320010020b81a00101200400808⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981dd56cc6b,decodeHints 0x201c1500100001c11000000004138000080ec03804008004040040080000300400e1d803d110680041700100c000030000040080901203801c0080800202400006000018020090080702b85707e024018030020e8008260000180000600802c020320400401782f00a01404810⟩
]

def nodesBlock35 : Array Node := #[
  ⟨60,6,decodeBank 7 0x22a89e1782602755b3,decodeHints 0x200300e0102700305400c0080400000c14000000010030040001a41380000601c0180700802c020450740e8040c50000180000600e00c038030040081a00805c0200300000c0004081305e04c0180700601c020090081b8048c134e02400006000018028050ae15c1f809⟩,
  ⟨60,6,decodeBank 7 0x22a85e09809d56cccf,decodeHints 0x200c1080100000c140000000040e80000601c0180701a034008640000180000600e00c038030460041600100c0000300010204c1781300601c01807002940008e30000180000600a0142b85707e0240200300e0100400400800003004016010020130040080a0040120100206e⟩,
  ⟨60,6,decodeBank 7 0x23a8aa1782602755b3,decodeHints 0x18040020100400400201c150010000100300400001c140000000041380000802c0204106601c168070020e800832000018000060040080384800e3101a00105c0040300000c000080cd05e0bc020090080d8048070c001c0080800202400006000018028050ae15c1f809⟩,
  ⟨60,6,decodeBank 7 0x22a85e09809d56cc6c,decodeHints 0x200c1300100000c11000000004138000060ec018100020e8008320000180000601c0380c0030680041700100c000030000203341782f0061b801809002020008090000180000600a0142b85707e024038040080040400400800003004016010020320040083e0040120100206e⟩,
  ⟨60,7,decodeBank 7 0x22a85e0981e02755b3,decodeHints 0x20840082600600c13021054004018010003d00002200600c110f4050000018000003d00001d0020040e8f404e0000080000801c0236400600ce800700e0100180400802002363002004e780801001000804008018020f40000007a00600c0100000402000c01b6200e01c58003006040038070c8004008106c20e808001002191b0064020000000f400c0187a000000040030060400100201006c02c08004008080d002036801c0381400600c0a00700e6d0018030280541a5120020052b01505c05000801028018030f40000007a00600c0500000003406801014008009af8100200501001402804017b5e0400bc048030060dc0380706e00c0180900e01c048010029440400849600400809010024048000003d0030061e80000000900c019ae8040080241b0090120100235c06c1b80d01a00a024080050129102b83f02815c1fa1f07e0240a009⟩,
  ⟨60,5,decodeBank 6 0x8aa17832027cdd5,decodeHints 0x803054004000030c00000000104e0000901200601c0881100203c148290000180b00318e00c7180118200402004012000538a701c0380380306800417001032064030001502a03180f0141b80a00a⟩,
  ⟨60,6,decodeBank 7 0x22a85e09809f3755b0,decodeHints 0x200c1500100000c1400000000413800024048018070220440080f0520a40000602c00c638031c60046080139c000ab80001603c0700e00e00c1a00105c0040c81900c0000500f0c603c0506e028028048030c000c04801266004048006ca000028050080100483f00400823809⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981df36cd72,decodeHints 0x803054004000030500000000104e0000700e00e00c040010100040c81900c0001980305a00c1d0010100042d8000180000200400601c018050020e0008050000180000503c0780280a00a0f80480500601c018070020b800834000018000060560280100205e0bc0a01001201404805⟩,
  ⟨60,6,decodeBank 7 0x22a826077cdd56ccce,decodeHints 0x182800001c01807006018000060000e8018160060e80000c0000340680700601c01806000018000020040e80a0650221740181102222c000110220e01c0110220e8048110220e01c01100201c0180100001800001002020040010020e8040010020b81a00100a04400811⟩,
  ⟨60,7,decodeBank 8 0x8aa1782607809f3755b3,decodeHints 0x803054004000030500000000104e0000380300e00c040010100040300000c0000180700601c00b67002190000060000181003609e0800b00302c00c0400101000406000018000020040200400380300e00c1a00105c0040300000c000010024ae0500a0200340500d00300e00c038010100040480000c0000304f012025b300500a0680483f01213023809⟩,
  ⟨60,6,decodeBank 7 0x22a85e09809f3755af,decodeHints 0x200c1500100000c140000000041380000601c018050020e0008050000180000500800e8980400800404004008000060040160100700e00e00c1a00105c0040c81900c0000f01e00a028330040ae0100180700601c0080800202400006000018078050080240203f01213001002⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981e02755b3,decodeHints 0x200c1500100000c140000000041380000800c03804008004040040080000300400601c018070020e8008640000180000600802c0202000e00c038030680041700100c000030000040080801405e0bc0180700601c0080800202400006000018020090081b8028050ae15c1f809⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdb35c958,decodeHints 0x200c1500100000c14000000004138000a614c0b0040a41480400437a6f40600400601c018050020e000805000018000051ba3740200500601c018070020b8008340000180000600802c020660120140480501c038038030140044c001032064030000200100f01e00a02401002⟩,
  ⟨60,6,decodeBank 7 0x22a825f3755b3560ce,decodeHints 0x18280000343681601a0343e80c01a01c01807006018000060001480a00d0221740181102222c00011022034020110220e01c01100e00c0380300c00003000074034010020700441c01100201c01801000018000010080340200d0020b81a00100a0440081100247c41801⟩,
  ⟨60,7,decodeBank 8 0x8aa17826027cdd56cd58,decodeHints 0x803054004000030500000000104e0000180700601c00b6a002360000060000180200302c01002001010010020000180100580400e00c038030680041700100c000030006d20500a0200cc0500200300e00c038010100040480000c0000300500a0100486e0121302380900e00c03803088004d880100c000030002c0080278202ee010010026d002427809⟩,
  ⟨60,6,decodeBank 7 0x22a85e09809d5739b3,decodeHints 0x200c1500100000c140000000041380000601c0180701a0340080b03606c0000601c038038020040040a802032064030020140080100a00801c0180400802000804008018000040200100100a0040100180700601c00808002024000060000180f81f0040fc010090080fc02009⟩
]

def nodesBlock36 : Array Node := #[
  ⟨60,6,decodeBank 7 0x22a82602755b35bcce,decodeHints 0xc1400000601c0183a0000180000601c03803802032064030020a41480100a00601c01807000018000060220440103f004024020032f0010020000180100680d028008048040080fc00807006004000060000046e001004054010010120040080800802002001⟩,
  ⟨60,7,decodeBank 7 0x22a85e09809d56cd6f,decodeHints 0x8210020980180304c08415001006004001070000880180304441c14000006000001070000740080103a41c13800002000080030060f00380707800c0181000e01c6e001002041b583a020004008dc07a3700800000041c0300620e0000001000c0180100701c0600180e03001c03802006008010150040b0008010580540a80200200801006032028000190140180300200000805010014008100020040400100a040028048030060dc0380706e00c0180900e01c048010020f40400807a004008090100240480000041c0300620e0000000900c0180d01a00a024080050120080103f0140fc1f802004024050090080680207c00600c3e01a0f8010018040080200201a0020041e80801001000804008030021070000008380c01801000004a2806805804020010bb81a0280100100209e0240480407e010020090080681f83f⟩,
  ⟨60,6,decodeBank 7 0x22a825f3755cd6ccce,decodeHints 0x30500000686d02c0340687d0180340700e00e00c0c81900c0000500d0ca0340b00302c00c790001e40001d00d35e034010020221740181102222c00011022034020110220d4548110220e01a81100201c01801000018000010080340200d0020540a8010020540a80101204400811⟩,
  ⟨60,7,decodeBank 8 0x8aa17826027cdd5735b3,decodeHints 0x803054004000030500000000104e0000180700601c00b6c002114000060000180200302c01002001010010020000180100580401c0380380302a0040a801032064030000140802780a008d780201600605801815002054008f20003c800168056068021a00080080100300e00c038010100040480000c0000300f0120100483f0120d41a8090120d41a809⟩,
  ⟨60,6,decodeBank 7 0x22a87617825f3755b3,decodeHints 0x180700601c008030420040a80100000c1400000c000000060000040e80000800c1680401601002042008004040040080000600401c038038030140b00100204600416001032064030000140101780400601c0180500a0240480500202000805000018000050080f80200503c07802809⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cca0,decodeHints 0x9c00c1500300000c140000001a41380000800c1680401a0340a8040080000600401c0380380302a0e41702e032064030000140101780400601c018050220440b805000018000050080f80200503c0780280900601c01807002004000060000180200b00804c0100201201404805⟩,
  ⟨60,6,decodeBank 7 0x2388aa17825d56cd72,decodeHints 0x6010008040100100088c0e000400004018010000db0500000000104e000050040200101681805a0280a80102a0040c81900c0000203e008014028c70c001400838002014000060000140f01e00a0240200b0080401202d14c0b400815002054000060000180100201201404805⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cd72,decodeHints 0x8210020980180304c08415001006004001080000880180304442014000006000001080000740080103a4201380000200002016009458018036da058168040060100200800804000801020020040040020100200c00842000000210030060040000100500701c0600180e03001c0380a00600c0501502a0b0008010580540a80a0020040c006032028000190140180301800000005010014da4020044ae0400800a008010028030060dc0380706e00c0180500e014028010020c4040380620040080501001402800000420030062100000000500c014028040080240803e0120100200502001404b4303c0140501e00a1ac028090140241200300634c0380716000c0182400e01c210010029600a815a2a0040084202a05415800000420030062100000002b00c0180d0040080d80800b2c00100201a0200402784f0040ac050020400240481a00a0140d0090121e802805⟩,
  ⟨60,5,decodeBank 6 0x8aa147cdd56cd72,decodeHints 0x30500000200305a010020000180100700e00e00c0c81900c000050044a801001807006014000060000140203e0080140f01e00a0240180700601c000060000180200b0086ac0100201201404805⟩,
  ⟨60,6,decodeBank 7 0x22a825ff7cdd56cd72,decodeHints 0x3050000008030e0004008006dc0000200305a01002000018010020010100100700e00e00c0c81900c0000a80102a004050044aa0100180700601400006000014008380020140203e0080140f01e00a0240180700601c00006000018008150020540200b0083700100201201404805⟩,
  ⟨60,6,decodeBank 7 0x22a825f3755b35c8ce,decodeHints 0x30500000200302c010020000180100700e00e00c0c81900c00029052074010018070060e0000060000180203a0080e02684d0700240180700601c000060000180680d0080e8010020220440483800201c01801000018000010080e8020010020540a80100a0040083802a00400815⟩,
  ⟨60,7,decodeBank 8 0x8aa17826027cdd56cd72,decodeHints 0x803054004000030500000000104e0000180700601c00b70002dbc000060000180200302c01002001010010020000180100800401c0380380302a0040a8010320640300009e13c0500a008d7c0200300e00c038010100040480000c0000300500a0100483f0120d41a80900601c0180700205400815000018000060400ac02036008068010020120d404835⟩,
  ⟨60,6,decodeBank 7 0x22a88a09809d56ccc8,decodeHints 0x80300e004000030500000000100c000018070060e80680d002114000060000180380300e00c0100200c0000300007404c3286500601c018070020d4008e30000180000600a0140483506a0240200302c0100200101001002000018010058040080b80a8040120100203f⟩,
  ⟨60,6,decodeBank 7 0x22a88a097cdd56ccce,decodeHints 0x380300e00c000030500000000600c0000200302c0100680d074010020000180100380300e00c0100200c000030000740103280400601c018380220441c009000018000060080e8020380120e0548a900601c0180708405400801000018000060080e80203a05c0b80a89800a01404838⟩,
  ⟨60,7,decodeBank 8 0x8aa2285e09809f3755b3,decodeHints 0x380300e00c2700305400c0080100000c14000000018030000001a41380000601c0180709e9604304502adc40a8300000180000600800c0b004008068e78040089640a804008000060040160100380300e00c0100202a0b0170060000180002c04020c1602c0089580200300e00c0380906a0d40480902a9300480000c0000300500a0100483f0120d41a809⟩,
  ⟨60,6,decodeBank 7 0x2358aa097cdd56ccce,decodeHints 0xc0180000c0180000000e0880000d0740e80680d00e0580680d0fa0300680200401c0c0c400c000030000740341d00d0220e01c01102201c6101102222c00011022034020110220e01c0110020540a80100201c0b001000018000010080340200d0020540a80100a04400811⟩
]

def nodesBlock37 : Array Node := #[
  ⟨60,7,decodeBank 8 0x8d62a85e09809f3755b3,decodeHints 0x18030020540a80100201c150010000180300000001c110000000041380009e34c4384102c01c0b007002dc800864000018000060081f0e800400801c0b00400800404004008000060040160100100200e0606201500205400806000018000180280500c0180080500200906a0d40480900e0dc038010100040480000c0000300500a0100483f0120d41a809⟩,
  ⟨60,6,decodeBank 7 0x22a85e09809f7755b3,decodeHints 0x8030e0004000030500000000104e000018330060400083a002744000060000180200300e010020010100100200000c010058040080800700e02c00c1a00105c0040300000c0000801405e0bc010020280100186a0060240080800202400006000018028050080240206e0ae15c1f809⟩,
  ⟨60,6,decodeBank 7 0x22a85e09801f3755b3,decodeHints 0x200c1500100000c140000000041380000601c01807002054008150000180000600800c1680400800404004008000060040160100201001c0380380302a0040a80103206403000014050010020140100800400601c018050020e0008050000180000500a024048050080f80200503c07802809⟩,
  ⟨60,6,decodeBank 7 0x23885e09809d56cc63,decodeHints 0x201004004000010060040000041380000802c020e500244c008a60000180000601c038240040900040a80100c00003000030120338670080240203f002020008090000180000600a01404d1706a0243e00400e0100a80102a0040300000c0001682d02c2980100206a0241a809⟩,
  ⟨60,6,decodeBank 7 0x22a825f3755b333863,decodeHints 0x18280000343691301a0343e80c01a0380c00300c000030000740341d00d0221740181102222c00011022034020110220e01c0110021c001801000018000010080340200d0020540a80100a0440081100e00c0300000c0001d00d074034010020700441c01102a0040a801⟩,
  ⟨60,7,decodeBank 8 0x8aa17826027cdd56cc63,decodeHints 0x8030e0004000030500000000104e000018b000639400b7400236000006000018020034b401002001010010020000180100580401c0600181500205400806000018000180280500c018008050020030d400c048010100040480000c0000300500a0100483f0120d41a80900e00c0a80102a0040300000c0028c02009e0803e0046e60100100206a0241a809⟩,
  ⟨60,7,decodeBank 7 0x22a8921782602755b3,decodeHints 0x80580204400600c2201602c010018040100840402600600c13021042020018030341100080800801000134000088018030444d01400000600000134000030020040184d006000008010001340000740400803a4d00e800010000098030061280380709400c0181300e01c1800400804c1b00b026010020300880c01800801004c4181302602004030088314098000002b80300615c0000001300c0180100701c0600180e03001c038020060080103d0040b00200405873c16002008008010150040b0040080580541700201000801006032028000190140180300200000805010014008098020040400100a026028048030060dc0380706e00c0180900e01c1e8040080241b0090120100203d07a0fc04844012110040c108893d26809010024048000004d0030062680000000900c0180d01a00a02409805012008010350141301a80200402405009⟩,
  ⟨60,6,decodeBank 7 0x22a85e09809dc755b3,decodeHints 0x200c1500100000c140000000041380000601c0180701a034009790000180000600800c0380400800404004008000030040160100201300e00c038030680040a80100c0000300002004c080130040080180700601c009a900238c00006000018028050080240206e0ae15c1f809⟩,
  ⟨60,7,decodeBank 7 0x22a85e09809d56ccc8,decodeHints 0x821002110018030780841500100600400135000088018030444d414000006000001350000740080103a4d413800002000098030061280380709400c0181300e01c1800101a04c4180d026004008300880c0098000002b80300615c0000001300c0180100701c0600180e03001c03802006008015190040b0008010589644c00200200801006032028000190140180300200000805010014008098020040400100a026028048030060dc0380706e00c0180900e01c0480100211129a520880040080908838c048000004d40300626a0000000900c0180d01a00a02409805012008010350141301a802004024050090080580207c00600c3e01602c01001804088068040040020100200c0084d40000026a030060040000104181a016010098040080500201a004009ba8140280100100209e02404804034010020090080680d03f⟩,
  ⟨60,6,decodeBank 7 0x2388aa09809d56ccce,decodeHints 0x18040000100600400036c1400001a0340217802c2bc0b113000018000060040100c0020041200b002032064030020140080100a0080240203f01231c30009000018000060220440104c004024020080080040087011800400006000004190010040b80100101200400808⟩,
  ⟨60,7,decodeBank 7 0x2388aa1782602755b3,decodeHints 0xf81f001816008010008440020200200401011004001008010008b50020980b08c04c1103800102c00400136000030020040184d806000008010001360000880b0db0444d81400002c000001360000740080103a4d813800002000218040080c81b00b064010020430f810c2181602c0c869832064058168430f80b419001002129bb0af094004008320880c8250000000c8030060640000004a00c0180103c004060020040307400c002008008010160040612d0480300580b00216a008010150040b000801058054170020020080100603202800019014018030020000080536d014008190020041a00100a0640281e0040080241b0090120100203c0780fc048b50121b80b0c70dc1f03000902c024048010021100400808800400809010024048000004d80300626c0000000900c0180d01a00a02419005012008010350141301a80200402405009⟩,
  ⟨60,6,decodeBank 6 0x8aa097cdd56ccce,decodeHints 0x7480002200600c111d20500000180001a058068af0061b45781602c0340180d01a030068e10001f47080c0180340000d00401c070180060380c00700e008018020040180c80a0000640500600c008000020040e82901401a0340a03a0ca0080680d02200c088c200e1746100300604403811022000088d700c22c6b800000044030110220100880901a0340480400804406811022008088380141341c0020040440501100200c0082600e01c1300300600403801002000001d200c018e9000000004030010020100200801a034040040080040680d002008010150140b80a80200400405001010024028010220440080900202008811⟩,
  ⟨60,4,decodeBank 5 0x22a85a15809d5,decodeHints 0x800c0b00400601c018070080180203f00601c0180700829c0237700a014049b801c03803802004010050020980080100960a008010a7⟩,
  ⟨60,4,decodeBank 5 0x23c856027cdd5,decodeHints 0x600001c0000700001c028050134680200002c010048040080fc0580401c03803802098008010090140080100f0040100a002⟩,
  ⟨60,5,decodeBank 6 0x8aa15852027cdd5,decodeHints 0x601c0180700000dbc80000c0000180700601c0280501346c0000f000ddc0200302c010048040080fc020006f00100580401c0380380209800801009004000050020140080100f0040100a002⟩,
  ⟨60,5,decodeBank 6 0x8aa14809f37547e,decodeHints 0x300305000c0180700601c148290180180200302c010020062ae0100580401c03803802032064030020140080100f0040100a00200601c01807000000028050080240203f00413001009⟩
]

def nodesBlock38 : Array Node := #[
  ⟨60,5,decodeBank 6 0x8aa1685202755b3,decodeHints 0x800c0b00401800c140030000100180700601c0200b0094700600b0186e00700e00e008010040140080100c384008050020040280180700601c020090080fc049576f00240280500413001009⟩,
  ⟨60,4,decodeBank 5 0x23c7cdd56cc8a,decodeHints 0x3606c0b004032064030020040100a0020520a4018060080240203f004130010090060180000000802c0200b0040280100a00a0140480f⟩,
  ⟨60,5,decodeBank 6 0x8aa147cdd56cc8a,decodeHints 0x30036f400c0200302c0100d81b0160100700e00e0080c81900c008010040280080180700601c1482901e018020090080fc0104c0040240180700601c0000000802c0200b0040280100a00a0140480f⟩,
  ⟨60,5,decodeBank 6 0x8aa147cdd56cc6b,decodeHints 0x704400002007064010020000180100700e00e0080c81900c008010040ec0080901203801c00006000018020090080fc0104c004024018030000180000600802c020320040280100a00a0140481c⟩,
  ⟨60,5,decodeBank 6 0x8f214809f3755b3,decodeHints 0xc0380300e0a1bd028a3c010018160080128e82800802c0200e01c01c010020140280100a004008050020080500100300e00c03809050de40480500a0100483f00413001009⟩,
  ⟨60,5,decodeBank 6 0x852027cdd56ccda,decodeHints 0xc000030040000300200b0080640c80600402801002014008020140040000300000c014028040120fc0104c0040241400000e00c018070060100b00401c0380380200e00c01807⟩,
  ⟨60,6,decodeBank 6 0x8aa14809f3755b3,decodeHints 0xa4a0001100300608a9202800000c0037b00600dbe00700e11001803a4601c038bf0000029100600c2fc0000017e0180300402c011bd8030061100b01600800c020040180101e8000014840600c008000021ac07a02c020bf0080080380e03000c0701800e01c01003004008030190140000c80a00c01801000004029b700a0046b001002358008050450140081e802028010020146b6050010040040240180306e01c0383700600c0480700e02400000a400180351f0000000480600c6acd58050122fc029ab008010049ac0126acd603f012008010350141301a80200402405009⟩,
  ⟨60,6,decodeBank 7 0x22a825ff7cdd56cc6b,decodeHints 0x70440000080704c004008006f80000200706401002000018010020010100100700e00e0080c81900c0080100105c008010040ec0080901203801c0000600001800808002024020090080fc0104c00402401803000018000060020980082600802c020320040280100a00a0140481c⟩,
  ⟨60,7,decodeBank 7 0x22a826027fdf3755b3,decodeHints 0x5f80004400c0182217e0a000003000df4018036fc01c0384400600e9380700e2fc0000017e018030bf0000005f80600c0042200104c00c018260881c0008030020045f80117e000000bf0894980080000013c2217a0022fc0080402c011be8030061100b01600800c020040180105f8000002fc0600c0080000204f0e402c020bf0080100400408800400844010020020010080080380e03000c0701800e01c01003004008030190140000c80a00c01801000004029b780a00413c0100209e008050450140080a8020880040084402a0b8010010040081e802028010020146c0050010040040240180306e01c0383700600c0480700e0240000017e018030bf0000000480600c74ce98050122fc028090020042200801011000801012020049d30080100484f01274c2783f012008010350141301a80200402405009⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cd76,decodeHints 0x803054004000030500000000104e0000200305a01002001010010020000180100700e00e00c0a80102a0040c81900c000050040200100180700601400838002014000060000140203e0080140f01e00a0240180700601c00815002054000060000180200b0080400100201201404805⟩,
  ⟨60,7,decodeBank 7 0x22a89a17825f3755b3,decodeHints 0x218030063400380708800c0184300e01c008210020980180304c08410801006004430442f4004158010005ec0002200600c1117b0500000180000c5ec030000560000017b000018158060005ec0001d0020040e97b03a000008000080580204a00600c2501602c0100180410c0f4058040560100200800804c00801026020040040020100200c0082b80000015c030060040000100100701c0600180e03001c0380200600805528014008210020042180100a084028010150040b00080105805417002002008010060320280001901401803002000008010100040500200402804017802008008048030060dc0380706e00c0180900e01c4303d00a02415805012004008170100200b801002024040090120000006f00c018378000000240300602e010020090260240480400805c0983f012008010350141301a80200402405009⟩,
  ⟨60,6,decodeBank 7 0x22a825f3755b3338a0,decodeHints 0x18280000343681601a0343e80c01a038070070060640c8060001480686501a0442e8030220444580002204406804022044268a902200c0380300e0000300000c0100680401a0b80a80a00a0440481100601c01807000018000060080340200d0040080481101204400801⟩,
  ⟨60,6,decodeBank 7 0x22a825f3755b333890,decodeHints 0x60a00000d0da0580680d0fa0300680e01c01c010190320180105201a194068110ba00c088111160000881101a0240881109a0080880300e00c0380000c0000300b0100340102e004020048110120440180700601c000060000180200d0040280100a07a04400801⟩,
  ⟨60,6,decodeBank 7 0x22a825f3755b333813,decodeHints 0x38220000343691301a0343e80c01a038070070040640c8060041480686501a0442e8d40220444580002204406804022044268020221c013007000018000060080340200d0040280100a0120440481100600c000060000180200d0080340100a0040280481101204400801⟩,
  ⟨60,7,decodeBank 6 0x8aa097cdd56ccce,decodeHints 0xe80003a0000e8088018030e80883a0280e8000018002f00340b00d2f02bc0186d2a42bc0b0161be0340180d0e80340600d0e83840007d0e83840600c0e80340000d1be0080380e6e80600180e6e4060038071be008018020e8008030190e8028000190e8028030060e80080000212c0081d0526d40500680d6ce0501d06512c0080680d1be044018116b03080385d6ae308018031be044038110e8044000110e835c0308b0e835c000000e80440301112c044020114940240680d09e0240200412c044068116880440101165e0e00504d5ac0e00100258e044050111be00401801a5609803807106098018031be004038010e8004000000e81d0030060e81d0000000e80040300108800402004a540200680d1060200200412c0040680d10600401002a520540502e106054010024b6004050010880200480512c004088111060040480135402008811⟩,
  ⟨60,6,decodeBank 7 0x22a825f3755b33386b,decodeHints 0x70440003686d15e010020000180100700e00e0080c81900c008010040280082e85d18401c00006000018020090080fc0104c0040240080704c00400006000004020080080040102e00400404801002020018030000180000601a034020af0040280100a022044048c200209800826⟩
]

def nodesBlock39 : Array Node := #[
  ⟨60,7,decodeBank 7 0x22a826027cdd56ccce,decodeHints 0x3a00004400c018220e80a0000030005e0018036fe01c0384f00600c6f80700e1d0000000e8018030740000003a00600c0100b0042f000c01b7602c05802003008010060040e8000000740180300200000813d2500d0081d00680200e0380c00301c0600380700400c0100200c06405000032028030060040000100a6e00280104f00400827802014db0050026d60080a004008051b08140040100100900600c1b80700e0dc0180301201c038090000003a00600c1d0000000120180309612c044048740222580200401213c0489609e0fc048020040d40504c06a00801009014024008030020980380704c00c0180100e004008000001d0030060e80000000100c004220440600043a001002010020081060200400400800441801002008010150140b80a802004004050010100240480112c0040080900202041808⟩,
  ⟨60,6,decodeBank 7 0x23d8aa097cdd56ccce,decodeHints 0x18030001a4138000000a81100001a0340980400832489804008000060040040e44c0020043201500203206403002004010178020220440b8090122546a009000018000060080240203f00413001009086098008010e00a81302a0000180000600802c020130040280100a00a01404817⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56ccce,decodeHints 0x6f82109c11001803700084150df00600c00074000088018030441d014000006000000740000743a06903a1d0138000e800002016008128018030940580b0040060100204401a04c4b00d0260f4098040880100200c0082b80000015c030060040000100100701c0600180e03001c038020060080125b0040b12d839058dc44c002088008010060320280001901401803002000008010100040500200402804017802008008048030060dc0380706e00c0180900e01c0484402205cd501102e2180b809088024048000001bc030060de0000000900c0180b80400802409809012010020170260fc048020040d40504c06a00801009014024120030062dc0380708800c0182400e01c220860020ac3a0010560000007400c0183a0000000ac030060600100203d02602c220040080c00981308400801258014028418020041080500a0600240281a02e014220090120c00b817⟩,
  ⟨60,6,decodeBank 6 0x8aa097cdd56ccd5,decodeHints 0x7500002200600c111d40500000180001a058068320061b41901605a0340180d01a030068e10001f47080c0180340000d004138360180061b00c04e09c008018020040180c80a0000640500600c008000020040e82901401a0340a03a0ca0080680d02200c0881c09c1740e00300604427011022000088d700c22c6b800000044030110220100880901a0340480400804406811022008088380141341c0020040440501100200c0082609c01c1300300600427001002000001d400c018ea000000004030010020100200801a034040040080040680d002008010150140b80a80200400405001010024028010220440080900202008811⟩,
  ⟨60,7,decodeBank 7 0x2398aa17825f3755b3,decodeHints 0x438b500e00c1580310e1129600106000400844002110180300022d40082600600c130440e00040180100c5f0030000560000017c000018158060005f00002200600c1117c050000018000005f00001d0020040e97c04e0000080010e0f005804056010020160080c801803064058168040060100200800812800801094020040040020100200c0080c80000006403006004000010050b00140081000200421c0100a04002801016004060018030300580b002006008010150040b000801058054170020020080100603202800019014018030020000080103c004050020040282c03b0020080084383c00a0241580501200c0181c02c1a80e0030060240b009012004008540100202a001002024040090120000007f00c0183f8000000240300603801002009064024048040080701903f012008010350141301a80200402405009⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cc6b,decodeHints 0x8210020980380704c0841500100e0040017d000088038070445f41100000e0000017d0000740080103a5f413800002000023810080c8038070640f01900400e0100200800812800801094020040040020100200c0080c800000064030060040000100100701c0605800e03001c0380216a008010150040b000801058054170020020080100603202800019014018030020000080103c00405002004028d883b002008008048b50240700381203821c0e00900e01c04801002150040080a800400809010024048000001fc030060fe0000000900c0180e004008024190090120100201c0640fc048020040d40504c06a008010090140243e0870060ac03803060004008b704c098680010020c0130260560000017d00c018be8000000ac030060860100203c06402c5a80400810c19032040008010d3014028340020040800500a04802402843038014218090120900e01c⟩,
  ⟨60,7,decodeBank 8 0x8aa17826027cdd56cc6b,decodeHints 0x807054004000070440000000104e001c088700e005bf8016fc0000300000c010038d3008010008080080100000c0080c80200e01c01c010020020b8010190320180100a004008050020080500100900e0dc038010100040480000c0000301c0120100483f0041300100900600c00826002098000060000182182b0080d80207c0040280100a0120dc04837⟩,
  ⟨60,7,decodeBank 8 0x8f62a85e09809f3755b3,decodeHints 0x1803002004108260540000e81d000000108220000000e81d0000c05b8440605f810844042099c00260600000300000c0103e044008010108440080101e0260080100000c00802c020020580b001002100084010020580b0010190320180100a004008050020080500100906e0dc048090420dc0480904c9380480000c0000300500a0100483f00413001009⟩,
  ⟨60,8,decodeBank 7 0x22a85e09809f3755b3,decodeHints 0x16a00410801088098018037240981082a16a0040180111200044800112088018031120884482811200001800112000448001120740080111207444827112000008000f810c01803a6b4d00380709e9740180316a10c038070880c0008011074ce9953109e970008010880c2980301120ac0000011222403006112224000001120ac030060f80100b0040f81f001803078e440b01616a0100180408801004004034e400080107ae3c040080880100080411201006004112224000001122240600c112010000043ac755a800b1120101580416a0080380e71c0600180e71a0600380716a008018023620080a8023620b0008017180b00a82e0880080080211200803019112028000191120280300611200800002a5e02a9700a09e0081000209e0091a802a5a0281000a034009c580271405002004712051c40140340080200216a0240180370e0dc0380770c0dc0180316a024038070880240080170ae1004008706e080080108802404009112024000001122240300611222400000112024030060340680d00511202415805034068020043ac024ea8090340682783f68e024010026680d40504c6240d40100259402405009⟩,
  ⟨60,5,decodeBank 6 0x85e09755b364066,decodeHints 0x104e0000706c02a0380707e00c0380f92500207c0f94b00007c0f80e00407c0680d0100040d81b0180002980e0ce0380481f00802000804008030000040040380100e00a07c0201f0080b419804⟩,
  ⟨60,6,decodeBank 7 0x22a85e09779d56cd90,decodeHints 0x200c1500100000c1400000000413800008e4c01804008020008040080300000400400c038020040040a802004000030020140080f85000607c0f92500207c0f94b00007c0f80500807c0f80500407c1980305a00c0680d0100040d81b01800005804020010058020200080481f⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981df3779b3,decodeHints 0x803054004000030500000000104e0000100300e008010010100080100000c0081980305a00c1d0010100042d8000180003300200612001858002020008080000300000c0040280102b0200501782f00601c018050020e000805000018000050040140106300a0f80480501201402809⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdde6cd58,decodeHints 0x200c1500100000c14000000004138000cc00c0b06601a0340406603606c06066006120018d6002020008080000300000c0cc02c0200400601c018050020e0008050000180000503e07c330050120140280900400c038020040052f002004000030020200080500200a00801009⟩,
  ⟨60,6,decodeBank 7 0x22a88a17825f3779b3,decodeHints 0x100300e0082700305400c0080200000c14000000008030020001a41380006600c168030cc008098020740e80a80b03606c060000062000182c0040280104202a0b01702e0000300000c10202c0200400601c018050040140100900a2a42b0050000180000503e07c0480501201402809⟩,
  ⟨60,6,decodeBank 7 0x2358aa17825f3779b3,decodeHints 0x18020020080a80200201c150010000080300200001c11000000004138000cc0080800206601c1680701a0340400103606c060000040280104300e060038c4002020008080000300000c02002c020040040140100900a3001b8050020e0008050000180000503e07c0480501201402809⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdde6cc63,decodeHints 0x200c3800100000c1400000000413800a6c00c5300301a0340400103606c0600001c03801824002020008080000300000c02002c020040061a8018e00020e0008050000180000503e07c048050120140280900e0080100102a0080100000c008010660200080500200a00801009⟩
]

def nodesBlock40 : Array Node := #[
  ⟨60,5,decodeBank 6 0x85e0e7cdde755b3,decodeHints 0x104e0000680d0100040d81b018000008080020200000c0000300800b0080100100102a0080100000c00801066020008050020020e0008050000180000503e07c048050120140280900401401009⟩,
  ⟨60,6,decodeBank 7 0x217825f3779dd755b3,decodeHints 0x41380001a0340400103606c06000002020008080000300000c02002c02004006004150010060029b8000060cc1680325200c0100102a0080100000c008010660200080500200400c038020020e0008050000180000503e07c048050120140280900601c0180500401401009⟩,
  ⟨60,6,decodeBank 7 0x2368aa17825f3755b3,decodeHints 0x25200c040010020200080305400406000000030000030440000000104e000058100080101280305a00c0680d0100040d81b0180000500200400c038020040040a80200400003002004198080020120140280900601c018050020e0008050000180000503e07c0480500401401009⟩,
  ⟨60,6,decodeBank 6 0x85e097cdd56cc66,decodeHints 0x75c0001d0020040e9d704e00000800016020068130020340980801002c008010260300d80b00006c0580c01804c0000001c054070800021b04001502a0380080e01c018070e20001f87100600c0380000e01c0400704801614c240100ce0380580e024004090950101744a80100204804012024000090d500c2446a80000004803012024e4c0f80901607c04a47012048058120240080900501c0380280200404807012006004008210100201080100200c04003006000001d7018030eb80000000c06003006040018160160b40b01000800c058040060080100701c0380380200400c0700e00e014028030240480180500601c09012⟩,
  ⟨60,6,decodeBank 7 0x217825f3779d56cc66,decodeHints 0x41380001a0340400103606c06000002020008080000300000c02002c0800b0040040a802004000030020041980800201c03800838002014000060000140f81f0120140901200a024010050040240080800200c0000c00000c0182d06600c1200300401c0100300a00c01807⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cc66,decodeHints 0x88c0e0004000db0500000000104e0000583b14c02c0680d0100040d81b0180000700e0300080100102a0080100000c008010660200080901203801400838002014000060000140f81f0120140100500402401803002020008080000300000c02002c020040040280101800a02402809⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdde755b3,decodeHints 0x8210020980180304c08415001006004001090000880180304442414000006000001090000740080103a42413800002000058160660c8018030640581680b00600c0580801a04c0080d0260200400b0020040980c03602c0001b01603006013000000120030074ee9d5394c000c01824a70090210010023480400816200400842010020158000004240600c2120000002b0180300d0100205980580b09e0400201a01601001007004e600180372e01c03802006008010150049780080172c0540a80200200801006004424000002120180300200000801010004e54058664be040080020160081b0360140081580200a00c0183700e01c1b8030060140380500a004008310100e0188010020140400500a0000010900c018848000000140300500ae500f80901607c04a4801201405805012080048050340140282000a0240d0090120080100506c014028020040241b009⟩,
  ⟨60,6,decodeBank 7 0x217825f3755b354866,decodeHints 0x8270000340680800206c0d80c0000383601501c0383f00601c0382986701c004040010120000300000c07c0480b0040380100e002020008080000180000648e02c0100e0040380901200202000803000030000030060b4198030040380100e00e00c0180700e00c01807⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f3779d56cd52,decodeHints 0x803054004000030500000000104e0001980305a00c0680d0100040d81b01800001d3c006368008080020200000c0000300800b02002c0100300e0080100102a0080100000c0080100b0200080500200601c01807002020008090000180000603e0240580906a0d40480206a0080480300e00c038010100040400000c000032480160801580206c0d802805⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f3755cc6cd52,decodeHints 0x803054004000030500000000104e0001980305a00c0680d0100040d81b0180000100300e0080100102a0080100000c0080100b0200080380300e00c0a80102a0040300000c0000800b02002c0500200601c01807002020008090000180000603e0240580206a0080480906a0d40480300e00c038010100040400000c000030040080d8010202ca0ac07809⟩,
  ⟨60,7,decodeBank 7 0x22a85e09809f3755b3,decodeHints 0x1042004130030060981082a00200c00800214000110030060888502800000c000002140000e801002074850270000040004300600c5a80700e1f00180308601c038300020042204f2f4110008010601101802b0000008500600c428000000560180300402c0103e0030060f00b01600800c02004010010220010021100400800800402004018010850000004280600c0080000204f03402c0202b0080080380e03000c0701800e01c010030040080a8020580040082c02a0b801001004008030190140000c80a00c01801000004028b400a0040800100209e008050200140080d002028010020142ee050010040040240180306e01c0383700600c0480700e024008010880200404400200404808012024000002140180310a0000000480600c0680d0050120ac0281a0080100484f0120680d03f012008010350141301a80200402405009⟩,
  ⟨60,6,decodeBank 7 0x22a88a1b825f3755b3,decodeHints 0x80300e0040180700601c00808002108000030500000000100c000030000000181980305a00c618010260041d03a0080100d81b0180000380300e00c0100202a0b01702e00c0000300010202c1780b00601c018070020d40080900a0140b8090000180000603e07c0480b0120d41a809⟩,
  ⟨60,7,decodeBank 7 0x22a86e17825f3755b3,decodeHints 0x120030061c80380716e00c0182400e01c008210021c80180306c084108010060041b03d010004158010005fc0002200600c1117f0500000180000c5fc030000560000017f000018158060005fc0001d0020040e97f03a000008000160581983200600c1901605a02c018030160f40581306004c0984400802c180040161c8618130020040983d02602c008010260300d80b00006c0580c01804c0000000401c070180060380c00700e0080180201434805002084008010b10040282100a0049780102c00200416399058008008020040180c80a0000640500600c008000020040400101401602c0a01005e0080580201200c0183700e01c1b803006024038070120c0028170340140b83002e024390090120040081706c05c0b801002024390090120000006f00c018378000000240300602e0f40f80901607c0488301205c0580b012008010350141301a80200402405009⟩,
  ⟨60,7,decodeBank 8 0x8aa1b85e097cdd56cd52,decodeHints 0x180700601c008030420040400100000c1400000c000000060000040e80006600c1680301604c0980b0160040980103606c0600001c038038020140080100a004004160020320640300200402c1780200601c018070120681e8090020d8008090000180000603e024058020980080480300e00c038300560041b0720000180000610602c0100a0040280b809⟩,
  ⟨60,5,decodeBank 6 0x85e097cdd56cc64,decodeHints 0x1a41380001a0340400b03606c0600001c1b00a80e01c1f80300e01c14c3380e0220440b8120242440001203e07c048120240380101200602000801000030000030060b4020040040380100e00a04801812⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd9755b3,decodeHints 0x2700305400c000030500000006904e0001980305a00c0680d01002c0d81b01800001d3d0060900a8080020040000c0000300800b0080100100300e0080102302a0080100000c008010660200080500200601c018050220440b8050000180000503e07c048050120140280900401401009⟩
]

def nodesBlock41 : Array Node := #[
  ⟨60,6,decodeBank 7 0x22b8aa17825f3755b3,decodeHints 0x3803010098008011bc00c1300300c0000000600000c110000001a4138000160c80200404a00c1900301a0340400b03606c060000140080100a00400c0c002004020170020320640300200402c1780200a0140e009006070018090220440b8090000180000603e07c0480b00413001009⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cc90,decodeHints 0x402109c0980180304c0841500800600c001800000880180304460014000006000001800000740406903a60013800010000058160660c8018030640581680b00600c0580801a04c4b00d0260200400b0e402c0980c03602c0001b016030060130000000100701c0600180e03001c03802006008010150040b00400805805417002010008010060320280001901401803002000008010100040500580b02804017802016008048030060dc0380706e00c0180900e01c0487202205c0401102e0d80b809010024048000001bc030060de0000000900c0180b83d03e0240581f0120d80481701602c048020040d40504c06a00801009014024218030061c803807a7e00c0184300e01c1e8360020ac040010560000018000c018c00000000ac030060880d80202b016010210020040d80500aa7c008010420140281e83d00a0ac04805⟩,
  ⟨60,6,decodeBank 7 0x2358ba17825f3755b3,decodeHints 0x18070060800080302a0042700100201c0000300c000030000000180000104e0001280302000c198070080100680d0100040d81b0180000100200e060038c402a0040a80100c0000300002002c0800b0060d40180900a0140e007002020008090000180000603e07c0480b0120d41a809⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cd78,decodeHints 0x803054004000030440000000104e0001280305a00c0680d0100040d81b0180000700e00e00c1a00105c0040c81900c0000500b05e0280180700601400838002014000060000140f81f0120140f01e00a0240180700601c00808002020000060000181900b0080100100201e0140e005⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56ccd3,decodeHints 0x2700304200c000030440000006904e0001280306400c0680d01002c0d81b018000010030420080100805c0080c81900c0080100b05e008018950060240881102e024000060000180f81f01202c0104c00402401807006084008010000180000606402c020040040280100a00a0140e009⟩,
  ⟨60,7,decodeBank 7 0x22e8aa17825f3755b3,decodeHints 0x1b03c00e00c1580301150404001060004008b7002020180080023680082600600c1303604c0040180100c6040300005600000181000018158060006040002200600c11181044000018000006040001d0020040e98104e000008000160f0058320860c81907c00802c218040167601283200600c1903c06402c01803016020068130020340980801002c008010260300d80b00006c0580c01804c0000001550005002040008012600040281000a0043680101800600c0c39a030008018020040540102c0020041601505c008008020040180c80a0000640500600c008000020040400101401602c0a01005e008058020120900281c0860140e0240380242180901200c0181c06c0700e0030060246d009012004008540100202a001002024040090120000007f00c0183f800000024030060380f00f80901607c04a490120700580b012008010350141301a80200402405009⟩,
  ⟨60,7,decodeBank 8 0x8ba2a85e097cdd56cd52,decodeHints 0x38030100040080800200c1300100c0000000600000c11000000004138000160c81900b01600c1900301a0340400103606c060000140080100a00400c0c002004004170020320640300200402c178020120dc1b8090060dc01809002020008090000180000603e024058020980080484305600c1b1d8002020008080000180000649202c0100a0040280e009⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd7755b3,decodeHints 0x807054004000070500000000104e0001980705a01c0680d0100040d81b0180000392900600c008080020200000c0000300800b008010010ca00e0080100102a0080100000c00801066020008050020240480e0050020e0008050000180000503e07c048050120140280900401401009⟩,
  ⟨60,6,decodeBank 7 0x217825f3755b318c33,decodeHints 0x104e0000680d0100040d81b0180000706c02a0380707e00c038070530ce0380905d002048090910000480f81f0120480900e06a0480380109c0040300000c0000382d06601c0100e00e0487481200202000803000018000030080100180e1940380281200601c94803⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cc33,decodeHints 0x8210020980380704c0841500100e00400182000088038070446081400000e000001820000740080103a60813800002000058160660c8038070640581680b00e01c0580801a04c0080d0260200400b0020040980c03602c0001b016030060130000000100701c060ec80e03001c038021b4008010150040b00080105805417002002008010060320280001901401803002000008010100040500580b02804017802016008048da024070038120380d80e00900e01c04801002150040080a800400809010024048000001fc030060fe0000000900c0180e03c03e0240581f0120d80481c01602c048020040d40504c06a008010090140241e0360060ac0380306000400872010020390010020c0040080560000018200c018c10000000ac0300616a0d80202b016010100020040d80500aa84008010200140281e03c00a0ac04805⟩,
  ⟨60,7,decodeBank 7 0x22a85e09755b364152,decodeHints 0x8210020980180304c08415001006004001830000880180304460c14000006000001830000740080103a60c138000020000100701c0600180e03001c03802006008010150040b000801058054170020020080100603202800019014018030020000080f80303e67c0385033e00c0181f00e07c0f80103e984041254c20040081f01007c0f80003ee6c0314b7360000001f00c07c0f80203e0f8050dd07c0080101f01407c058160660c8018030640581680b00600c0580801a04c0080d0260200400b0020040980c03602c0001b0160300601300000005814016040010020200501780b0040082781a01202c0f81f00800c0203c00e01c1e003006010038040080040203d0100201e801002010040040080000218300c018c18000000100300400800801036014029ca002004010050040340680280403e07c0d04f09e01005804⟩,
  ⟨60,6,decodeBank 7 0x22a88a21825f375552,decodeHints 0x80300e0040180700601c00808002024000030500000000100c000030000000181980305a00c058011580040f81f01202c0d81b0180000380300e00c0100206a0241a80900c0000300054a02cd400b00601c0180700205c008f500a01400006000018020041742e82b017⟩,
  ⟨60,7,decodeBank 7 0x22a88617825f375552,decodeHints 0x48030060dc0380706e00c0180900e01c008210021c80180306c084108010060041b03d010004048010006100002200600c111840500000180000c6100300001200000184000018048060006100001d0020040e98403a000008000160581983200600c1901605a02c018030160240f81303407c0980901202c0d00b0161c8058130020040983d15802c008010260300d80b00006c0580c01804c0000000401c070180060380c00700e008018020140d426002012008010350040280480900550c0102c00200416262058008008020040180c80a0000640500600c008000020040400101401602c0a01005e0080580202e00c0185400e01c2a00300605c0380707a0f4028170120141800100205c1b01702e004008300e41580b8000001bc030060de0000001700c0182208300805c0580402e008010310140281880200405c0500a⟩,
  ⟨60,7,decodeBank 8 0x8aa2185e097cdd56cd52,decodeHints 0x601c0180700200c1080101000400003050000030000000180000103a0001980305a00c0581302602c058010260040d81b0180000700e00e00805002004028010010580080c81900c0080100b05e0080180700601c048090020d83900000c0000326110602c0100a0040280180700601c1e82b0020d800830000018000060080100100a0040280b817⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd5548b7,decodeHints 0x100842702600600c13021054020018030006140002200600c11185050000018000006140001d0101a40e98504e000040000160581983200600c1901605a02c018030160200681312c0340980801002c3900b0260300d80b00006c0580c01804c0000000401c070180060380c00700e008018020040540102c0100201601505c008040020040180c80a0000640500600c008000020040400101401602c0a01005e0080580202e00c0185400e01c2a00300605c038070601c8088170100440b83602e0c00400802e0000006f00c0183780000005c030060880d8020170160100b8020040c40500a06200801017014028048030060dc0380706e00c0180900e01c1e836002024040010120000018500c018c2800000024030060340f40f80901607c048360120680580b012008010350141301a802004024050090120c00281a02e014390300600240b809⟩,
  ⟨60,7,decodeBank 8 0x8d22a85e097cdd56cd52,decodeHints 0xe00c040010020200080304c00403000000018000030440000000104e0000583206402c0580306400c0680d0100040d81b01800005002004028010030300080100105c0080c81900c0080100b05e008048090060dc300010100040400000c0000319f06e02c0100a0040282182b0060d80187c00202000808000018000060080100100a0040280e01c⟩
]

def nodesBlock42 : Array Node := #[
  ⟨60,6,decodeBank 7 0x22a85e097cdd565152,decodeHints 0x200c1500100000c140000000041380003e1401681f03e4940401f03e52c0601f00400c0380200400417002004000030021ba07c1781f00e00c038030120040400100c0000300001607c1f01f0120082600202404801807022044008080520a40000600807c0f01e00403c02805⟩,
  ⟨60,7,decodeBank 8 0x8aa17826077cdd56cd52,decodeHints 0x803054004000030500000000104e0000380300e00c040010100040300000c0001980305a00c1d0010100042d8000180000580b00e00c038030680041700100c000030000040080801405e00c0380300e004040010120000300000ce700480906c0f8048100121302380900601c0180700202000808000018000060400d8278202ee040100144be05002805⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56dd52,decodeHints 0x200c1500100000c140000000041380007c00c0b00301a0340400103606c0600000400c03802004004170020040000300200402c3b8020061a801809002020008090000300000903e07c1f00b0041300100900601c018050020e000805000018000050080100100500418c07805⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f3755b356152,decodeHints 0x803054004000030500000000104e0000b00302c00c0680d0100040d81b0180000380300e00c1a00105c0040300000c000e481401600c0380300e004040010120000300000c07c0480b0121302380900e00c038030e40053180100c0000300002002c0100206c025ce80900601c0180700202000808000018000060080101001472a050028050400d8b3020⟩,
  ⟨60,7,decodeBank 8 0x8aa2285e097cdd56cd52,decodeHints 0x380300e00c2700305400c0080100000c14000000018030000001a41380006600c1680301604c0980b0740e80a80b03606c0600000e00c038030040080a82c05c018000060002040582f01600c0380300e0241a8350120240aa620120000300000c07c0480b0120d41a80900601c0180708a0d858845060055cc815000018000060080101002c72c0b002805⟩,
  ⟨60,7,decodeBank 8 0x8d62a85e097cdd56cd52,decodeHints 0x18030020540a80100201c150010000180300000001c11000000004138000160400800b06601c1680701a0340400103606c06000004008038181880540081500201800006000040058100160241a8350120240383700e004040010120000300000c07c0480b0120d41a8090820d93004117801dcd00700202000808000018000060080101001872e06002805⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cd54,decodeHints 0x200c3800100000c140000000041380001600c5300301a0340400103606c0600001c0380c0020040040a80200400003002004198080020063a4018050020e0008050000180000503e07c04805004014010090064a401807002020008080000300000c02002c020040040280101800a02402809⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f3755b354863,decodeHints 0x8030e0004000030500000000104e0000580314c00c0680d0100040d81b0180000701800605400815002018000060000400581001600c35003012004040010120000300000c07c0480b0120d41a809006764018e50020200080800001800006008010100187300600280500e00c0a80102a0040300000c0000800b02002c0100206a0241a80906c082a2020⟩,
  ⟨60,8,decodeBank 7 0x22a85e097cdd56cd52,decodeHints 0x1b4004108010e40980180306c0981082a1b40040180112400049000124088018031240884902812400001800124000490001240740080112407449027124000008002a602c0b0332a60c8018030780c80b02d1b402c018030e402c0400d03404c0080d07a04c040080e402c0080112404c0601b12402c0001b12402c0600c12404c000001b40080380e7500600180e74e060038071b4008018024c60080a8024c60b00080174c0b00a82e0e400800802124008030191240280001912402803006124008000020340080800274a0500580b7480500802f034008058021b40240180306c0dc038077460dc018031b4024038070e40240080106ce8804008742e80008010e40240400912402400000124248030061242480000012402403006034069cf81f3ac024ea8090340680580b6900240100206c0d40504c6260d40100206c024050091b410c0180306c99403807a97528018032a610c038070e40c00080106c99004008a93520008010e40c0040081240ac0000012424803006124248000001240ac030063ace78ea8041240ac05804a8e0800100206c8f80500aa8d5140100206c0800500a0340680d0051240ac04805⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cde2755b3,decodeHints 0x8210020980180304c084150010060040010b0000880180304442c140000060000010b0000740080103a42c138000020000201600953401803078058168040060100200800804000801020020040040020100200c00842c00000216030060040000101200700e0f00180307801c0382400600c210080100f40080107a020040420020041580600c42c000002160180302b0000000d010016068020040340400801a008011d480700e0500180302801c03ba900600c0a0150695300080107a054170140020040a00600c42c00000216018030140000000d010020050020040280401781a0080100d01a0040501580200a00c0901c00e0480e0030060140380500a004088170100440b8010020140400500a0001480f00c0a4078000000140300500a0100f83502007c1a8040080140800501e59c078050f40140284f00a03c1000901ed14260050280140286b00a03c0a00f⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981dd56d9b3,decodeHints 0x200c1500100000c140000000041380000e00c0380301a0340400103606c0300000e00c038030680041700100c0000300039202c0380300e00c320010740040300000c0000200405e0bc0801402404801805022044008050520a40000501e0140280f01e014028770120140280f⟩,
  ⟨60,7,decodeBank 7 0x22a85e0981dd56cd90,decodeHints 0x8210020980180304c084150010060040010c00008801803044430140000060000010c0000740080103a43013800002000020070080f00180307801c03804006010020080080f40080107a020040040020100200600843000000218018030040000111000700e0500180302801c03a2000600c0a01506953c0080107a054170140020040a00600c43000000218018030140000000d01a0040500200200a00c0901c00e0480e0030060140380500a004088170100440b8010020140400500a0001480f00c0a4078000000140300501e0100f80506c07c0280400803c1b00f01e9140780502801402a2100a03c0a077020058198bc00600c5e01605a040018030c80201d01000200408008010190008010200302d90c0000008600c01804000000a9c06805810008010100140280400d0100200501781a0340bcbb81a01204002805⟩,
  ⟨60,8,decodeBank 7 0x22a85e097cdd56cd90,decodeHints 0x1ee0041080122e098018030780981082a1ee0040180111c0004700011c0880180311c0884702811c0000180011c0004700011c0740080111c0744702711c000008003b40100b0043b4768018030340f00b0161ee0100180422e01004004034068008010340f40400822e0100080411c0100600411c2380000011c2380600c11c010000041ee0080380e0780600180e078060038071ee008018024320080a8024320b00080107a0b00a82e22e0080080211c0080301911c0280001911c0280300611c008000020340080d00203405002004034051d5014034008020021ee0140181207807003812078070018031ee0140380522e0140081107a05c0401107a05c0080122e0140400511c0140002911c03c0302911c03c0000011c01403005034069cf81f034068020040340140d00569203c0101e66a0140501e6280140100259603c0500f1ee0900b0163b410c0180303410c0b0161ee0900180322e0c004008034068008010340f40400822e0c00080111c0ac0600c11c2380000011c2380600c11c0ac000000340680d00b11c0ac020040340800a014034068010020355400a01403406801002034e780d00911c0ac02805⟩,
  ⟨60,5,decodeBank 6 0x886097cdd56cc65,decodeHints 0x30000000180680d00802c0d81b0180100706c0040380707e00c038070530ce038088110000180000600802c0200b0040380100e00e00400807000030000010080b4020010040380100e00e00400807⟩,
  ⟨60,6,decodeBank 7 0x22a886097cddb755b3,decodeHints 0x601c0180700000c1400000c0000000600800c1680401a0340200b03606c060040029980180102a004008080000300000100802c0200100400c0380202a0080100800400003002004010080020140080180700601c088110000180000600802c0200b0021580081700415801017⟩,
  ⟨60,7,decodeBank 7 0x22a886097cdd56ccb7,decodeHints 0x40030060980380704c00c0180800e01c0018600008801803044618140000060000318600c0000400000061800006010018020160080c801803064058168040060100580801a0104b00d0080200200b12c02c0200c03602c0001b016030060040000100100701c0600180e03001c0380200600805015068008040020040540100a0100200100603202800019014018030020000080101000405002004028040178020080080b803006150038070a800c0181700e01c1803002205c0401102e0000006f00c0183780000005c0300602e0100203601602c5880400805c0580b02e008010310140281880200405c0500a00200c008d000e01c68003006004038010600c015801010004008000006180300630c0000000100c004008040080d80580b16201002001016004008020040d80500a4ce00801001014004180300ac0040b801⟩
]

def nodesBlock43 : Array Node := #[
  ⟨60,7,decodeBank 8 0x8d22a88617825f3755b3,decodeHints 0x38030480c02002400621c0182410c0040083000200c1b0010100040300000001800003044000030000000180000103a0000580400802c020030640100580400802c020010260100d81b018010050020040280100303000805002004028010010580080c81900c0080100405e0080b8170061505d81c0380042a0eb0000180000600802c0200b0040280100a⟩,
  ⟨60,7,decodeBank 8 0x8aa2185e097cdd56cc54,decodeHints 0x4201c1080700201c1080101000400007050000030000000180000103a0000200705a0100580400802c020010260100d81b0180100700e00e00805002004028010010580080c81900c0080100405e0084a85400e0700e0010a83ac000060000180200b00802c0100a004028018031cc0ac008d00020c0000060000180200b00802c0100a0040280b817⟩,
  ⟨60,6,decodeBank 7 0x22a88a21826077cdb3,decodeHints 0x200c0380100601c018070020200081400000c140000000040300000c0000000600e00c038030040081600105c0b01709800c0000300006600c16803028004178010ca194170e70b6000060000080100180700601c008170023d402805000018000061742e82b01702e6a0e6817⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981dd56cd5f,decodeHints 0x803042004000030500000000103a0000380300e00c0680d0740040d81b00c0000380300e00c1d0010ca0040300000c0000100200601c0183e0020e80083e0000180003e03e07c1f00b0120f83b87700601c018070020e80083a0000180000608402c0200405e0bc0807600a0140b83e⟩,
  ⟨60,6,decodeBank 7 0x22a89e21825f3755b3,decodeHints 0x80300e0040180700601c008080020d8000030500000000100c000030000000181980305a00c020040740e8040c50b60000600000e00c038030040081a00805c0200300000c0004081305e04c0180700601c008170023d402805000018000061582b0d38171742e82b017⟩,
  ⟨60,6,decodeBank 7 0x22a85e09811f3755b3,decodeHints 0x200c1080100000c140000000040e80004200c108030100041b00103a0000e80006600c168030160040800103606c060000080100800b01c038038030140044c001032064030000040080d00a01402c1780a024048018070220440080f0520a40000600a0141880f01e02c3700f01e0281880f⟩,
  ⟨60,7,decodeBank 8 0x8aa2185e0981df3755b3,decodeHints 0x180700601c008030420040400100000c1400000c000000060000040e80000e00c038031a4218435510f6004ed80100c0000300006600c168037560400801a0c8004080010b6000060000080100380300e00c0a0cf1620500a0014d00040300000c000010020200501780300e00c0380500a0040b8560000180000602e0c41881702e0412581702e0c418817⟩,
  ⟨60,7,decodeBank 7 0x22a88a21825f3755b3,decodeHints 0x201c0084000600c2000700e0040180102a00c0184000e01c20003006054038070840040081506c0200a8010021083d84200061c0002200600c111870500000180000061c000060020040318700c0000080000c61c0300002a000001870000180a8060080580203200600c1901605a0100180400811402013002004099db026010008040160541d0041ce0100201500802c7380b0080300d80b00006c0580c0180100000405801c0384900600c2480700e0b0018030f61ec0102c0020086901502a0b02102c0580541707b0840b82480600c0b0000000580180304900000016010102114020044d00401782c0080100b803006150038070a800c0181700e01c2280100205c1b01702e0040084508a3d41803000a05c0a80502e0000006f00c0183780000005c0300602e0100226201602d2600400805c0580b02e1145d0560582e82b07b0ac05c16017⟩,
  ⟨60,6,decodeBank 7 0x22a85e097f1f3755b3,decodeHints 0x803054004000030500000000104e0000180700601c0091f0020c0000060000180200302c01002001010010020000180100580401c038038030680041700103206403000014050010020cc0100a00400601c018050020e0008050000180000500a024048050080240200503c07802809⟩,
  ⟨60,6,decodeBank 7 0x23d8aa097cdd56cd75,decodeHints 0x60040000104e0000002a0440000200102a010020c90640100d81b0180101a00102a004050180540280c81900c000050040200100083800201402912176014000060000140203e0080140f01e00a028008080020541202a0e00a8000060000180200b00802c010020120140b805⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cd75,decodeHints 0x821002eb00180375c08415001006004001880000880180304462014000006000001880000740080103a62013800002000020160080c801803064058168040060100201500804c008010260540a8040020100200c03602c0001b016030060040000100500701c0600180e03001c0380a00600c05015068eb4008017580540a80a0020040c006032028000190140180301800000005010014050020040280400800a00801002803006150038070a800c0180500e0140280100205c0a83802e0040080502a014028000001bc030060de0000000500c014028040080d40583e06a010020050160140b84503c0140501e00a1ac02817014028120030063480380716000c0182400e01c210010021140a80808a0040084202a05415800000620030063100000002b00c0180d0040083480580baa40100201a01602c3d8860040ac0500204005c0484200a0142101702e1e802805⟩,
  ⟨60,7,decodeBank 8 0x8aa2185e097cdd56cd75,decodeHints 0x180700601c008030420040a80100000c1400000c000000060000040e80000800c168040160100200b0080040980403606c0600401c0380380375a2180500a002348008190320180000a0080400200300e00c0380500a0040b8560000180000600802c0200b02e0281880a00601c018070840ac008360021ec000060000180200b00802c0100202e0c40b831⟩,
  ⟨60,7,decodeBank 8 0x8d62a88617825f3755b3,decodeHints 0x18030483482002404201c108070021ec2000100201c108010100040000600c00000007044000030000000180000103a000020100200100200705a0100580400802c020010260100d81b0180100100200e060620180921240c0180021240080600001800010008040020170620c40b81700e1500380500a0040b8560000180000600802c0200b02e0c418817⟩,
  ⟨60,7,decodeBank 7 0x22a89221825f3755b3,decodeHints 0x20580083000600c1801602c0040180101000c0182600e01c13003006020038070340040080806c020040010020681e81a0006240002200600c11189050000018000006240000c002004061890180000080000c6240300001000000189000018040060260580b04a00600c2501602c04c018030600c0020130020105880801004c0d0130260200403d0343140980c0182b80000015c030060130000000100701c0600180e03001c038020060080103d0040b00080105876c1600200200805015068008040020040540100a0100200100603202800019014018030020000080101000405009813028040178020260080b803006150038070a800c0181700e01c1e80100205c1b01702e0040083d07a1581803000a05c0400502e0000006f00c0183780000005c0300602e0f45603d0262b01ea4f49a05c0981702e008010310140281880200405c0500a⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cd5f,decodeHints 0x8210020980180304c0841080100600400137000088018030444dc14000006000001370000740080103a4dc0e800002000058160660c8018030640581680b00600c0580801a4e00080d2700200400b0020049b80c03602c0001b016030061370000000100701c0600180e03001c03802006008010150040b000801058054170020020080100603202800019014018030020000080103d0040500580b028eac3b002016008048030060dc0380706e00c0180900e01c0480100205c0400802e00400809010024048000001bc030060de0000000900c0180b83d03e0240581f01213c0481701602c048020040d40504c06a00801009014024218030064e00380716200c0184300e01c180010020f40400807a00400830010020158000004dc0300626e0000002b00c018220860080ac05804040008010d2014028588020040800500a03405c028300120141801702e06804809⟩,
  ⟨60,7,decodeBank 7 0x23d8aa21825f3755b3,decodeHints 0x6010001821002004120010020986800804c00400824080090120210420986802604c084150240800a80018a0000740080103a6280e8000020000018a00008810821044628110000420000318a00c000130000006280000604c0180203000804c008010260c009804002010025530080c8108c90640c01900404201005826016011d78040080980200b75e02c0200c03602c0001b01603006004000010010400040b00080105810016002002008010210040602288003008410802080008053ae014008130020041000100a04c0280100603202800019014018030020000080101000405002004028040178020080087300100205c6801702e004008e61cc1580b84002e3ac109121d60d85d81704205c1803000a05c1300502e0000006f00c0183780000005c0300602e0100203601602d2700400805c0580b02e008010310140281880200405c0500a⟩
]

def nodesBlock44 : Array Node := #[
  ⟨60,7,decodeBank 7 0x23e8aa17825f3755b3,decodeHints 0x5b84000e00c1580316e11004001056004008210020980180304c084150010060040318b00c0001580000062c000060560180018b0000880180304462c110000060000018b0000740080103a62c0e800002000058b1016010218040081100200b08602c025550080c801803064110190040060100202600804c00801026098098040020100200c03602c0001b01603006004000010050b0014008210020041000100a084028010210040600180303008410802006008015540040b000801058100160020020080100603202800019014018030020000080101000405002004028040178020080085b8e600a05c1580502e00c0181c0422540e00300605c108170380040081704c05c0b8010020701305602e0000006f00c0183780000005c0300602e0100203701602c1b80400805c0580b02e008010310140281880200405c0500a⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cc6f,decodeHints 0x8400020980380704c1c81300100e0040018c000088038070446301400000e0000018c0000740080103a6300e800002000020160080c8038070640581680400e0100202600804c00801026098098040020100200c03602c0001b016030060040000100100701c060b680e03001c038020800080114c0040b000801058100160020020080100603202800019014018030020000080101000405002004028040178020080080b8400240700381203821c0e01700e01c0e00100205c1301702e0040081c04c1580b8000001bc030060de0000001700c0180b8040080dc0580b06e0100201701602c0b8020040c40500a06200801017014028200b70060ac038030480040087204c02020001002090130260560000018c00c018c60000000ac030060860100213801602c6800400810c0580b048008010d2014028200020040900500a04805c028300380142001702e0900e01c⟩,
  ⟨60,8,decodeBank 7 0x22a88617825f3755b3,decodeHints 0x80090018031a15640380710c9a40180308009003807080004108010600c001803060edc108210800040180106077018008132004158011320004c800132088018031320884c828132000018001320184c806132000158001320004c800132018158061320004c800132074008011320744c81d1320000080076c0100b00476c0c8018030600c80b02d0800100180416202eac00b10c0100d00410c0112e00407a02c0d00b0600101800406004c0080106004dda813060010008041320100601b13202c0001b13202c0600c132010000040800080380e08a0600180e7680600380708000801802aae02aab00a0f60082100210c0091b00208a0282100a0f60083d8020f60b0008010600b1d982c060008008021320080301913202800019132028030061320080000207a0080800208a050020047640500802f07a0080200208005c01803762150038077601500180308005c038070600c01800513205c158050600c00080106005cee0170600c01805613205c000001321bc030061321bc0000013205c0300607a05c02004742e800580b706e080200407a05c0580b08a05c0100266c0c40500a62a0c40100208a05c0500a⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981df376db3,decodeHints 0x2700305400c000030500000006904e0000100300e008010230100080100000c0081980305a00c1d03a0106d42d8000180000200200612001858068020008010000300000c0040280101a0200501782f00601c018050220440b805000018000050040140101700a1dc1f80501201402817⟩,
  ⟨60,6,decodeBank 7 0x2358aa17825f376db3,decodeHints 0x18020460080a80209c01c150070000080300200001c110000001a4138000080080800200801c1680401a0340400403606c060040040280102400e060038c402a020008010000300000c00802c0200b0040140104700a3002a0050220440b805000018000050080f80200501201402817⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cd5a,decodeHints 0x2700305400c000030500000006904e0000b00302c00c0680d01002c0d81b0180000100300e0080102305c0080100000c0080100b028008018070060140881102e014000060000140f81f0120140100500402401816006058180080020040000c000030020040040280101400a02402809⟩,
  ⟨60,5,decodeBank 6 0x85e0d7cddb755b3,decodeHints 0x6904e0000680d0100100d81b0180100a8080020040000c0000300200b00802c0102302a0080100000c00801004020008050020220440b805000018000050080f8020050120140281700401401047⟩,
  ⟨60,6,decodeBank 7 0x217825f376dda755b3,decodeHints 0x1a41380001a0340400403606c0600402a020008010000300000c00802c0200b00613815003006002ad0000060101680418c00c0102302a0080100000c008010040200080500200400c038020220440b805000018000050080f8020050120140281700601c0180500401401047⟩,
  ⟨60,5,decodeBank 6 0x825f3755b332065,decodeHints 0x687d0180340707e00c0380700d0740340888b0000440880d0d40440880e004044060000180000200d0100382400e0100448c811000030000010020346180d0040380100e00a044008110020200a801⟩,
  ⟨60,6,decodeBank 6 0x85e097cdd56cc65,decodeHints 0x7740001d0101a40e9dd04e000040000080200681377003409808010010780040080300d80b00006c0580c0180100000401c054070800101b04001502a0380400e01c018070e20001f87100600c0380000e01c0400704800814c240100ce0380200e0243c0088170100440ba6602e04804012024000090d500c2446a800000048030120240100906a01614035004008048058120240080900501c0380280200404807012006054018210100201081500200c04001006000001dd018030ee80000000c06003006010020160160b40b00400800c058030060080100701c0380380200400c0700e00e014028030240480180500601c09012⟩,
  ⟨60,6,decodeBank 7 0x217825f376dd56cc65,decodeHints 0x1a41380001a0340400403606c0600402a0200a8080000300000c00802c0200b00408c0a802004000030020040100800201c0380881102e014000060000140203e0080140901200a05c0100500411c0180809c00c0000c00000c0202d00800c1200300401c0100300a00c01807⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cc65,decodeHints 0x408c0e0020000db0500000006904e0000203b14c0100680d0100100d81b0180100700e0300080102302a0080100000c00801004020008090120380140881102e014000060000140203e0080140100500411c0180302a020008010000300000c00802c0200b0040280101800a02402817⟩,
  ⟨60,6,decodeBank 7 0x22a825f376dd56ccc8,decodeHints 0xc1400001a1b40b00d01a1f40600d002ee001801000030000010020346180d00400c03802004000030020040341d00d0140080885d0060440888b0000440880d06a04408805002044088050040440400311800c060000180000200d0100040a8010100080a8020100448c811⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cddb755b3,decodeHints 0x402109c0980180304c0841500800600c00139000088018030444e414000006000001390000740406903a4e413800010000020160080c801803064058168040060100200801a04ddd80d0260200400417a0100200c03602c0001b016030060040000101200300757eaf55d18c00c01824ab80902101502a2f4040080f605400842010004158000004e40600c2720000002b0180300d00400956c0580b1060100201a01602c010070041140180377401c038020060080101500471c0402317a0540a802010008010060044e400000272018030020000080101000411402004772040080020080081b0450140081580200a00c0185400e01c2a0030060140380500a2f4088170100440ba6702e0140400500a0000006f00c018378000000140300500a010020350160f81a8040080140580502e080048050840140282000a05c2101702e0080100506c0140280200405c22847⟩,
  ⟨60,6,decodeBank 7 0x217825f3755b32dc65,decodeHints 0x348270000340680800806c0d80c0080383601501c0383f00601c0382986701c0440b8080000180000600802c0200b0040380100e4cc020000060000180200b00802c0100e0040380901200602027003000030000030080b4020030040380100e00e00c0180700e00c01807⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f376dd56ccb7,decodeHints 0x2700305400c000030500000006904e0000200305a0100680d0100100d81b01801001d600061c40a80802a0200000c0000300200b00802c0100300e0080100802a0080100000c008010040200080500200601c0180702205c0400000c00003004016010058170620c40b8020620080b80300e00c03a670100000300000c010058040161081580206c71c02805⟩
]

def nodesBlock45 : Array Node := #[
  ⟨60,6,decodeBank 7 0x22a85e0981df9755b3,decodeHints 0x2700305400c000030500000006904e0000200300e010020c30100100200000c0100180700601c1d03a002004000060000180200b0081080380300e00c1a00805c0200300000c000010020200501782f00601c018070220440b809000018000060080240201700a014048170ae15c1f809⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cd71,decodeHints 0x2700305400c000030500000006904e0000200305a010020c3010010020000180100700e00e00c0a80802a0200c81900c00005004020010018070060140881102e014000060000140203e0080140f01e00a0240180700601c04015002004000060000180200b0080400100201201404805⟩,
  ⟨60,7,decodeBank 7 0x22a85e097e5f3755b3,decodeHints 0x402109c0980180304c0841500800600c0013a000088018030444e8140000060000013a0000740406903a4e8138000100002180300634c0380708800c0184300e01c180080101104197a08802000830088004158000004e8030062740000002b00c01802016008ef4018030880580b004006010020080081104b0c3088020040040880100200c0084e800000274030060040000101b03d0160101580400401c070180060380c00700e008018020040540102c0100201601505c008040020040180c80a0000640500600c0080000201558405002040008010830040281000a0040f4010140080100a3bc0280080200201200c0183700e01c1b80300602403807012110088170100440b8b102e024040090120000006f00c018378000000240300602e068028090600140481a01205c1801702e0100200906c0240480400805c1e83f012008010350141301a80200402405009⟩,
  ⟨60,6,decodeBank 7 0x22a825f9755b3320b7,decodeHints 0x30500000686d0060340687d0000340700e00e0080c81900c0082900d0040340885d0060440888b0000440880d0880440884d00404402003118010020000180100580d0080081a0020100440201118601c018c3000018000c30020340100a00430c71811008020020c3⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f97cdd56ccb7,decodeHints 0x2700305400c000030500000006904e0000180700601c041aa0100c0000060000180200302c010023be010010020000180100580401c0380380200402017002032064030020140080100a0040100a00200601c0180702205c0400000c000030170601100b80406c0100b8020140080500300e00c038b10100000300000c0681580406c0f40100a00402804809⟩,
  ⟨60,6,decodeBank 7 0x2358b217825f3755b3,decodeHints 0x18070061086f00302a00c270070020040000300c000030000000180006904e000020030200101980400801c0680d0100100d81b0180100100200e060038c402a0200a80800c00003000020010080040060c40181700a0140e0070220440b8080000180000600802c0200b02e0c418817⟩,
  ⟨60,7,decodeBank 7 0x22c8aa17825f3755b3,decodeHints 0x5b87200e00c158030101100402604809813040002020120010101c46f02600600c1304404c0200180300c634030000560000018d000018158060006340002200600c1118d044000018000006340001d0101a40e98d04e0000400001634c058040860100204400802c2180b008ef40203200600c1904406401001804008020068132a403409808010010220040080300d80b00006c0580c018010000040141c405002048008010c60040281200a0041c40101800600c0c3bf030008018020040540102c0100201601505c008040020040180c80a0000640500600c00800002004040010140080100a01005e0080200202e0900281c0600140e02403805c3881702e00c0181c18c0700e00300605c38817038110088170100440b8d002e0700400802e0000006f00c0183780000005c0300602e0100203701602c1b80400805c0580b02e008010310140281880200405c0500a⟩,
  ⟨60,7,decodeBank 8 0x8b22a85e097cdd56ccb7,decodeHints 0x38030100981300801000c1300300c0000000600000c110000001a4138000160100200b00800c1900401a0340400403606c060040140080100a00400c0c00200402017002032064030020040101780202e1502a0170061500181702205c0400000c00003004016010058020140080502405600c5b8711a0020000060000180200b00802c0100a0040280e017⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd6755b3,decodeHints 0x2700705401c000070500000006904e0000200705a0100680d0100100d81b018010038c600600c0a8080020040000c0000300200b00802c010ca00e0080102302a0080100000c00801004020008050020240480e0050220440b805000018000050080f8020050120140281700401401047⟩,
  ⟨60,6,decodeBank 7 0x22a85e097d1f3755b3,decodeHints 0x2700705401c000070500000006904e0000b00700600c04152002004000060000180202502c010020c3010010020000180100580401c0380380200402017002032064030020140080100a0040100a0020240480e0070220440b8090000180000600a014048170080240203f00413001009⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cc0f,decodeHints 0x402109c0980380704c0841500800e01c0018e000088038070446381400000e0000018e0000740406903a63813800010000020160080c8038070640581680400e0100200801a04ca900d026020040040e40100200c03602c0001b016030060040000100100701c060b680e03001c038020e2008010150040b004008058054170020100080100603202800019014018030020000080101000405002004028040178020080080b871024070038120383180e01700e01c0e07202205c0401102e3400b81c0100200b8000001bc030060de0000001700c0180b8040080dc0580b06e0100201701602c0b8020040c40500a06200801017014028388b70060ac038030802dc0082b010004158000006380300631c0000002b00c018218040081c80580bac60100204301602c210020041c40500aac400801042014028730b700a0ac0b805⟩,
  ⟨60,7,decodeBank 8 0x8d22a85e097cdd56ccb7,decodeHints 0xe00c0402604c0200400304c00c03000000018000030440000006904e0000580400802c020030640100680d0100100d81b01801005002004028010030300080100805c0080c81900c0080100405e0080b8170061505d8c20a8020000060000180200b00802c0100a0040287302b00631801824002004000060000180200b00802c0100a0040280e01c⟩,
  ⟨60,6,decodeBank 7 0x22a85e0980df3755b3,decodeHints 0x200c1500100000c140000000041380000e00c038030100040400100c0000300000800c16804008004040040080000600400802c0800400400c0380200400417002004000030020040280a0020040101780202404801807022044008080520a40000601e0c40280503e07c0200f03c0780100f⟩,
  ⟨60,6,decodeBank 7 0x22a825f3755b333cb7,decodeHints 0x30500000686d05a0340687d0180343606c00e00c2c85900c0002900d05e0340885d0060440888b0000440880d4a00440884d0c60440380300e00c0300000c0000200d074034010020680200401107004400807006004000060000040080d186034008390460040281100202043001⟩,
  ⟨60,7,decodeBank 8 0x8aa17826077cdd56ccb7,decodeHints 0x2700305400c000030500000006904e0000380300e00c043c00105380300000c0001980305a00c1d03a0101902d8000180000200400e00c038030680201700800c000030000040080801405e00c0380300e0440b8080000180000602e0c41881702e0412881702e0c41881700601c018070020040000600001ab20361060d80d0107780406781477205002805⟩,
  ⟨60,7,decodeBank 8 0x8d62a85e097cdd56ccb7,decodeHints 0x18030100540a80809c01c150070000180300000001c110000001a4138000080400800400801c1680401a0340400403606c060040040080381818805404015010018000060000400201000805c1883102e05c0385400e0440b8080000180000600802c0200b02e0c4188170481c46302404801ddf807002004000060000180200b00802c8001877406002805⟩
]

def nodesBlock46 : Array Node := #[
  ⟨60,6,decodeBank 7 0x22a825f3755b56ccb7,decodeHints 0x30500000686d02c0340687d0180340700e00e0080c81900c0082900d0ca0340180700601c000060000180200d0080340102e0040200180700601c000060000180200d008034015650044640881100201c01801000018000010080340200d0040280100110c00404801⟩,
  ⟨60,7,decodeBank 7 0x22a825f3755b3320b7,decodeHints 0x63c0002200600c1118f0500000180001a058068af0061b45781602c0340180d01a030068e10001f47080c0180340000d00401c070180060380c00700e008018020040180c80a0000640500600c008000020040e82901401a0340a03a0ca0080680d02200c088c200e1746100300604403811022000088d700c22c6b800000044030110222580889601a0344b2534a404406811022008088380141341c002004044050110100580402600600c13016118020018030100300618f000000c780c018020000000600c00200801a034040140100540100202a0501a00800400804096010258088117822588c80802204400803002548038072a400c0180100e0040080000063c0300631e0000000100c004008960022580680d12cef86180101a034008020047200500a776008010010140041803000a00408811002258008960100204b1aa2f400404001⟩,
  ⟨60,8,decodeBank 7 0x22a85e097cdd56ccb7,decodeHints 0xe20201084e060098018030600981082a0e2020018031340004d000134088018031340884d028134000018001340004d000134074040691340744d0271340000400078c0100b00478c0c8018030600c80b02d0e2010018040600100400d06004de280d06004c04008060010180041340100601b13402c0001b13402c0600c134010000040e20080380e08a0600180e788060038070e20080180229c0080a80229c0b0040080600b00a82e060008040021340080301913402800019134028030061340080000207a0080800208a050020047860500802f07a008020020e205c0180306c15003807784150018030e205c038070600c01801106005cee0170600c00400813405c000001341bc030061341bc0000013405c0300607a05c0200406ce880580b70ae100200407a05c0580b08a05c0100206c0c40500a62c0c40100208a05c0500a0e20900180306c9a803807ad75a8018030e2090038070600c0ee0011340ac040011340ac0000013426803006134268000001340ac0300607a0680200406c9900580bad35a00200407a0680580b08a1080100206c8fc0500aacf5980100229c1080500a0600c0180051340ac0b805⟩,
  ⟨60,5,decodeBank 6 0x8d2097cdd56ccca,decodeHints 0x30000000180686d0080340687d0180340700e0040280c81900c0082900d0ca03408811000018000060080340200d0040280100a01000400807000018000010080340200d0040b80100101000400808⟩,
  ⟨60,6,decodeBank 7 0x23485e097d9f3755b3,decodeHints 0x9c0040080700c000000060000041380002c00c018070029ac008030000180000302c0100200700800404004008000060040160100700e0040280100105c0080c81900c0080500200400c010040280080901200202000808000018000060061800181c0081800201c0040280100a⟩,
  ⟨60,7,decodeBank 7 0x23485e097cdd56cc54,decodeHints 0x402109c004038010020840080800e01c0319000c000038000006400000600e018001900000740080103a6401380000200005816066010038040080580200b00e01c0200801a04c0080d026020040040020100200c03602c0001b016030060040000100500701c0084b80e00401c0100a12e028010150040b000801058054170020020080100603202800019014018030020000080101000405002004028040178020080081202402407003812038004008540100202a001002070040080380000007f00c0183f800000070030060380100203701602c1b8040080700580b03800801036014028580020040700500a0480901580300e00c018010023180400818c0040080301000c01800000640030063200000000300c00c018040080d80580b4d80100200301600c018020040d80500a1600080100301400c120240c000c0e003⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981df36cd79,decodeHints 0x803054004000030440000000104e0000700e00e00c040010100040c81900c000198030ce00c32801010004dc8003740000200400601c018050020e0008050000180000503c0780280a00a0f82b80500601c018070020200080800001800006086028010020ec0bc0a02f0120140e005⟩,
  ⟨60,6,decodeBank 7 0x2388d21782607755b3,decodeHints 0x601c0181000200c040010100040080800000c0600000c00000006000004138000080100800305a0c8168a60100040400100c0000300002000c178030ce19c168e80680041700100c00003000004008018100060400280500202000808000018000061a23443001c03868cdb01c⟩,
  ⟨60,6,decodeBank 7 0x23a8d217825f3755b3,decodeHints 0x18070060d8008030100042700100201c0000300c000030000000180000104e0000200406601c16807074004040010b6000060000040080384800e3101a00105c0040300000c000080cd05e0bc0181c0063e80280500202000808000018000061a2040300101642c8d101c⟩,
  ⟨60,6,decodeBank 7 0x22a85e09819f3755b3,decodeHints 0x200c1300100000c110000000041380000e00c1b00304c004130010440001100001600c5300301a0340400103606c060000080101000b01400c0a00306800417001032064030000040080a00a01402c1780a0240480180f022044008080520a40000600a0141b80f01e02c1b80f01e0283180f⟩,
  ⟨60,7,decodeBank 8 0x8d22a85e0981df3755b3,decodeHints 0x38030100040080800200c1300100c0000000600000c11000000004138001a621c43d6c0f800cef0030100040400100c000030000202f05801002000d36803074004040010b600006000008011e38140280802c00302800c1a00105c0040300000c000010020200501780500a00c0e06000202000808000018000060380dc1b81c0380401b8100380511101c⟩,
  ⟨60,7,decodeBank 7 0x2358d217825f3755b3,decodeHints 0x4000c0180706c01c03803006080208200020900081500600c0a82402a004018010100842700100e00400821002020038070006440000600600c0319100c0000180000c6440300000e00000191000018038060006440001d0020040e99104e000008000081040201000600c081de020010018040160581980400e0100201600802c038070080200681300203409808010010008040080300d80b00006c0580c01801000004048090010180060085800700e0601001803001c038410403100c01502a124008010920540a8180020040c00600c2d80000016c018030180000000c0100200500200402804008018008010208030060701b01c03800c018410821801202400a07003805038004008540100202a001002070040080380000007f00c0183f800000070030060380100203701602c1b8040080700580b038104590410302c820a264460700c01c⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cd79,decodeHints 0x8210020980180304c084150010060040013b000088018030444ec110000060000013b0000740080103a4ec13800002000020160080c801803064058168040060100200801a04c0080d026020040040020100200c03602c0001b016030060040000100500701c4340180e21a01c0380a00600c050150680b0008010580541700a0020049d806032028000190140180313b000000050100141040200478e0401780a008010028030060700380703800c0180500e014028010020c40403806200400805010014028000001fc030060fe0000000500c014028040080d40583e06a010020050160140e04103c0140501e00a1ac0281c014028120030061040380708200c0182400e01c210010024340400816000400842010020158000004ec030062760000002b00c0180d00400834c0580b1600100201a01602c200870040ac050020400700482400a0141201c0381e802805⟩,
  ⟨60,7,decodeBank 8 0x8d22a89217825f3755b3,decodeHints 0x38031a60c0220300f800c220030100981300801000c1300300200403000000018000030440000000c0180000000803a0000984a09404c0980309400c0200401004c6280c0000300000a00400805002006060010020580b0010020100b801019032018010020260bc0100500a00c0e0600380dc1b81c0380202a0080000180000603804c1b8130040280100a⟩,
  ⟨60,7,decodeBank 7 0x2388d217825f3755b3,decodeHints 0x8600c0181606c01c0b00300610c3e0430021100080800600c04044010004018010101100400102c004008440020200b0080006480000c00600c061920180000180000c6480300002c000001920000180b0060006480001d0020040e99204e000008000f81f0020320060106981602c0c8218320640581687c0860b41900801012800801094020040320020042500c0180c8000000640300604a0000000103c004060018030307780c00200600805016090008740020040580100a1d0028010150040b000801058054170020020080100603202800019014018030020000080103c004050190cd0289b43b0020640081e0030060701b01c03800c0183c0783e81202400a0700b005038004008540100202a001002070040080380000007f00c0183f800000070030060380f0688600643443007c0c00701901c0380080123c014029120020040700500a⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cddf755b3,decodeHints 0x803054004000030500000000104e0001980305a00c0680d0100040d81b01800001929006090008080020200000c0000300800b0080100100300e0080100102a0080100000c008010660200080500200601c018050020e0008050000180000503e07c048050120140280900401401009⟩
]

def nodesBlock47 : Array Node := #[
  ⟨60,6,decodeBank 7 0x23d85e097cdd56cd61,decodeHints 0x20040000303a0000001d03a0001980302c00c0581302602c0d81b0180000100302c0080102c0580080c81900c0080100b05e0080186a006024048d4176024000060000180f81f01202c0104c00402401807006058180210540a800006000018020040040280100a00a0140e009⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cd61,decodeHints 0xbc80020980180304cf2838001006004001930000880180304464c14000006000001930000740080103a64c1380000200005816066f24018037900580b00b00600c0580801a04c0080d0260200400b0020040980c03602c0001b0160300601300000001016004060018030300580b002006008010150040b00080105805417002002008010060320280001901401803002000008010100040500580b02804017802016008048030060700b06a03800c0180902c02404801002150040080a800400809010024048000001fc030060fe0000000900c0180e03c03e0240581f01213c0481c01602c048020040d40504c06a00801009014024218030060f00b00707800c0184302c0581800100234c04008162004008300100201580000064c030063260000002b00c0183e0870080ac05804040008010d301402ab68020040800500a034070028430120142181c03806804809⟩,
  ⟨60,7,decodeBank 8 0x8d22a85e097cdd56cd61,decodeHints 0xb0030100040080800200c1300100c0000000600000c110000000041380079221c0580b00634c0180d01a0200081b0360300000a00400805002006060010020020b801019032018010020160bc0100901200c0e060002020008080000180000603802c1b80b0040280100a0860ac018360061f00080800202000006000018020040040280100a0380dc0e037⟩,
  ⟨60,7,decodeBank 7 0x23d8d217825f3755b3,decodeHints 0x6000c0182118c01c108030060c02203004809000826006004630210420981802604c084150440600a8001940000740180303a6500e8000060000319400c0001080000065000006042018001940000741301d03a6500e80004c0000204400804c018030261100980400601005bca016010108040081100200b04202c0202600804c1e013026098098040880100200c03602c0001b01603006004000010010240040b0018030580901600200600805021014009e58020040840100a7960280156e0040b01302c0580901600204c008010060320280001901401803002000008010100040500200402804017802008008730030060706301c03800c018e61cc1801202400a070108050381106a0bb04c3505d8361760701301c0380000007f00c0183f800000070030060380100203701602c1b8040080700580b03800801036014029128020040700500a⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56ccd4,decodeHints 0x402109c4340180321a0841080800600c001950000880180304465411000006000001950000740406903a65413800010000025700080c801803064110190040060100200801a04eb780d026020040040880100200c03602c0001b01603006004000010010210040600180303008410802006008010150040b004008058054170020100080100603202800019014018030020000080101000405002004028040178020080080b8030060701089503800c0181704205c0e04402205c0401102e2180b81c0100200b8000001bc030060de0000001700c0180b8040080dc0580b06e0100201701602c0b8020040c40500a06200801017014028120030061c8108070e200c01824042084200b70020ac040010560000019500c018ca8000000ac03006060010020d301602c220040080c00580b0840080110d014028630020041080500a0600700282402e0141201c0380c00b817⟩,
  ⟨60,8,decodeBank 7 0x2348aa17825f3755b3,decodeHints 0x4877c1200713600c1580318c022ba0080880041800110e00534801088020180080480041200104809801803048099e8826048004018011360184d806136000158001360004d800136018158061360004d800136088018031360884d822136000018001360004d800136074008011360744d82713600000800ae602eb900b0f80102180410e0112e80407802c2180b0f80103e0040f80c8018030480c9e8032048010018040880100400d07804c0080d79e04c04008088010008041360100601b13602c0001b13602c0600c1360100000416002ab880a10e0081000210e0091b8020820281000a0480081200204806001803048061e70180480080180279a0080a80279a0b0008010480b00a82e048008008021360080301913602800019136028030061360080000207800808002082050020047980500802f07800802002048090120051360701580504809001803048070ef81c0480901206008807000801784150040087601500080108807004008136070000001361fc030061361fc0000013607003006078070020047460dc0580b70c0dc020040780700580b08207001002670cdc0500a630c5c010020820700500a⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981df3761b3,decodeHints 0x807054004000070500000000104e000010ca00e008010010100080100000c0081980705a01c1d0010100042d8000180000200200e12001803002020008080000300000c004028010430200501782f0240480e0050020e000805000018000050040140106300a1dc1f8050120140281c⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cd59,decodeHints 0x807054004000070500000000104e0000b00702c01c0680d0100040d81b018000010ca00e0080100105c0080100000c0080100b0280080901203801400838002014000060000140f81f012014010050040240381600600c008080020200000c000030020040040280101400a02402809⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd8755b3,decodeHints 0x8210020980380704c0841500100e0040013c000088038070444f01400000e0000013c0000740080103a4f013800002000020160080c8038070640581680400e0100200801a04c0080d026020040040020100200c03602c0001b016030060040000101200700e1003416b08001c0182408000c210010023480400808000400842010020158000004f00600c2780000002b0180300d0040095d40580b0d00100201a01602c010070041004b8ca08001c0380208000801015004f4c008010800540a802002008010060044f0000002780180300200000801010004104020047a404008002008008340410140081580200a1000901c00e0480e0b00380140380500a004008310100e0188010020140400500a0000007f00c0183f8000000140300500a010020350160f81a80400801405805038080048050480140282000a0701201c038008010050d00140280200407020847⟩,
  ⟨60,6,decodeBank 7 0x217825f3761b318c54,decodeHints 0x104e0000680d0100100d81b0180100706c0020380707e000038070530080380905d00204809091000048090500080480900e0800480100109c0080100000c008010040660080500e00e04801012002020008ca000018000ca00802c020ca0060387001200401c010ca⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f3761d56cc54,decodeHints 0x807054004000070500000000104e0000200705a0100680d0100100d81b018010039a400e090008080020200000c0000300200b00802c013d400e0080100102a0080100000c0080100402000805002024070038010100040400000c000030040160100581c0481000e0020d00080e0b000e004040010100000300000c01005804016080158020d010402805⟩,
  ⟨60,6,decodeBank 7 0x22a85e0981df6755b3,decodeHints 0x807054004000070500000000104e0000202500e010020010100100200000c0101980700600c0083a002190000060000180200b0080800384800e6d01a00105c0040300000c000010020200501782f0240480e00700202000809000018000060080240201c00a014048100ae15c1f809⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cd70,decodeHints 0x807054004000070500000000104e0000202505a01002001010010020000180100700e00e0280a80102a0040c81900c000050040200100901203801400838002014000060000140203e0080140f01e00a0241200700600c00815002054000060000180200b0080400100201201404805⟩,
  ⟨60,5,decodeBank 6 0x825f3755b332863,decodeHints 0x687d0180340707e00c0380700d0740340888b0000440880d0080440880e070044000060000040200d0080340080e194038028110020440300000c0001d00d0740340100e0700441c01100e0040a801⟩,
  ⟨60,6,decodeBank 7 0x217825f67cdd56cc63,decodeHints 0x413800002f54008030000180000300800404004008000060040160100706c02a0380707e00c03807003194038070040900380905d0020480909100004809005006048090090080480900e06a0480380109c0040300000c0000380302c00c0380402c0100100e00e04874812⟩,
  ⟨60,6,decodeBank 7 0x22a89217825f6755b3,decodeHints 0x202502c0100400704201c0080400001c14000000010060040000200e80002c01c0180300802c0203001004c040c50000180000601c038038020040101600200402017002032064030020140080100a0240480e0070080240203f0123042a0090000180000600a0140481300413001009⟩
]

def nodesBlock48 : Array Node := #[
  ⟨60,5,decodeBank 6 0x8aa127d9f3755b3,decodeHints 0x70500000b00700600c000060000180202502c010020000180100580401c03803802032064030020140080100a0040100a0020240480e0070000180000600a0140481c0080240203f00413001009⟩,
  ⟨60,6,decodeBank 7 0x22a825f67cdf0755b3,decodeHints 0x1c1400002c01c01803000018000060080940b00400800006004016010008070e000400800aec000a90010020100400401c03803802032064030020140080100a0040100a002004004170020240480e0070000180000600a0140481c0080240203f0020200080900413001009⟩,
  ⟨60,6,decodeBank 6 0x8aa097cdd56ccca,decodeHints 0x7800002200e01c111e00500000380001a058068af00e1b45781602c0340380d01a030068e10001f47080c0180340000d00401c070187aa0380c00700e0086f8020040180c80a0000640500600c008000020040e82901401a0340a03a0ca0080680d02237c0881c00e0480e26b1a804403811022000088d700c22c6b800000044030110220100880901a0340480400804406811022008088380141341c002004044050110020580082600e01c1301600600403801002000001e000c018f0000000004030010020100200801a034040040080040680d002008010150140b80a80200400405001010024028010220440080900202008811⟩,
  ⟨60,6,decodeBank 7 0x22a825f67cdd56ccca,decodeHints 0x1c1400002c01c0b007000018000060080940b0040080000600401a0340700e00e0080c81900c00805002004028010040280080901203801c0000600001808811012070020090080fc0104c004024008071180040000600000418001008020020010040b80100101200400808⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56ccca,decodeHints 0x2700705401c000070500000006904e0000202502c0100680d026010020000180100700e00e008010391300080c81900c0080100405e0080901203801c0881102e02400006000018020090080fc0104c0040240b00700600c008010000180000600802c020130040280100a00a01404817⟩,
  ⟨60,7,decodeBank 7 0x22a85e097d9f3755b3,decodeHints 0x8210020980380704c0841500100e0040013d000088038070444f41400000e0000013d0000740080103a4f4138000020002181602c2d4038070f80580184300e00c180010035eebd5791a000400830af00c0158000004f40300627a0000002b00c018020160087600382516a0580b00400e010020080080f0008017b0020040040020100200c0084f40000027a030060040000101b03c0160101580400401c070187ae0380c00700e0085a8020040540102c0020041601505c008008020040180c80a0000640500600c008000020155dc05002040008010680040281000a0040f0010140080100a3d6028008020020122d40901c00e0480e26c03802403807012004008540100202a001002024040090120000007f00c0183f80000002403006038068028090860140481a0120702181c0380100200906c024048040080701e03f012008010350141301a80200402405009⟩,
  ⟨60,6,decodeBank 7 0x22a825f3755b332854,decodeHints 0x38280000343681601a0343e80c01a038070070040640c8060041480686501a0480e007000018000060080340200d0040280100a00201c46001000018000010080340200d0040b801001010004008084d601c000060000180200d0080340100a0040280881100202000808⟩,
  ⟨60,7,decodeBank 8 0x8aa17825f67cdd56cc54,decodeHints 0x807054004000070500000000104e0000b00702c01c00d7c0021c8000060000180200702c01002001010010020000180100580401c0380380200400417002032064030020140080100a0040100a002024070038010100040400000c0000301c06e0dc0e00406e0100e0020140080526c00e004040010100000300000c10c1580406c7600100a00402804809⟩,
  ⟨60,6,decodeBank 7 0x22a89219825f3755b3,decodeHints 0x8de02c0040400700600c0080800210c0000705000000001018000030000000180b00702c01c0200401004c040c50180000600001c0380380200400416002068008010080320640300200404c178020240480e00700205c0085600a0140b808000018000061582b01b8170040280100a⟩,
  ⟨60,7,decodeBank 7 0x22a86617825f3755b3,decodeHints 0x12021042100038070800840182400e00c00821002100038de0800841080100e0045b872010004158010006580002200e01c111960500000380000c6580300005600000196000018158060006580001d0020040e99603a000008000080580203200e01c1901605a010038040161c805804060010020d000802c1800b0081c80201300200409bd9026010008040080300d80b00006c0580c0180100000400401c070182da0380c00700e0082000201434805002084008010400040282100a004f4c0102c00200416040058008008020040180c80a0000640500600c00800002004040010140080100a01005e0080200202e1000901c00e0480e0c603805c038070380c0028170480140b83002e0701201c038004008171a005c0b8010020703905602e0000006f00c0183780000005c0300602e0100203701602c1b80400805c0580b02e008010310140281880200405c0500a⟩,
  ⟨60,7,decodeBank 8 0x8aa1985e097cdd56cc54,decodeHints 0x1080704201c008070420040400100001c1400000c000000060000040e80000801c168040160100200b0080040980403606c0600401c038038020140080100a0040041600203206403002004010178020240700381c0a81500e0010a80040e00000c0000300401601005802014008050c600e0c01580116e1c8000060000180200b00802c0100a0040280b817⟩,
  ⟨60,6,decodeBank 7 0x22a85e09815f3755b3,decodeHints 0x200c1500100000c140000000041380000e00c038030100040400100c0000300000800c16804008004040040080000600400802c0800400400c0380200400417002004000030020040280a0020040101780202404801807022044008080520a40000601e0dc0280503e07c0200f03c0780100f⟩,
  ⟨60,6,decodeBank 7 0x217825f3755b31b054,decodeHints 0x104e0003686d0100042f05e0180000706c05c0380707e00c0380705305e0380905d00204809091000048090500dc0480900e44e0480380109c0040300000c0000200406601c0100e00e038038121d20480080800200c0000600000c0183b04a00c0180e1940380281200601c43803⟩,
  ⟨60,7,decodeBank 8 0x8aa17826077cdd56cc54,decodeHints 0x807054004000070500000000104e00003bda00e54c040010100040300000c0001980705a01c1d0010100042d8000180000200400e120038580680041700100c000030000040080801405e0480e00700202000808000018000060380dc1b81c0380401b8100380511481c00600c008080020200000600001abe8360d00d85e0107ac040100147a405002805⟩,
  ⟨60,6,decodeBank 7 0x217825f3755b46cc54,decodeHints 0x104e0000680d0100100d81b0180100706c02a0380707e00c038070530ce0380080800201c0000c00001c0202d00801c0100e00403800d7f0023a4000060000180257e0083a40100e00403809012002020008030000180000300802c020030040380100e10e00c02803⟩,
  ⟨60,7,decodeBank 7 0x217825f3755b318c54,decodeHints 0x65c0001d0020040e99704e000008000080200681300203409808010010008040080300d80b00006c0580c0180100000401c054070800021b04001502a0380080e01c018070e20001f87100600c0380000e01c0400704800814c240100ce0380200e024004090950101744a80100204804012024000090d500c2446a800000048030120240100906a016140350040080480581202425c0909701c0384ba2b4540480701200e054038210020041081509c01c0080100e01803197000000cb80600c01c0000000e040038160080100b01006601c020040480900100701c0380389700e25c090127b625c74807024048018010025b4040082da0040080301000c0180000065c0300632e0000000300c00c018040087640580b7ae0100200301600c0189700625c0700e12ef506500301c0381202400a00c0901200625c0189700e01c4b9a42d600c03803⟩
]

def nodesBlock49 : Array Node := #[
  ⟨60,7,decodeBank 8 0x8aa2485e097cdd56cc54,decodeHints 0xb00702c01c0400704201c0080100001c14000000030060000000200e80002c01c0b0070080100401318a0300000c000038070070040081602c0040080402e0040640c8060040080982f0040480e0070380dc1b81c0380202a0080000180000603804c1b8130040280100a00600c180721a00c0180087b202000006000018f08137b004c0100a00402802805⟩,
  ⟨60,8,decodeBank 7 0x22a85e097cdd56cc54,decodeHints 0x4800410801048098038070480981082a048004038011380004e000138088038071380884e028138000038001380004e000138074008011380744e027138000008002a60100b0042a60c8038070480c80b02d048010038040e40100400d07804c0080d7be04c040080e4010008041380100601b13802c0001b13802c0600c138010000040480080380e048061ef00e04806003807048008120027ba0080a8027ba0b0008010480b00a82e048008008021380080301913802800019138028030061380080000207800808002082050020047b80500802f0780080200204809012012048070ef81c048090038070e40700080106c15004008762150008010e407004008138070000001381fc030061381fc00000138070030060780700200406c0dc0580b70e0dc020040780700580b0820700100206cce40500a634c64010020820700500a048090ef8031380ac038030e40c00080106c9a804008b0b610008010e40c0040081380ac0000013827003006138270000001380ac0300607810c0200406c9940580bb07608020042a610c0580b0820800100206c9000500ab03600010020820800500a048090120051380ac0e005⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cde6755b3,decodeHints 0x8210020980180304c084150010060040013e000088018030444f8140000060000013e0000740080103a4f813800002000020160080c8018030640580b0040060100200801a04c0080d026020040040020100200c03602c0001b01603006004000010120030060f00380710e00c0182400e01c180010020f40400810c00400830010020158000004f80300627c0000002b00c0180d0040080680580b0340100201a01602c0100701c0600180e03001c03802006008010150040b0008010580540a8020020080100603202800019014018030020000080101a00406802004034080178020080080507a014008100020040800100a0400281a8030060f00380707800c0183500e01c1a8010020f40400807a004008350100201a8000004f80300627c0000003500c0180d0040080d40583506a0100201a0160fc0d01a00a0d415805040008010350140d41a80200408005047⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cd6b,decodeHints 0x8210020980180304c084150010060040013f000088018030444fc140000060000013f0000740080103a4fc13800002000020160080c801803064058168040060100200801a04c0080d026020040040020100200c03602c0001b016030060040000100100701c0600180e03001c03802006008010150040b000801058054170020020080100603202800019014018030020000080101000405002004028040178020080081a8030060f00380707800c0183500e01c1a8010020f40400807a004008350100201a8000004fc0300627e0000003500c0180d0040080d40583e06a0100201a01602c100020040d40504c06a00801020014028120030060f00380707800c0182400e01c180010020f40400807a00400830010020158000004fc0300627e0000002b00c0180d0040080680580b0340100201a01602c100020041e80500a040008010200140280d01a00a0ac1a805⟩,
  ⟨60,8,decodeBank 7 0x22a85e097cdd572db3,decodeHints 0x23400410801280098018030780981082a2340040180113a0004e80013a0880180313a0884e82813a0000180013a0004e80013a0740080113a0744e82713a000008004de0100b0044de0c8018030340c80b016234010018042800100400d03404c0080d03404c040082800100080413a0100601b13a02c0001b13a02c0600c13a010000042340080380e0400600180e04006003807234008018024dc0080a8024dc0b0008010400b00a8152800080080213a0080301913a0280001913a0280300613a008000020340080d002034068020040340681002f2340900b0164de10c0180303410c0b016234090018032800c00a8154dc108008010341080a8152800c00080113a0ac790f213a2740000013a274790f213a0ac000000340680d01013a0ac020040340800d01413a0ac01002234014018120780700381207807001803234014038052800140081107a05c0401107a05c008012800140400513a0140002913a03c0302913a03c0000013a014030050340140201f0340240581f03402402004034014058050400240101e0400140501e04001401002040024050090340140d0050340d6c38350340d6c30350340140d005⟩,
  ⟨60,4,decodeBank 5 0x23b8a1f3755b3,decodeHints 0x1380106600c1680301a0340400101c038038030680041700101402c1780a024048018070220440080814e29c3700f1502a03180f⟩,
  ⟨60,5,decodeBank 6 0x8aa28831f3755b3,decodeHints 0x803054004138037c000c0000006600c1680301a03404001b1602c05d8a01c0380380306800417001b120280501801402c1780a02404801807022044008084ec03c07d8814e29c3700f1502a03180f⟩,
  ⟨60,5,decodeBank 6 0x8aa0c7cdd56cd08,decodeHints 0x30500001980305a00c0d81b0180000700e00e00c0c81900c0000500b05e0280901200601c14829000018538a70dc03c540a80c603c008030540041380001a034040010020d01700102204400808⟩,
  ⟨60,5,decodeBank 6 0x8ee17831f3755b3,decodeHints 0x80305400400000050005f000106600c1680301a0340400102602c0581301c0380380306800417001b1c0280558d01402c1780a024048018070220440080802e03c07d8c14e29c3700f1502a03180f⟩,
  ⟨60,5,decodeBank 6 0x85e0c7cdd56cd09,decodeHints 0x104e0000680d0100040d81b0180001a00105c0040c81900c0000500b05e0280881100202014829000018538a70dc03c540a80c603c01801054004140000060cc1680301c0380380302404801807⟩,
  ⟨60,6,decodeBank 6 0x8aa17831f3755b3,decodeHints 0x20840082600600c13021054004018010016480002200600c11591050000018000016400001d0020040ed8f04e000008000160581983200600c1901605a02c01803016020068130020340980801002c008010260300d80b00006c0580c01804c0000001401c070180060380c00700e028018030140541a02c0020041601505c028008010300180c80a0000640500600c060000000140400501401602c0a01005e0280580a01e00c0901c00e0480e00300603c0380701e004088170100440b80100203c0400802e0001480f00c0a40780000005c0300601e0d85383601629db28360dc03c0580f01e0d8540360142a1778360c603c0500f⟩,
  ⟨60,6,decodeBank 6 0x8aa20825f3755b3,decodeHints 0x20840082600600c13021054004018010007880002200600c111e2050000018000007880001d0020040e9e204e000008000160581983200600c1901605a02c01803016020068130020340980801002c008010260300d80b00006c0580c01804c0000001401c070180060380c00700e028018030140540102c0020081601505c028008010300180c80a0000640500600c060000000140400501401602c0a01005e0280580a01e00c0901c00e0480e00300603c0380701e004088170100440b80100203c0400802e0001480f00c0a40780000005c0300601e0d80783601602c998360dc03c0580f01e0d8078560140282b0360ac03c0500f⟩,
  ⟨60,6,decodeBank 7 0x22a88217825f3755b3,decodeHints 0x1080304200c1080304200c0080100000c140000000740e8000000740e80006600c168030080100980b01604c0980b03606c0600001c038038030040081600a0140b01600a0320640300001402c1780a0240480180700a0140b80f01e05c0b80f0520a40000601e02c3700f01e0283180f⟩,
  ⟨60,6,decodeBank 6 0x8ce17825f3755b3,decodeHints 0x20840082600600c130210540040180100078c0002200600c111e30500000180000078c0001d0020040e9e304e00000800016058020320060101901605a02c01803016020068130020340980801002c008010260300d80b00006c0580c01804c0000001401c070180060380c00700e028018030140541a02c0020041601505c028008010300180c80a0000640500600c060000000140400501401602c0a01005e0280580a01e00c0901c00e0480e00300603c0380701e004088170100440b80100203c0400802e0001480f00c0a40780000005c0300601e0d80786001602c300360c003c0580f01e0d807836014028940360c603c0500f⟩,
  ⟨60,6,decodeBank 7 0x2338aa17825f3755b3,decodeHints 0x180300209813001002098130010000881100000008811000000004138000080101900b0160c81900b01a0340400103606c060000040080c00a0140600c00a068004170010320640300001402c1780a00a0140e00f01e0700e00f022044008080520a40000601e02c3700f01e0283180f⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cdb0,decodeHints 0x8210020980180304c08415001006004001540000880180304455014000006000001540000740080103a55013800002000058160660c8018030640581680b00600c0580801a04c0080d0260200400b0020040980c03602c0001b016030060130000000500701c0600180e03001c0380a00600c050150680b0008010580541700a0020040c0060320280001901401803018000000050100140500580b0280401780a016028078030240700381203800c0180f00e01c0780102205c0401102e0040080f0100200b80005203c0302901e0000001700c0180783601e0d80580b6cc0d83700f01603c0783601e0d80500a5e00d83180f01403c120360480d801803b2e0dacb02400600c180360600d800801b2a0daca03000200415954056550000002a80dac982b0000000d036008080058040400d81001a01602c10036004068050020340d80d0200140281b03600a0ac07805⟩
]

def nodesBlock50 : Array Node := #[
  ⟨60,5,decodeBank 6 0x8aa17832087cdd5,decodeHints 0x200c1500100000c300000000042b0000240480180f0220440080f0520a40001706600c638031c6004608010080100480014e29c7000318000c1a0011520040100200a000540a80c61b817863⟩,
  ⟨60,6,decodeBank 7 0x22a85e0c81df3755b3,decodeHints 0x40182a002000018280000000082700001c0180700602000808002018000060000cc0182d0060e80080800216c0000c00002c0580700601c018340020b8008060000180000a0140400a02f02404801807022044008080520a40000601e0d9f080f01e041ac80f01e0517180f⟩,
  ⟨60,6,decodeBank 7 0x22a8820981df3755b3,decodeHints 0x40182a002000018280000000082700001c0180700602000808002018000060000cc0182d0060e80080800216c0000c00002c0580700601c018340020b8008060000180000a0140400a02f02404801807022044008080520a40000601e1582b00f01e6a1ad00f01e1582b00f⟩,
  ⟨60,6,decodeBank 7 0x23385e0981df3755b3,decodeHints 0x40182a002000018280000000082700001c0180700602000808002018000060000cc0182d0060e80080800216c0000c00002c0580700601c018340020b8008060000180000a0140400a02f02404801807022044008080520a40000601e1803000f01e0403000f01e68d7200f⟩,
  ⟨60,5,decodeBank 6 0x8aa17825f37559d,decodeHints 0x200c1500100000c140000000041380003e1406381f03e4946081f03e52cab81f03c4906001e03c1345481e03c5348e81e03c07c1781e02404801805022044008050520a40000500a07c0201f0120780101e⟩,
  ⟨60,6,decodeBank 7 0x22a85e09821f3755b0,decodeHints 0x803054004000030500000000104e0000901200603c0881100203c1482900005c1980318e00c71801182004e70002ae0000580f1c000c600030680045480136e0008e80001403c3186e05e18c028030c000c028010ac004028007c2001f10050080100480500400802809⟩,
  ⟨60,7,decodeBank 8 0x8aa17826077cdd56cdb0,decodeHints 0x803054004000030500000000104e0000380300e00c040010100040300000c0001980305a00c1d0010100042d8000180000580b00e00c038030680041700100c000030000140280801405e0480900300e044088010100a41480000c03c1b3e301e041ae00f01e0517300f0b000ecd0030c8006cc801110002cc0002ce0ac0d0100400401001403405002805⟩,
  ⟨60,6,decodeBank 7 0x22a85e077cdd56cd30,decodeHints 0x40182a00201c01807006020008080020cc0182d0060e80080800206c0d80700601c018340020b8008190320400a02f0522440182905222c00829052014028290520f804829052014028290000a00180000009c00800000018030000000302d8000000180300000a0a400029⟩,
  ⟨60,6,decodeBank 7 0x22a826077cdd56ccd0,decodeHints 0x182800001c01807006018000060000cc0182d00616c0000c0000340680700601c01806000018000020040400a02f0221740181102222c00011022014028110220f804811022014028110020a80180100009c00001002020040010020201d0010020b81a00100a04400811⟩,
  ⟨60,6,decodeBank 7 0x217826077cdd56cc6d,decodeHints 0x82700002000808002018000060000e80080800216c0000c000010020340020b8008060000180000e01c0400a02f0241740081202424400012024014028120240f804812024014028120020a8008030000a00000300601c038030060b41980300601c0380300a04801812⟩,
  ⟨60,7,decodeBank 8 0x8aa178260881df3755b3,decodeHints 0x803054004000030500000000104e00001d9d0062f000d9c00233c0059b0002200380300e00c040010100040300000c0001b02b06600c16803074004040010b60000600045e0400200400e00c038030680041700100c000030004ae050010020200501780300e00c028010700040280000c0000280f00a13c02be300a0f80480501201402809⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56514c,decodeHints 0x803054004000030500000000104e0000f85005a07c0f92501007c0f94b01807c0f12400e0780f04d05c0780f14d00c0780f01f05e0780280300e00c028010700040280000c0000281f07c07c0481e00a0780901200601c08811002020148290000180201f004079f1005⟩,
  ⟨60,7,decodeBank 8 0x8aa17826077cdd56cd4c,decodeHints 0x803054004000030500000000104e0000380300e00c040010100040300000c0001980305a00c1d0010100042d8000180000580b00e00c038030680041700100c000030000140280801405e00c0380300a0041c00100a0000300000af900283600a0f8048050120140280900601c01807002020008080000180000609e0ad1c8104be05007805⟩,
  ⟨60,6,decodeBank 7 0x22a87a17825f3755b3,decodeHints 0x380300e00c2700305400c0080100000c14000000018030000001a41380000800c1680400802c098040080e8040040080000600400400c03802004028160020040201700200400003002004010178020240480180701e05c028050700e00b8080520a40000603e07c0200f03c0780100f⟩,
  ⟨60,6,decodeBank 7 0x2318aa17825f3755b3,decodeHints 0x18030020200400100201c150010000180300000001c140000000041380000802c0800400801c1680400800404004008000060040040280c0020041200380200400417002004000030020040101780201e070028051d201c0e007022044008080520a40000603e07c0200f03c0780100f⟩,
  ⟨60,6,decodeBank 7 0x22a88a17825f36cd94,decodeHints 0x400c0380209c00c15003002008000030500000000200c0080006904e0000200305a0100200205e0080206505c010020000180100901200601c0f01e00403c0782e1740b8148290000180f81f00803c0380300e00c050020580081702c05c2600300000c0000580405e01002805⟩
]

def nodesBlock51 : Array Node := #[
  ⟨60,6,decodeBank 7 0x2388aa17825d56cd94,decodeHints 0x6010008040100100088c0e000400004018010000db0500000000104e0000100405e0080106705a0080100105c0080100000c0080f81f00803c0782d1a20b408811002020148290000180f01e00403c058040200101683205a298040010100040300000c000050020ec00802805⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cd94,decodeHints 0x8210020980180304c084150010060040010e00008801803044438140000060000010e0000740080103a4381380000200002016009684018037cc058168040060100200800804000801020020040040020100200c0084380000021c03006004000010010070040500180302801c0380200600801015005680008017ca05417002002008010060044380000021c01803002000008010100040500200402804017802008008078030240700381203800c0180f00e01c0780102205c0401102e0040080f0100200b80005203c0302901e0000001700c0180780403ee700801f09e0100200f02003c0780203ccc00a01e0d60080100f02803c1200700e21c01803b3e01c0382400600c1800801021800801b3c020040300020041580600c4380000021c0180302b0000000d010016080020040400400801a00801010014014068010020340500a0200040082784f00a0ac07805⟩,
  ⟨60,7,decodeBank 8 0x8aa17826077cdd56cd94,decodeHints 0x803054004000030500000000104e0000380300e00c040010100040300000c0001980305a00c1d0010100042d8000180000200400e00c038030680041700100c000030000040080801405e0480900300e044088010100a41480000cf902780f01e041ae80f01e0517380f00e00c038030100040400100c0000300006c0ac080200200680a01a02808002805⟩,
  ⟨60,7,decodeBank 7 0x22a88a17826077cdb3,decodeHints 0xb001c0381400600c0a00700e1600180305c0842705800600c2c0210540b80180319e33c0082e028004001410000880180304450414000006000001410000180a00600c50403000028000001410000741706903a5041380005c0001600700e1240180309201c0382c00600c210140040b00d0020580501604219e1082102e05c0b09982c0580b81704219e2602480600c0b0000000580180304900000017816067688018030b00581682f00600c228140280bc0d02f05e0501783d0341d83202e0ca0bc7386505e0b8170640c81901780c0b6504000002820300602f000000100200080bc1600400a00c0901c00e0480e0030060140380501211404805028014028b100a0240a00900a1900281705c0e00ba6802e0141700500a0001480f00c0a4078000000140300501ef94078050580140288300a03c1600f00a0f40280905e0f804a5601201417805⟩,
  ⟨60,7,decodeBank 7 0x2388aa1782607755b3,decodeHints 0x1782f00182d02000c008100020203203a010040040010c8004008580020981688c04c1903800105a004001420000300805b0185080600002000000142000088168db0445081400005a000001420000740080103a50813800002000218100080c8100040640400804317810c2182d05a0c8940320640b4168431782981900801012800801094020040320020042500600c0c8000000640180304a0000001e0100201d8100760ec0401783c0400bc2c02d0ce1d8740670ec0b4168580b01603b01506968c008010b0054170760020043b00600c50800000284018030760000000d01a0041d81900200a0f0028090200f8048b00120140800500a1600281c05a1a80e26d0380141680500a004088170100440b8010020140400500a0001480f00c0a4078000000140300501ef98078050640140286800a03c1900f012104048050ec01402a2e00a0243b009⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cd99,decodeHints 0x803054004000030500000000104e0000200305a01002001010010020000180100100300e0080100105c0080100000c0080100405e0080901200601c08811002020148290000180f81f00803c0f01e00403c0380300e00c040010100040300000c000058040260100500205800802805⟩,
  ⟨60,7,decodeBank 7 0x22a89e17825f3755b3,decodeHints 0x2180700e160018030b001c0384300600c0402109c0980180304c0841500800600c99864002020158010006600002200600c1119805000001800000660000060560180319800c000158000006600001d0101a40e99804e000040000260581984a00600c2501605a04c0180308a0f4020130560103200807404c7383a026020040640c83140980c0b62b80000015c030060130000001600700e0500180302801c0382c00600c1e83d0040b0158020280541a02c0100201601505c050040080280180302c0000001600600c050000000580404081402604c0a01005e0b00981300a00c0901c00e0480e0030060140380501f6900780506c0140288600a03c1b00f00a190028170100e00b9db02e0140400500a0001480f00c0a4078000000140300500a0f4028090260f8049cf0120140980501211404805058014029bb00a02416009⟩,
  ⟨60,7,decodeBank 8 0x8aa2785e0981df3755b3,decodeHints 0x380300e00c2700305400c0080100000c14000000018030000001a41380000e00c038030840ac0413319e018000060000cc0182d0061140803a0740203205b0000300001302601c018070060f40a0340100b8040060000180002c0580400a02f0240480180501e0140280f00a0e00b8050520a40000501e0140280f00a0f80480501201402809⟩,
  ⟨60,6,decodeBank 7 0x23d8aa097cdd56cccf,decodeHints 0x18010000040e8000000841100001a03409801026324898130b600006000046004160011002001082c00c0000300010204c178130220440080500a4486a0050520a40000500a0f80480501201402809086004040010540a81302100c00003000008010130130040080a02c00a03c0280f⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cccf,decodeHints 0x821002190018037d008410801006004001990000880180304466414000006000001990000740080103a6640e80000200009816066128018030940581681300600c3206401a04c0080d0260f4098640020040980c0b62b80000015c030060130000001600700e0500180302801c0382c00600c0a3e70460b000801058114160140020040a00600c0b0000000580180301400000016010102050098130280401782c02604c028030240700381203800c0180500e0140280102205de001102e004008050c80140280005203c0302901e0000000500c0140283d00a0240983e012d8c04805026014048450120141600500abb4028090580241200700e9c0018030c801c0382400600c321330100ac0080105601803199000000cc80600c0ac0000006019002042026010210640840c0098130840500101a058008320140281081602c06c0140288601e03c4180500a0d80780f⟩,
  ⟨60,7,decodeBank 8 0x8aa17826077cdd56cccf,decodeHints 0x803042004000030500000000103a0000380300e00df3933002018000060000cc0182d0061900081000216c0000c00004c0980700601c018140024cc008060000180002c0580400a02f02404801805022044008050520a40000501e0140280f00a0f8048050120140280900e00c038030100040300000c0002102b0c8040678100280680a0cf00a03c0280f⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cd9b,decodeHints 0x803054004000030500000000104e0000200305a01002001010010020000180100100300e0080100105c0080100000c0080100405e0080901200601c08811002020148290000180f81f00803c0f01e00403c0380300e00c040010100040300000c000058040200100500203000802805⟩,
  ⟨60,7,decodeBank 7 0x23a8aa17825f3755b3,decodeHints 0x9405800601c158030021900080808402004058010004210010020840082600e01c1302105400403801000668000060560180319a00c000158000006680002200e01c1119a050000038000006680001d0020040e99a04e000008000820f002010056010080160660c8038070640581681000e01c1900807404000801020020040320020040800c0b60c800000064030060100000001e03c004060158020b001c038181d01200c00700e1602c0c40300541a0490020042481505c06000801030018030b60000005b00600c06000000030040080140643340a01005e0601902f01f6940780506c0140288700a03c1b00f00a1600281c00e01c0e1de0380140380500a004088170100440b8010020140400500a0001480f00c0a4078000000140300500a0f0028090200f8049d00120140800501210404805030014029bc00a0240c009⟩,
  ⟨60,7,decodeBank 8 0x8ea2a85e0981df3755b3,decodeHints 0x18030020200400100201c150010000180300000001c14000000004138000860ac0392817802000808002018000060001040803300e0b40383a0020200085b000030000320200f00a00709001c2c0340020b800806000018000180300400a02f01e0140280f00a01c0e005022044008050520a40000501e0140280f00a0f80480501201402809⟩,
  ⟨60,6,decodeBank 7 0x23d85e097cdd56cc6c,decodeHints 0x80100000c0e8000000740e80004a00c6480315e32464da60b60000600001c03840003030200640c800c00003000100324178800240480180500a05c0b8050520a40000500a0f8048050120140280908400c038030540a81082600c00003000008010080c90040081088000a03c0280f⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cc6c,decodeHints 0x8580020980180304cfa8130010060040019b0000880180304466c110000060000019b0000740080103a66c13800002000083e904a0c8018030640f01901000600c1900807404000801020020040320020040800c0b60c800000064030060100000002c05801c0600180e0301040c05800600c0c01506812400801092054170180020040c00600c2d80000016c018030180000000c010020050190cd028040178180640bc02803024071ed01203800c018050b00140280102205c0401102e004008050100140280005203c0302901e0000000500c0140283c00a0240803e012d9004805020014048410120140c00500abb8028090300242c12800e0ac01803048020042700020042c008010090008010560180319b000000cd80600c0ac00000086040020200640102c01002010c1903204816001043030008218580860900c01806c0140288701e03c3400500a0d80780f⟩
]

def nodesBlock52 : Array Node := #[
  ⟨60,7,decodeBank 8 0x8aa17826077cdd56cc6c,decodeHints 0x80304c004000030440000000104e001f49280060200080800201800006000040019280060e80080800216c0000c0000c808058006050018340020b800806000018000180300400a02f02404801805022044008050520a40000501e0140280f00a0f8048050120140280900e00c040010100040300000c0002182b020080080bc0b00505e01400a03c0280f⟩,
  ⟨60,7,decodeBank 8 0x8f62a85e0981df3755b3,decodeHints 0x1803002004108260540000e81d000000108220000000e81d00009138058048085f50212fc099f4026200018000060001900801017804010864020098080100c816c0000c00001002058028050678210280842c01404c1600a006000018000020040400a02f00a05c0b80500a2540e00500a05c0b8050520a40000501e0140280f00a0f80480501201402809⟩,
  ⟨60,8,decodeBank 7 0x22a85e0981df3755b3,decodeHints 0xb0004108010c8098018037da0981082a0b000401801110000440001100880180311008844028110000018001100004400011007400801110074440271100000080017810c03807b656c401803b609c8038070b010c0180319e10804008b5f6b800801b5a9c4040080c8108008011100ac0300611022000000110220030061100ac000001780400b0331782f001803078fb00b02d0b0040018030c81900403a0340400080107a040040080c8190008011100400605b110220000001102200600c1100400000004008010004110040158040b01600380704005001803082050038070b01600180319e0500a83419e33c0080108afac0a82e0c805000801110050030061102200000011022003006110050000000340680d0021100501580203406808010040050100140340681002f0b0014018127b807003812798070018030b0014038050c80140081178605c0401176405c008010c8014040051100140002911003c0302911003c0000011001403005b5803ed580fb540151f005b520151a805b5003ed380f034015d50057480240803e712025c400903401408005040025a50096740140a0056380158d8050400240a009⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56ddb3,decodeHints 0x8210020980180304c084150010060040010f0000880180304443c140000060000010f0000740080103a43c13800002000020160080c8018030640580b0040060100200801a04c0080d026020040040020100200c03602c0001b01603006004000010010070040500180302801c03802006008010150056cc0080108a054170020020080100600443c0000021e0180300200000801020004050020040280800a002008008120030061040b01610e00c0182402c058180010021140400810c004008300100201580000043c0600c21e0000002b0180300d0040085980580b09e0100201a01602c0d0020041e80a00a0400080101a028050028030061040380708200c0180500e014028010020c404038062004008050100140280000043c0300621e0000000500c01402804008e740583e09e01002005016014100020040140a00500a0080102002818c1002001201415805⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cdaf,decodeHints 0x8210020980180304c08415001006004001430000880180304450c14000006000001430000740080103a50c13800002000020160080c801803064058168040060100200801a04c0080d026020040040020100200c03602c0001b016030060040000100500701c0600180e03001c0380a00600c050150680b0008010580541700a0020040c0060320280001901401803018000000050100cc050020040280401780a008010028030061040380708200c0180500e014028010020c404038062004008050100140280000050c030062860000000500c014028040080d80580b6d0010020050160141002003c0140501e00a1ac02820014028120030061040380708200c0182400e01c180010021140400808a004008300100201580000050c030062860000002b00c0180d0040080d80580b2c00100201a01602c0d0200341e80500a0401ac0101a014008100200120ac02805⟩,
  ⟨60,7,decodeBank 7 0x22a85e0981df3755b3,decodeHints 0x1042004130030060981082a00200c00800220000110030060888802800000c000002200000e801002074880270000040004300e01c2c0030061600380708600c0184201002032001002190040080840040082b00c01888000000440030060560000001002c0cc5e0030060f00b02d02000c019d10100e808001002040040080c80040081001816c880000004400600c020000000200340100802b0096d00380702800c0181400e01c2c0030060500a83419e0040083d02a0b80a001002050030062200000011000c0180a0000000680d0020280ac0101a0200400a0200280680d02f00a00c0901c00e0480e0030060140380500a004088170100440b8010020140400500a0001480f00c0a4078000000140300501e59c0780506c0140284f00a03c1b00f00a068028090200f80497701201408005012080048050280140296400a0240a009⟩,
  ⟨60,8,decodeBank 7 0x22a85e097cdd56cd58,decodeHints 0x1ac004108011b0098018030820981082a1ac0040180112600049800126088018031260884982812600001800126000498001260740080112607449827126000008001ca0100b0041ca0c8018030780c80b0161ac010018041b00100400d03404c0080d07a04c040081b0010008041260100601b12602c0001b12602c0600c126010000041ac3580380704005001803040050038071ac358018033c80500a8343c8790008010401140a82e1b0050008011260500300612624c0000012624c03006126050000000340681006604005010014034068020041ac0140181208207003812082070018031ac014038051b00140081108a05c0401108a05c008011b0014040051260140002912603c0302912603c00000126014030050340140201f74a0240581f7140240200403401405805040024100090400140a0050400158e8050400240a0091ac10c0380704008001803040104038071ca10c018031b00c0100303c810800801040108100421b00c0008011260ac0300612624c0000012624c030061260ac00000040fb8100101260ac020040340680d0021260ac0a0020416d802805040080048090416d40280504008004809⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56e5b3,decodeHints 0x8210020980180304c08415001006004001110000880180304444414000006000001110000740080103a44413800002000020160096dc01803078058168040060100200800804000801020020040040020100200c00844400000222030060040000100100701c0600180e03001c03802006008010150040b0008010580540a802002008010060320280001901401803002000008010100040680200403404008002008008120030060f00380710e00c0182400e01c180010020f40a81510c0040083002a05415800000444030062220000002b00c0180d0040080680800b0340100201a020040100020045a00500a09e00801020014028048030060dc0380706e00c0180900e01c048010020f40400807a0040080901002404800000444030062220000000900c0180d004008024080090120100201a02004004802004cc40504c0d6008010090140240d01a00a02415805⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cdab,decodeHints 0x8210020980180304c08415001006004001440000880180304451014000006000001440000740080103a51013800002000058160660c8018030640581680b00600c0580801a04c0080d0260200400b0020040980c03602c0001b016030060130000000100701c0600180e03001c03802006008010150040b00080105805417002002008010060320280001901401803002000008010100040500586602804017802016008048030060dc0380706e00c0180900e01c048010020f40400807a0040080901002404800000510030062880000000900c0180d01a03e0240581f01213c0481a01602c048020040d80500a5e600801009014024120030060f00380707800c0182400e01c180010020f40400807a0040083001002015800000510030062880000002b00c0180d01a0340680580b03413c0201a016010100020040d80500a2ca008010200140280d01a00a0ac04805⟩,
  ⟨60,8,decodeBank 7 0x22a85e097cdd56cd6f,decodeHints 0x1fc004108011b8098018030780981082a1fc004018011280004a000128088018031280884a028128000018001280004a000128074008011280744a027128000008003ca0400b0333ca794018030340f00b02d1fc040018031b83700403a03404000801034040040081b8370008011280400605b128250000001282500600c128040000001fc0080380e0400600180e078060038071fc008018024e60080a8024e60b00080107a0b00a8151b8008008021280080301912802800019128028030061280080000203406810066034068080100340080d0021fc0140181207807003812078070018031fc014038051b80140081107a05c0401107a05c008011b8014040051280140002912803c0302912803c00000128014030050340140d0050340240803e034025c5809034014080050400240101e6760140501e63c01401002040024050091fc0900d0243ca10c0180303410c0d0431fc090018031b810804008034068008010340f4040084e6108008011280ac0600c128250000001282500600c1280ac000000340680d0041280ac08004034fb80d0141280ac010020356e404809034068028050356e00480903406802805⟩,
  ⟨60,6,decodeBank 7 0x22a88a097cdd56d5b3,decodeHints 0x200c0380100000c140000000040300000800c0b00401a0341d0040080000600400e00c038030040080300000c0001d0040ca0100180700601c00815002020000060000180203a0080e81702e02a2600180700601c00919002024000060000180203a0080e80483506a02402805⟩,
  ⟨60,7,decodeBank 7 0x22a88a097cdd56ccc8,decodeHints 0x201c008f300600c7980700e004018010006700002200600c1119c05000001800000670000060020040319c00c000008000740581d04a00600c2501602c0e80180308a39c0683a0020341d0e707439c008010740301d0ae0000005700c0180e80000013001c038ee00600c7700700e260018031f03e0010980020087700600c26000000130018030ee0000004c03a07439c098131ce0e832898026194028030240700381203800c0180500e01404801022014e401100a0040080908a0240280005203c0302901e0000000500c014028e700a0241d03a01296404805074014048450120144c00500a8c0028091302a40a81602a798018033cc0580b01500600c210f80840540080102a39c040420020040a80c0186700000033803006015000000180300080541d0040843e0170151300b80a8e702a1084c09802a024048e700a015f780901205402805⟩,
  ⟨60,8,decodeBank 7 0x22a88a17825f3755b3,decodeHints 0x48090038070480900180304809003807048090018030480541084e048090018030480901082a048054018030841082100113c0541580113c0004f00013c0880180313c0884f02813c0000180013c0004f00013c0181580613c0184f00613c0001580013c0004f00013c0740a86913c0744f02713c0000a8003cc0100b0043cc0c8018030480c80b02d0480100180408a0102280407a04c0d01308a04d3881307a0100d0040600100a80406004df803a06004c0a8150600101800413c0100601b13c02c0001b13c02c0600c13c010000040480b00380704812401803048124038070480b0018030841082100213c0b0158020841080a8150840b02102c0841082102e13c1240300613c0b00000013c0b00300613c1240000007a0b0080810401140200408afac0802f0400b0020040480140181204807003812048070018030480140380508a0242280908a0151f80508a0151b00508a024228090600141800506005c0a83806005dd98170600140a80513c0140002913c03c0302913c03c0000013c0140300507a0140201f74c0240581f7180240200407a014058050400242280908a0141600508a0158f80504002416009⟩,
  ⟨60,7,decodeBank 8 0x8d62a89217825f3755b3,decodeHints 0x18030480c02c02402c01c0b0070100540a80801001c108070020040000600c000000070440000000c0180000000803a0000981002004c0b00702c01c0200401004c6280c0000300000200401c0c0c40300500a01802a0200a80800c0000300002004c080130120140280900a01c0e00500a0240480500a0200b8050520a40000500a0240480501201402809⟩,
  ⟨60,8,decodeBank 7 0x2358aa17825f3755b3,decodeHints 0x480801200313e01c158030480041200120005421015048054120150480042100104800410801048098038070480981082a0480040380113e0004f80013e0181580613e0184f80613e0001580013e0004f80013e0880380713e0884f82213e0000380013e0004f80013e0740080113e0744f82713e00000800082010208041780402181008204139010078010218041780100b0041780c8038070480c80b02d048010038040c80100400d07804c0080d7e204c040080c80100080413e0100601b13e02c0001b13e02c0600c13e010000040480901200213e060158020480900380704806010018048090120c42000600a815200124008010481240a8150480600080113e0600300613e2d80000013e2d80300613e060000000780600801004005002004082050080100400600200408202420809082015200050820151b805082024208090480141200504807003807048071e701c048014038050c80140081178805c0401176805c008010c80140400513e0140002913e03c0302913e03c0000013e014030050780140201f74e0240581f71a0240200407801405805040024208090820140c005082015900050400240c009⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cd53,decodeHints 0x8030e0004000030500000000104e0000b00305a00c0680d0100040d81b0180000700e02c0080100105c0080100000c0080100b0ec008018e900601400838002014000060000140f81f012014010050040240181600601c008080020200000c000030020040040280101800a02402809⟩
]

def nodesBlock53 : Array Node := #[
  ⟨60,6,decodeBank 7 0x23885e097cdd56d1b3,decodeHints 0x200c0400100000c060000000041380000801004001010004060000180000700e0900080100102a0080100000c008010480ce0080181600601c008080020200000c0000301682d02c29801048004120018e900601400838002014000060000140283506a0140100500412004805⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56d1b3,decodeHints 0x9550020980180304c11438001006004001450000880180304451414000006000001450000740080103a51413800002000025bb0080c801803064fc8530040060100200801a04c0080d026020040040020100200c03602c0001b016030060040000100115501c0600180e0300800c00200600801015004124008010920540a802002008010060042d80000016c01803002000008010100040500200402804008002008008120030061003416b08000c018242aa01c12001002114040082aa00400824010020158000005140600c28a0000002b0180300d0040096e80580b09e0100201a01602c120020041e80c00a0400080102403006002803006555ed8e92aa00c018052aa014028010020c40403806200400805010014028000005140300628a0000000500c014028040080d40583e06a01002005016014100020040140c00500a0080102003011c1002001201415805⟩,
  ⟨60,5,decodeBank 6 0x8aa097cdd56cccd,decodeHints 0xc1400001a1b40b00d01a1f40600d01c03803803032064030000a40343280d0221740181102222c000110220340201103c0780281100201c01801000018000010080340200d0020b80100201204400811⟩,
  ⟨60,6,decodeBank 7 0x22a85e09805f3755b3,decodeHints 0x803054004000030500000000104e0000180700601c00dbc0020c0000060000180200302c01002001010010020000180100580401c038038030680041700103206403000014050010020cc0100a00400601c018050020e0008050000180000500a024048050080240200503c07802809⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cdb2,decodeHints 0x8210020980180304c08415001006004001460000880180304451814000006000001460000740080103a51813800002000020160080c801803064058168040060100200801a04c0080d026020040040020100200c03602c0001b016030060040000100500701c0600180e03001c0380a00600c050150680b0008010580541700a0020040c006032028000190140180301800000005010014050020040280401780a008010028030064340380721a00c0180500e014028010020c40403806200400805010014028000005180300628c0000000500c014028040080d40583e06a010020050160141002003c0140501e00a1ac02820014028120030061040380708200c0182400e01c120010024340400808a00400824010020158000005180300628c0000002b00c0180d0040080d80580bb7a0100201a01602c1210d0481e80500a0401ac01024014008100200120ac02805⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cd91,decodeHints 0x8030e0004000030500000000104e0000200302c01002001010010020000180100700e02c0080100105c0080100000c0080100405e0080901200605808811002020148290000180f81f00803c0f01e00403c0b00300e00c040010100040300000c000058040200100500202800802805⟩,
  ⟨60,7,decodeBank 7 0x22a85e097ddf3755b3,decodeHints 0x8580020980180304c11438001006004001470000880180304451c14000006000001470000740080103a51c138000020002181602c160018030b00580384300600c12008010114008010b0020040240020041580600c51c0000028e0180302b000000080160676fc018030b00580b01000600ce880807404000801020020041d10020040800c0b651c0000028e0300601000000010020008040158040b0058070180060380c01602c160018030300541a0490020042481505c06000801030018030b60000005b00600c06000000030068010140860080a01a02806021818030040080140400500a01005e0601002f00a00c0901c02c0480e0030060140b00500a004088170100440b8010020140400500a0001480f00c0a4078000000140300501f6f80780506c0140284f00a03c1b00f00a0f0028090200f804b73012014080050120800480503001402af800a0240c009⟩,
  ⟨60,7,decodeBank 7 0x23885e097cdd56cc63,decodeHints 0x23600080800600c040d8010004018010006740000c00600c0619d018000018000006740001d0020040e99d04e000008001ca394020a6006010530080103b0008011d8020040a60020047600c0182980000014c030060ec0000001e0e801c1200180e0903a0240e800600c24015090124008010920540a8480020042400600c2d80000016c018030480000000c0e8030120530480903a03381814c19c02803024024ec81201200c018050780140280102205c0401102e004008050100140280005203c0302901e0000000500c0140283c00a024530090129680480514c014048e80120142400500a8c402809090024218e50860580180302c3a00384300600c0b01502a79c008013ce0540a8160020040b00600c6740000033a01803016000000218e505a0585302d02c3a00b04314c298120240040582400202c014028e8012025f900500a05804809⟩,
  ⟨60,8,decodeBank 7 0x22a85e097cdd56cc63,decodeHints 0x480041200104809801803048098228700480040180114000050000140088018031400885002814000001800140000500001400740080114007450027140000008001ca010728041ca0c8018030480c9f98a6048010018041b00100400d07804c0080d08a04c040081b0010008041400100601b14002c0001b14002c0600c140010000040480901200e04806010018048090018034e80600a8154e8124008010481240a81504806000801140060030061402d8000001402d803006140060000000400600801004005002004040050080100400600200404801401812048071ef01204807001803048014120051b00140081108a05c0401108a05c008011b0014040051400140002914003c0302914003c00000140014030050780140201f7500240581f71c0240200407801405805040024100090400140c005040015908050400240c009048090100071400ac018030480900a8154e8108008010481080a815048090008011400ac0300614028000000140280030061400ac0000004010c0801004008002004041708080101ca10c02004048090120021400ac0c00204170402805040080048090417000280504008004809⟩,
  ⟨60,8,decodeBank 7 0x22a89217825f3755b3,decodeHints 0x3c210c0b0160600c0018030600c00b01623010c0180323002010808060098018030600981082123002001803060068180011420201580114200050800142088018031420885082814200001800142000508001420301580c1420305080c1420001580014200050800142074040081420745081d142000040003c204c0b0163c2128018030601280b01623004c018030600c01800414204c158040600c00400806004c0d0130600c0180c514204c0600c1422b8000001422b80600c14204c000002300080380e08a0600180e7e2060038072300080180207a0081e8023940b02102c07a0b13882c07a008210023940080a8023940b0040080600b00a82e06000804002142008030191420280001914202803006142008000020340080800207a0500981307a0500802f03400809802230014018127be0700381279e070018032300140380507a0141e80507a0253200907a0252e00907a0141e8050600141800506005c0400806005dda817060014040051420140002914203c0302914203c00000142014030050340141e80507a0240980907a025c78090340140980508a0240101e6780140501e6440140100208a02405009⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cd69,decodeHints 0x803054004000030500000000104e0000200305a0100680d02a010020000180100700e00e00c0a80105c0040c81900c0000500405e0100180700601400838002014000060000140203e0080140f01e00a0240180700601c00815002020000060000180200b00804c0100201201404805⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56d5b3,decodeHints 0x8210025580180307808415001006004001480000880180304452014000006000001480000740080103a5201380000200002016008128018030940580b0040060100215601a04c0080d026068098040020100200c0082b80000015c030060040000100100701c0600180e03001c03802006008015c40040b000801058fbc4c002002008010060320280001901401803002000008010100040500200402804017802008008120030060f0038072ac00c0182400e01c180010021104197a088004008302ac02015800000520030062900000002b00c018180040080680980b0340100203002604c1000200570c0500a0d600801020014028048030060dc0380706e00c0180900e01c04801002559e09192ac004008092ac02404800000520030062900000000900c0180d004008024098090120100201a0260fc048020040d40504c06a008010090140240d01a00a02415805⟩,
  ⟨60,5,decodeBank 6 0x85e097cdd56cc67,decodeHints 0x41380001a0340400103606c0600001c1b00a80e01c1f80300e01c14c3380e024174008120242440001203e07c048120240380101200202000803000030000030060b4020040040380100e00a04801812⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cde9755b3,decodeHints 0x803054004000030500000000104e0001980305a00c0680d0100040d81b01800001dc5006090008080020200000c0000300800b0080100100300e0080100102a0080100000c008010660200080500200601c018050020e0008050000180000503e07c048050120140280900401401009⟩,
  ⟨60,7,decodeBank 7 0x22a85e097cdd56cdb1,decodeHints 0x8210020980180304c08415001006004001490000880180304452414000006000001490000740080103a52413800002000058160660c8018030640581680b00600c0580801a04c0080d0260200400b0020040980c03602c0001b016030060130000000100701c0600180e03001c03802006008010150040b00080105805417002002008010060320280001901401803002000008010100040500580b02804017802016008048030060dc0380706e00c0180900e01c048010024e0040082700040080901002404800000524030062920000000900c0180d01a03e0240581f01213c0481a01602c048020040d40504c06a00801009014024120030064e00380707800c0182400e01c180010020f40400807a0040083001002015800000524030062920000002b00c018181380600680580b03413c02030016010100020040d80500ab8c008010200140280d01a00a0ac04805⟩,
  ⟨60,6,decodeBank 7 0x22a85e097cdd56cd88,decodeHints 0x803054004000030500000000104e0000200305a0100680d02a010020000180100100300e0080100102a0080100000c008010040200080901200601c08811002054148290000180f81f00803c0f01e00403c0380300e00c0a8010100040300000c000058040200100500202800802805⟩
]

def nodesBlock54 : Array Node := #[
  ⟨60,7,decodeBank 7 0x22a85e097cddc755b3,decodeHints 0x8210025e401803078084150010060040014a00008801803044528140000060000014a0000740080103a5281380000200009816066128018030940581681300600cbc81501a04c0080d0260540a9790020040980c0b62b80000015c030060130000001200700e0f0018032f201c0382400600c2101502a190008010c8054040420020041580600c528000002940180302b00000021010008068098040340400804202604d1a00700e0500180302801c03a3400600c0a015069720008012f20540a8140020040a00600c52800000294018030140000000d010020050098130280400801a02604c0d01a0040501580200a00c0901c00e0480e0030060140380500a0040881702a0440b8010020140a80500a0001480f00c0a4078000000140300500a068028090260f804b750120140980501f71c0780506c0140286b00a03c1b00f0121140480502801402b1000a0240a009⟩,
  ⟨60,8,decodeBank 7 0x22a85e097cdd56ccc8,decodeHints 0x1e6004108010600c0018030600f01082a1e60040180114400051000144088018031440885102814400001800144000510001440740080114407451027144000008004ea04c0b0164ea128018030601280b0161e604c018030600c01800d06004c0d0130600c00080114404c0600c1442b8000001442b80600c14404c000001e60080380e0780600180e078060038071e6008018021f00087c0021f00b0008010600b1f8098060008008021440080301914402800019144028030061440080000203400808002034050098130340500802f034008098021e60140181207807003812078070018031e6014038050600140081106005de281106005c00801060014180051440140002914403c0302914403c00000144014030050340140d00503402409809034025c80090340140980508a0240101e67a0140501e6460140100208a024050091e60900b0164ea10c0180306010c0b0161e6090018030600c00d0081440ac008011440ac0600c144288000001442880600c1440ac000000600c0180041440ac098040341080a0140340680100203572c0a0141f01080100203572804809034068028050357240480903406802805⟩,
  ⟨60,8,decodeBank 7 0x2388aa17825f3755b3,decodeHints 0x8610c218031460581580306000418001060020180080600201800806000418001048004120010480980b08c048098180700480040b001146000518001460301580c1460305180c14600015800146000518001460880b0db146088518281460000b0001460005180014607400801146074518271460000080008610c218041460c81580408610c0b0160860c82183208610c2182d0600c80400806012800801060128040080600c8008011461280600c1460c8000001460c80600c146128000000780081e0020780601001807806139018078008100020480080b002048061f98480480600b016048008120023ce0080a8023ce0b0008010480b00a82e04800800802146008030191460280001914602803006146008000020340081e002078050190cd078051f6076034008190020780141e005078025328090780252e8090780141e005048014120050480700b06a048071e801c0480140b0050600140081106005c0401106005c00801060014040051460140002914603c0302914603c00000146014030050340141e00507802419009078025c8809034014190050820240101e67c0140501e6480140100208202405009⟩,
  ⟨60,8,decodeBank 7 0x23d8aa17825f3755b3,decodeHints 0x480c01200314808415803048090120011480981580104809010821048098180260480901202a148000520001480741581d1480745201d1480001580014800052000148088108211480885202214800010800148000520001480741301d1480745201d14800013000060010180042fc04c2181306004c18013060010218042fc010bf0042fc0c8108c90480c818032048010108040600101300406004c1e01306004c13013060010180041480100601b14802c0001b14802c0600c14801000004048008120022000b02102c0480b01202c0480082100204800810802048060228800480601082104800812002200008800022000b01302c0480b01202c048008130021480080301914802800019148028030061480080000207800808002082050020047da0500802f078008020021cc0147300516e05d3501716e05d348171cc014730050480141200504807010895048071e881c048014108050600141800506005c1301706005ddb817060014130051480140002914803c0302914803c00000148014030050780140201f06c0240581f72402402004078014058050820240101e06c0140501e64a0140100208202405009⟩,
  ⟨60,9,decodeBank 6 0x8aa17825f3755b3,decodeHints 0x480041080106009801803bc40981082a0480040180105600015800056088018030560881582805600001800056000158000560740080105607415827056000008000860100b0040860c801803bc20c80b02d048010018040600100400dbc004c0080dbbe04c04008060010008040560100601b05602c0001b05602c0600c056010000040480080380ebbc0600180ebba06003807048008018020840080a8020840b000801bb80b00a82e0600080080205600803019056028000190560280300605600800002bb600808002bb405002004bb20500802fbb00080200204801401812bae07003812bac070018030480140380506001400811baa05c04011ba805c00801060014040050560140002905603c0302905603c0000005601403005ba60140201fba40240581fba202402004ba001405805b9e0240101eb9c0140501eb9a01401002b9802405009⟩
]

def nodesGet (i : Nat) : Option Node :=
  if i < 432 then
    if i < 208 then
      if i < 96 then
        if i < 48 then
          if i < 16 then
            nodesBlock0[(i-0)]?
          else
            if i < 32 then
              nodesBlock1[(i-16)]?
            else
              nodesBlock2[(i-32)]?
        else
          if i < 64 then
            nodesBlock3[(i-48)]?
          else
            if i < 80 then
              nodesBlock4[(i-64)]?
            else
              nodesBlock5[(i-80)]?
      else
        if i < 144 then
          if i < 112 then
            nodesBlock6[(i-96)]?
          else
            if i < 128 then
              nodesBlock7[(i-112)]?
            else
              nodesBlock8[(i-128)]?
        else
          if i < 176 then
            if i < 160 then
              nodesBlock9[(i-144)]?
            else
              nodesBlock10[(i-160)]?
          else
            if i < 192 then
              nodesBlock11[(i-176)]?
            else
              nodesBlock12[(i-192)]?
    else
      if i < 320 then
        if i < 256 then
          if i < 224 then
            nodesBlock13[(i-208)]?
          else
            if i < 240 then
              nodesBlock14[(i-224)]?
            else
              nodesBlock15[(i-240)]?
        else
          if i < 288 then
            if i < 272 then
              nodesBlock16[(i-256)]?
            else
              nodesBlock17[(i-272)]?
          else
            if i < 304 then
              nodesBlock18[(i-288)]?
            else
              nodesBlock19[(i-304)]?
      else
        if i < 368 then
          if i < 336 then
            nodesBlock20[(i-320)]?
          else
            if i < 352 then
              nodesBlock21[(i-336)]?
            else
              nodesBlock22[(i-352)]?
        else
          if i < 400 then
            if i < 384 then
              nodesBlock23[(i-368)]?
            else
              nodesBlock24[(i-384)]?
          else
            if i < 416 then
              nodesBlock25[(i-400)]?
            else
              nodesBlock26[(i-416)]?
  else
    if i < 656 then
      if i < 544 then
        if i < 480 then
          if i < 448 then
            nodesBlock27[(i-432)]?
          else
            if i < 464 then
              nodesBlock28[(i-448)]?
            else
              nodesBlock29[(i-464)]?
        else
          if i < 512 then
            if i < 496 then
              nodesBlock30[(i-480)]?
            else
              nodesBlock31[(i-496)]?
          else
            if i < 528 then
              nodesBlock32[(i-512)]?
            else
              nodesBlock33[(i-528)]?
      else
        if i < 592 then
          if i < 560 then
            nodesBlock34[(i-544)]?
          else
            if i < 576 then
              nodesBlock35[(i-560)]?
            else
              nodesBlock36[(i-576)]?
        else
          if i < 624 then
            if i < 608 then
              nodesBlock37[(i-592)]?
            else
              nodesBlock38[(i-608)]?
          else
            if i < 640 then
              nodesBlock39[(i-624)]?
            else
              nodesBlock40[(i-640)]?
    else
      if i < 768 then
        if i < 704 then
          if i < 672 then
            nodesBlock41[(i-656)]?
          else
            if i < 688 then
              nodesBlock42[(i-672)]?
            else
              nodesBlock43[(i-688)]?
        else
          if i < 736 then
            if i < 720 then
              nodesBlock44[(i-704)]?
            else
              nodesBlock45[(i-720)]?
          else
            if i < 752 then
              nodesBlock46[(i-736)]?
            else
              nodesBlock47[(i-752)]?
      else
        if i < 816 then
          if i < 784 then
            nodesBlock48[(i-768)]?
          else
            if i < 800 then
              nodesBlock49[(i-784)]?
            else
              nodesBlock50[(i-800)]?
        else
          if i < 848 then
            if i < 832 then
              nodesBlock51[(i-816)]?
            else
              nodesBlock52[(i-832)]?
          else
            if i < 864 then
              nodesBlock53[(i-848)]?
            else
              nodesBlock54[(i-864)]?

def fastViews : Fast.Table View := ⟨61,viewsGet⟩

def fastNodes : Fast.Table Node := ⟨869,nodesGet⟩

end SignedProjection

namespace SignedProjection

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_0 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 0 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_16 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 16 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_32 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 32 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_48 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 48 13 = true := by decide +kernel

theorem joinRoots_0_0 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 0 32 = true :=
  @Fast.merge_blocks (Fast.checkRootAt fastViews fastNodes) 0 16 16 blockRoots_0 blockRoots_16

theorem joinRoots_0_32 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 32 29 = true :=
  @Fast.merge_blocks (Fast.checkRootAt fastViews fastNodes) 32 16 13 blockRoots_32 blockRoots_48

theorem joinRoots_1_0 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 0 61 = true :=
  @Fast.merge_blocks (Fast.checkRootAt fastViews fastNodes) 0 32 29 joinRoots_0_0 joinRoots_0_32

theorem certifiedRoots : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 0 61 = true := joinRoots_1_0

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_12 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 12 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_24 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 24 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_36 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 36 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_48 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 48 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_60 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 60 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_72 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 72 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_84 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 84 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_96 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 96 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_108 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 108 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_120 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 120 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_132 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 132 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_144 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 144 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_156 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 156 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_168 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 168 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_180 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 180 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_192 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 192 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_204 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 204 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_216 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 216 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_228 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 228 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_240 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 240 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_252 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 252 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_264 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 264 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_276 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 276 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_288 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 288 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_300 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 300 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_312 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 312 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_324 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 324 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_336 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 336 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_348 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 348 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_360 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 360 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_372 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 372 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_384 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 384 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_396 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 396 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_408 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 408 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_420 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 420 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_432 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 432 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_444 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 444 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_456 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 456 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_468 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 468 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_480 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 480 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_492 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 492 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_504 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 504 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_516 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 516 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_528 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 528 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_540 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 540 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_552 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 552 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_564 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 564 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_576 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 576 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_588 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 588 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_600 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 600 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_612 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 612 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_624 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 624 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_636 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 636 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_648 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 648 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_660 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 660 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_672 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 672 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_684 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 684 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_696 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 696 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_708 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 708 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_720 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 720 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_732 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 732 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_744 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 744 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_756 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 756 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_768 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 768 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_780 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 780 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_792 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 792 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_804 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 804 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_816 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 816 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_828 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 828 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_840 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 840 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_852 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 852 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_864 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 864 5 = true := by decide +kernel

theorem joinNodes_0_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 0 12 12 blockNodes_0 blockNodes_12

theorem joinNodes_0_24 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 24 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 24 12 12 blockNodes_24 blockNodes_36

theorem joinNodes_0_48 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 48 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 48 12 12 blockNodes_48 blockNodes_60

theorem joinNodes_0_72 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 72 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 72 12 12 blockNodes_72 blockNodes_84

theorem joinNodes_0_96 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 96 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 96 12 12 blockNodes_96 blockNodes_108

theorem joinNodes_0_120 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 120 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 120 12 12 blockNodes_120 blockNodes_132

theorem joinNodes_0_144 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 144 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 144 12 12 blockNodes_144 blockNodes_156

theorem joinNodes_0_168 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 168 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 168 12 12 blockNodes_168 blockNodes_180

theorem joinNodes_0_192 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 192 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 192 12 12 blockNodes_192 blockNodes_204

theorem joinNodes_0_216 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 216 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 216 12 12 blockNodes_216 blockNodes_228

theorem joinNodes_0_240 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 240 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 240 12 12 blockNodes_240 blockNodes_252

theorem joinNodes_0_264 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 264 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 264 12 12 blockNodes_264 blockNodes_276

theorem joinNodes_0_288 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 288 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 288 12 12 blockNodes_288 blockNodes_300

theorem joinNodes_0_312 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 312 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 312 12 12 blockNodes_312 blockNodes_324

theorem joinNodes_0_336 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 336 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 336 12 12 blockNodes_336 blockNodes_348

theorem joinNodes_0_360 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 360 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 360 12 12 blockNodes_360 blockNodes_372

theorem joinNodes_0_384 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 384 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 384 12 12 blockNodes_384 blockNodes_396

theorem joinNodes_0_408 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 408 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 408 12 12 blockNodes_408 blockNodes_420

theorem joinNodes_0_432 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 432 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 432 12 12 blockNodes_432 blockNodes_444

theorem joinNodes_0_456 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 456 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 456 12 12 blockNodes_456 blockNodes_468

theorem joinNodes_0_480 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 480 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 480 12 12 blockNodes_480 blockNodes_492

theorem joinNodes_0_504 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 504 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 504 12 12 blockNodes_504 blockNodes_516

theorem joinNodes_0_528 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 528 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 528 12 12 blockNodes_528 blockNodes_540

theorem joinNodes_0_552 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 552 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 552 12 12 blockNodes_552 blockNodes_564

theorem joinNodes_0_576 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 576 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 576 12 12 blockNodes_576 blockNodes_588

theorem joinNodes_0_600 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 600 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 600 12 12 blockNodes_600 blockNodes_612

theorem joinNodes_0_624 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 624 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 624 12 12 blockNodes_624 blockNodes_636

theorem joinNodes_0_648 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 648 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 648 12 12 blockNodes_648 blockNodes_660

theorem joinNodes_0_672 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 672 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 672 12 12 blockNodes_672 blockNodes_684

theorem joinNodes_0_696 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 696 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 696 12 12 blockNodes_696 blockNodes_708

theorem joinNodes_0_720 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 720 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 720 12 12 blockNodes_720 blockNodes_732

theorem joinNodes_0_744 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 744 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 744 12 12 blockNodes_744 blockNodes_756

theorem joinNodes_0_768 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 768 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 768 12 12 blockNodes_768 blockNodes_780

theorem joinNodes_0_792 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 792 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 792 12 12 blockNodes_792 blockNodes_804

theorem joinNodes_0_816 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 816 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 816 12 12 blockNodes_816 blockNodes_828

theorem joinNodes_0_840 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 840 24 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 840 12 12 blockNodes_840 blockNodes_852

theorem joinNodes_1_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 48 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 0 24 24 joinNodes_0_0 joinNodes_0_24

theorem joinNodes_1_48 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 48 48 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 48 24 24 joinNodes_0_48 joinNodes_0_72

theorem joinNodes_1_96 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 96 48 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 96 24 24 joinNodes_0_96 joinNodes_0_120

theorem joinNodes_1_144 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 144 48 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 144 24 24 joinNodes_0_144 joinNodes_0_168

theorem joinNodes_1_192 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 192 48 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 192 24 24 joinNodes_0_192 joinNodes_0_216

theorem joinNodes_1_240 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 240 48 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 240 24 24 joinNodes_0_240 joinNodes_0_264

theorem joinNodes_1_288 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 288 48 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 288 24 24 joinNodes_0_288 joinNodes_0_312

theorem joinNodes_1_336 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 336 48 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 336 24 24 joinNodes_0_336 joinNodes_0_360

theorem joinNodes_1_384 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 384 48 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 384 24 24 joinNodes_0_384 joinNodes_0_408

theorem joinNodes_1_432 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 432 48 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 432 24 24 joinNodes_0_432 joinNodes_0_456

theorem joinNodes_1_480 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 480 48 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 480 24 24 joinNodes_0_480 joinNodes_0_504

theorem joinNodes_1_528 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 528 48 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 528 24 24 joinNodes_0_528 joinNodes_0_552

theorem joinNodes_1_576 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 576 48 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 576 24 24 joinNodes_0_576 joinNodes_0_600

theorem joinNodes_1_624 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 624 48 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 624 24 24 joinNodes_0_624 joinNodes_0_648

theorem joinNodes_1_672 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 672 48 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 672 24 24 joinNodes_0_672 joinNodes_0_696

theorem joinNodes_1_720 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 720 48 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 720 24 24 joinNodes_0_720 joinNodes_0_744

theorem joinNodes_1_768 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 768 48 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 768 24 24 joinNodes_0_768 joinNodes_0_792

theorem joinNodes_1_816 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 816 48 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 816 24 24 joinNodes_0_816 joinNodes_0_840

theorem joinNodes_2_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 96 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 0 48 48 joinNodes_1_0 joinNodes_1_48

theorem joinNodes_2_96 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 96 96 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 96 48 48 joinNodes_1_96 joinNodes_1_144

theorem joinNodes_2_192 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 192 96 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 192 48 48 joinNodes_1_192 joinNodes_1_240

theorem joinNodes_2_288 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 288 96 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 288 48 48 joinNodes_1_288 joinNodes_1_336

theorem joinNodes_2_384 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 384 96 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 384 48 48 joinNodes_1_384 joinNodes_1_432

theorem joinNodes_2_480 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 480 96 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 480 48 48 joinNodes_1_480 joinNodes_1_528

theorem joinNodes_2_576 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 576 96 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 576 48 48 joinNodes_1_576 joinNodes_1_624

theorem joinNodes_2_672 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 672 96 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 672 48 48 joinNodes_1_672 joinNodes_1_720

theorem joinNodes_2_768 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 768 96 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 768 48 48 joinNodes_1_768 joinNodes_1_816

theorem joinNodes_3_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 192 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 0 96 96 joinNodes_2_0 joinNodes_2_96

theorem joinNodes_3_192 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 192 192 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 192 96 96 joinNodes_2_192 joinNodes_2_288

theorem joinNodes_3_384 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 384 192 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 384 96 96 joinNodes_2_384 joinNodes_2_480

theorem joinNodes_3_576 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 576 192 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 576 96 96 joinNodes_2_576 joinNodes_2_672

theorem joinNodes_3_768 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 768 101 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 768 96 5 joinNodes_2_768 blockNodes_864

theorem joinNodes_4_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 384 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 0 192 192 joinNodes_3_0 joinNodes_3_192

theorem joinNodes_4_384 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 384 384 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 384 192 192 joinNodes_3_384 joinNodes_3_576

theorem joinNodes_5_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 768 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 0 384 384 joinNodes_4_0 joinNodes_4_384

theorem joinNodes_6_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 869 = true :=
  @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 0 768 101 joinNodes_5_0 joinNodes_3_768

theorem certifiedNodes : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 869 = true := joinNodes_6_0

end SignedProjection

namespace Bridge
abbrev W := BitVec 64
abbrev basicOps (a b : W) := SignedProjection.signedOps a b
open CoreSigned
def wordGate (k : Fin 4) (a b : W) : W :=
  match k.val with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a &&& ~~~b
  | _ => b &&& ~~~a

theorem wordGate_mem (k : Fin 4) (a b : W) : wordGate k a b ∈ basicOps a b := by
  fin_cases k <;> simp [wordGate, basicOps, SignedProjection.signedOps]

theorem zero_left_word (k : Fin 4) (x : W) : wordGate k 0 x = 0 ∨ wordGate k 0 x = x := by
  fin_cases k <;> first | exact .inl BitVec.zero_and | exact .inr BitVec.zero_or | exact .inr BitVec.and_allOnes

theorem zero_right_word (k : Fin 4) (x : W) : wordGate k x 0 = 0 ∨ wordGate k x 0 = x := by
  fin_cases k <;> first | exact .inl BitVec.and_zero | exact .inr BitVec.or_zero | exact .inr BitVec.and_allOnes | exact .inl BitVec.zero_and

theorem simulate {s : Nat} {S : W → Prop} {av : Finset W} {f : W}
    (sources : ∀ x, S x → x = 0 ∨ x ∈ av)
    (h : UC wordGate (fun _ => True) s S f) : f = 0 ∨ build basicOps f s av := by
  induction s generalizing S av with
  | zero => exact sources f h
  | succ s ih =>
    rcases h with skip | ⟨k,a,b,_,ha,hb,tail⟩
    · exact (ih sources skip).imp_right Or.inl
    by_cases old : wordGate k a b = 0 ∨ wordGate k a b ∈ av
    · apply Or.imp_right Or.inl
      apply ih _ tail
      rintro x (rfl | hx)
      · exact old
      · exact sources x hx
    · have alive : a ∈ av ∧ b ∈ av ∧ a ≠ b := by
        rcases sources a ha with rfl | ma
        · exfalso
          apply old
          rcases zero_left_word k b with e | e
          · exact .inl e
          · rw [e]; exact sources b hb
        rcases sources b hb with rfl | mb
        · exfalso
          apply old
          rcases zero_right_word k a with e | e
          · exact .inl e
          · rw [e]; exact .inr ma
        refine ⟨ma,mb,?_⟩
        rintro rfl
        apply old
        fin_cases k <;> simp_all [wordGate]
      have next : ∀ x, (x = wordGate k a b ∨ S x) → x = 0 ∨ x ∈ insert (wordGate k a b) av := by
        rintro x (rfl | hx)
        · exact .inr (Finset.mem_insert_self ..)
        · exact (sources x hx).imp_right (Finset.mem_insert_of_mem ·)
      exact (ih next tail).imp_right (fun cont => .inr ⟨a,alive.1,b,alive.2.1,alive.2.2,
        wordGate k a b,wordGate_mem k a b,cont⟩)

def sampleRows : List (Fin 8 → Bool) := ([0, 128, 32, 160, 64, 192, 96, 224, 1, 129, 33, 161, 65, 193, 97, 225, 2, 130, 34, 162, 66, 194, 98, 226, 3, 131, 35, 163, 67, 195, 99, 227, 4, 132, 36, 164, 68, 196, 100, 228, 5, 133, 37, 165, 69, 197, 101, 229, 6, 134, 38, 166, 70, 198, 102, 230, 7, 135, 39, 167, 71, 199, 103, 231] : List Nat).map assignment
def encode (f : BF) : W := BitVec.ofNat 64 (enc f sampleRows)

theorem encode_op (k : Fin 4) (a b : BF) : encode (gF k a b) = wordGate k (encode a) (encode b) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have get (v : Nat) : (BitVec.ofNat 64 v)[i] = v.testBit i := by
    rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat]
    simp [hi]
  simp only [encode, enc_gF,get,gN_testBit]
  fin_cases k <;> simp [wordGate,zeroGate,get,Bool.and_comm]

def cols : List W := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def fanGoal : W := 0xfefefeeefefafea8

def rejectType := ¬ CoreSigned.build SignedProjection.signedOps fanGoal 9 cols.toFinset

set_option maxHeartbeats 0 in
theorem fan (rejected : rejectType) (h : UC gF (fun _ => True) 9
    (sourceVars (((Finset.univ : Finset (Fin 8)).erase 3).erase 4))
    (rst 4 (rst 3 graph))) : False := by
  have src : ∀ i ∈ (((Finset.univ : Finset (Fin 8)).erase 3).erase 4),
      encode (var i) ∈ cols := by decide +kernel
  have eq : encode (rst 4 (rst 3 graph)) = fanGoal := by decide +kernel
  have u := UC_map (G:=gF) (G':=wordGate) (A:=fun _ => True) encode encode_op 9 _
    (fun x => x ∈ cols.toFinset) _ (by
      rintro _ ⟨i,hi,rfl⟩
      exact List.mem_toFinset.mpr (src i hi)) h
  rw [eq] at u
  rcases simulate (av:=cols.toFinset) (fun _ h => Or.inr h) u with fail | run
  · exact (by decide : fanGoal ≠ 0) fail
  · exact rejected run

end Bridge
theorem lower_with_not (reject : Bridge.rejectType) (gates : List Gate) (o : ℕ) (legal : GOK gates)
    (hnot : ∃ g ∈ gates, g.op = GateOp.not)
    (comp : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = graph x) :
    13 ≤ gates.length := by
  have hg : (wiresF gates (List.ofFn var)).getD o zF = graph := by
    funext x
    rw [← comp x, ← getD_map_x, ← wires_eq]
    simp only [Circuit.eval, Circuit.wires, List.map_ofFn]
    rfl
  have start := trans_binary gates (List.ofFn var) (sourceVars Finset.univ) legal (by
    intro w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hw
    exact Or.inr ⟨i, Finset.mem_univ i, ori_zp rfl⟩) o
  rw [hg, ori_zp (by decide : graph (fun _ => false) = false)] at start
  rcases start with e | base
  · have c := congrFun e (assignment 33)
    exact False.elim ((by decide : graph (assignment 33) ≠ false) c)
  obtain ⟨t1, pay1, h1⟩ := remove_var graph 3 (Finset.univ : Finset (Fin 8)) (countBinary gates)
    ⟨assignment 72, by decide⟩ (by
      intro h
      exact (by decide : (rst 3 graph) (assignment 33) ≠ false) (congrFun h (assignment 33))) base
  obtain ⟨t2, pay2, h2⟩ := remove_var (rst 3 graph) 4 ((Finset.univ : Finset (Fin 8)).erase 3) t1
    ⟨assignment 18, by decide⟩ (by
      intro h
      exact (by decide : (rst 4 (rst 3 graph)) (assignment 33) ≠ false) (congrFun h (assignment 33))) h1
  have extra := countBinary_lt gates hnot
  by_contra! tooSmall
  exact Bridge.fan reject (UC_le (by omega) h2)

def witness : List Gate := [⟨.or, [7, 0]⟩, ⟨.or, [7, 6]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [8, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [10, 5]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [15, 0]⟩, ⟨.and, [16, 12]⟩, ⟨.or, [17, 1]⟩, ⟨.and, [18, 13]⟩, ⟨.or, [19, 14]⟩]

theorem witnessBasis : ∀ g ∈ witness,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨witness, 20⟩ (List.ofFn x) = graph x := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem graph_correct : ∀ x : Fin 8 → Bool, graph x = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

def rootMatches (item : Option SignedProjection.View) : Bool :=
  match item with
  | none => false
  | some v => SignedProjection.vg v == Bridge.fanGoal && SignedProjection.vk v == 9 &&
      (SignedProjection.vs v).toFinset == Bridge.cols.toFinset

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem rejected : Bridge.rejectType := by
  let views := SignedProjection.fastViews
  let nodes := SignedProjection.fastNodes
  have shape : rootMatches (SignedProjection.Fast.get views 60) = true := by decide +kernel
  cases ev : SignedProjection.Fast.get views 60 with
  | none => simp [rootMatches,ev] at shape
  | some v =>
    have valid := SignedProjection.Fast.certified_view views nodes
      SignedProjection.certifiedRoots SignedProjection.certifiedNodes ev
    simp only [rootMatches,ev,Bool.and_eq_true,beq_iff_eq] at shape
    rcases shape with ⟨⟨goal,budget⟩,stock⟩
    unfold SignedProjection.ViewOK at valid
    rw [goal,budget,stock] at valid
    exact valid

end PEqualNP.Outside.L_meta_15056

open PEqualNP.Outside.L_meta_15056 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_15056 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o legal _oneNot computes
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · have comp : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = graph x :=
      fun x => (computes x).trans (graph_correct x).symm
    have large := lower_with_not rejected gates o legal hnot comp
    have hw : witness.length = 13 := rfl
    exact ⟨witness, 20, witnessBasis, by omega, fun x => (witnessCorrect x).trans (graph_correct x)⟩
  · refine ⟨gates, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨ops, hlen⟩ := legal g hg
    refine ⟨?_, hlen⟩
    rcases ops with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hnot ⟨g, hg, h⟩)
