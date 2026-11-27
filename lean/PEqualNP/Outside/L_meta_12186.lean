import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12186

-- Gate normalization and the four-vertex bound are adapted from L-meta-5459.
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

abbrev BF := (Fin 7 → Bool) → Bool

def gF (k : Fin 4) (a b : BF) : BF := fun x => zeroGate k (a x) (b x)

def var (i : Fin 7) : BF := fun x => x i

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

theorem enc_gF (k : Fin 4) (a b : BF) (l : List (Fin 7 → Bool)) :
    enc (gF k a b) l = gN k (enc a l) (enc b l) := enc_gate k a b l

theorem enc_lt {ρ : Type} (w : ρ → Bool) (l : List ρ) : enc w l < 2 ^ l.length := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [enc_testBit, List.getD_eq_default _ _ (by simp; omega)]

def zF : BF := fun _ => false

def rst (p : Fin 7) (a : BF) : BF := fun x => a (Function.update x p false)

def ThrL (V : Fin 7 → Prop) (F : BF) : Prop :=
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

theorem upd_single {i p : Fin 7} (h : i ≠ p) :
    Function.update (singleInput i) p false = singleInput i := by
  funext m
  by_cases hm : m = p
  · subst hm; simp [singleInput, Ne.symm h]
  · simp [Function.update_of_ne hm]

theorem upd_pair {i j p : Fin 7} (hi : i ≠ p) (hj : j ≠ p) :
    Function.update (pairInput i j) p false = pairInput i j := by
  funext m
  by_cases hm : m = p
  · subst hm; simp [pairInput, Ne.symm hi, Ne.symm hj]
  · simp [Function.update_of_ne hm]

theorem rst_var_self (p : Fin 7) : rst p (var p) = zF :=
  funext fun x => by simp [rst, var, zF]

theorem rst_var_ne {i p : Fin 7} (h : i ≠ p) : rst p (var i) = var i :=
  funext fun x => by simp [rst, var, Function.update_of_ne h]

theorem var_inj {i j : Fin 7} (h : var i = var j) : i = j := by
  have := congrFun h (singleInput i)
  exact (by simpa [var, singleInput] using this : j = i).symm

theorem TRF_det {C : Fin 4 → BF → BF → Prop} {ys : List BF} {s : ℕ} {ws : List BF}
    (h : TR gF C ys s ws) (x x' : Fin 7 → Bool) :
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

def dcount (p : Fin 7) (ws : List BF) : ℕ := ws.countP fun w => decide (rst p w = zF)

theorem dcount_cons (p : Fin 7) (a : BF) (l : List BF) :
    dcount p (a :: l) = dcount p l + if rst p a = zF then 1 else 0 := by
  simp [dcount, List.countP_cons]

theorem dcount_rep (p : Fin 7) (n : ℕ) (g : BF) (r : List BF) :
    dcount p (List.replicate n g ++ r) = (if rst p g = zF then n else 0) + dcount p r := by
  simp only [dcount, List.countP_append, List.countP_replicate]
  split_ifs <;> simp_all

theorem pot_dead {A : Fin 4 → Prop} (p : Fin 7) {F : BF} (hF : rst p F ≠ zF) {s : ℕ}
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

def otop (x : Fin 7) : BF := fun p => decide (∃ i, i ≠ x ∧ p i = true)

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

theorem getD_map_x (W : List BF) (i : ℕ) (x : Fin 7 → Bool) :
    (W.map fun w => w x).getD i false = (W.getD i zF) x := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> rfl

theorem wires_eq (x : Fin 7 → Bool) : ∀ (gs : List Gate) (W : List BF),
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

def graphTable (a : ℕ) (x : Fin 7 → Bool) : Bool := a.testBit (tableIndex x)

def assignment (a : ℕ) (i : Fin 7) : Bool := a.testBit i.val

theorem inputVector (x : Fin 7 → Bool) : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
  funext i
  fin_cases i <;> rfl

theorem equalSeven {f g : (Fin 7 → Bool) → Bool}
    (h : ∀ a b c d e v w : Bool, f ![a, b, c, d, e, v, w] = g ![a, b, c, d, e, v, w]) : f = g := by
  funext x
  rw [inputVector x]
  exact h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

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



theorem phaseGate : ∀ (k : Fin 4) (α β : Bool), ∃ k' : Fin 4, ∀ a b : Bool,
    Bool.xor (zeroGate k a b) (zeroGate k α β) =
      zeroGate k' (Bool.xor a α) (Bool.xor b β) := by
  decide

end PEqualNP.Outside.L_meta_12186
-- The signed live-wire checker is adapted from L-meta-2960 under Apache-2.0.
-- Two input restrictions leave the threshold function on five inputs.
namespace PEqualNP.Outside.L_meta_12186.KFive

/- Each sampled signal carries its phase. The four binary operations represent AND and OR on signed inputs, and inverting a signal changes only its phase. -/
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A wire is a phase and a column of sampled truth values. Complementing a wire is free.
abbrev Wire := Bool × ℕ
def zero : Wire := (false,0)
def flip (a : Wire) : Wire := (!a.1,a.2)
def combine (d a b : ℕ) : ℕ :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def opIndex (a b : Bool) : ℕ :=
  if a then (if b then 1 else 3) else (if b then 2 else 0)
def meet (a b : Wire) : Wire := (a.1 && b.1,combine (opIndex a.1 b.1) a.2 b.2)
def join (a b : Wire) : Wire := flip (meet (flip a) (flip b))
def read (j : ℕ) (a : Wire) : Bool := a.1 != a.2.testBit j
lemma read_zero (j : ℕ) : read j zero=false := by simp [read,zero]
lemma read_flip (j : ℕ) (a : Wire) : read j (flip a)=!(read j a) := by
  cases a with | mk s a => cases s <;> cases h : a.testBit j <;> simp [read,flip,h]
lemma read_meet (j : ℕ) (a b : Wire) : read j (meet a b) = (read j a && read j b) := by
  obtain ⟨s,a⟩ := a;obtain ⟨t,b⟩ := b
  cases s <;> cases t <;> cases h : a.testBit j <;> cases g : b.testBit j <;>
    simp [read,meet,combine,opIndex,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,h,g]
lemma read_join (j : ℕ) (a b : Wire) : read j (join a b) = (read j a || read j b) := by
  simp only [join,read_flip,read_meet];cases read j a <;> cases read j b <;> rfl

def gate (w : List Wire) (g : Gate) : Wire :=
  let arg := fun i => w.getD i zero
  match g.op,g.inputs with
  | .not, xs => flip (arg (xs.headD w.length))
  | .and, [] => flip zero
  | .or, [] => zero
  | .and, [i] | .or, [i] => arg i
  | .and, i::j::_ => meet (arg i) (arg j)
  | .or, i::j::_ => join (arg i) (arg j)
  | _,_ => zero
def execute (gs : List Gate) (w : List Wire) : List Wire :=
  gs.foldl (fun w g => w++[gate w g]) w
def boolRun (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) w
lemma read_get (j : ℕ) (w : List Wire) (i : ℕ) :
    (w.map (read j)).getD i false = read j (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h : w[i]? with
  | none => exact (read_zero j).symm
  | some a => rfl
lemma gate_read (w : List Wire) (g : Gate) (legal : g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) (j : ℕ) :
    read j (gate w g) = g.op.eval (g.inputs.map fun i => (w.map (read j)).getD i false) := by
  simp_rw [read_get]
  obtain ⟨op,xs⟩ := g
  obtain ⟨ops,len⟩ := legal
  change op ∈ ({.and,.or,.not} : Set GateOp) at ops
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
  rcases ops with rfl|rfl|rfl <;>
    rcases xs with _|⟨i,_|⟨k,_|⟨h,rest⟩⟩⟩ <;>
    simp_all [gate,GateOp.eval,read_flip,read_meet,read_join,read_get,read_zero,List.getD_eq_default]
lemma execute_read (j : ℕ) (gs : List Gate) (w : List Wire) (legal : ∀ g ∈ gs,
    g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (execute gs w).map (read j) = boolRun gs (w.map (read j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gate w g])).map (read j) = boolRun gs (_++[_])
    rw [ih _ (fun v hv => legal v (.tail _ hv))]
    simp [gate_read w g (legal g List.mem_cons_self) j]

def counted (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List Wire) := w.map Prod.snd
def simple (w : List Wire) (z : ℕ) := z=0 ∨ z∈reps w
def priced (w : List Wire) (paid : Bool) (z : ℕ) := simple w z ∨
    (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a≠0 ∧ b≠0 ∧ a≠b ∧ z=combine d a b)
lemma get_simple (w : List Wire) (i : ℕ) : simple w (w.getD i zero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a,List.mem_of_getElem? eq,rfl⟩)
lemma combine_eq_cases (d a b : ℕ) (hd : d<4) (h : a=0 ∨ b=0 ∨ a=b) :
    combine d a b=0 ∨ combine d a b=a ∨ combine d a b=b := by
  rcases h with h|h|h <;> subst_vars <;> interval_cases d <;> simp [combine]
lemma made (w : List Wire) (d : ℕ) (a b : Wire) (hd : d<4) (pa : simple w a.2) (pb : simple w b.2) :
    priced w true (combine d a.2 b.2) := by
  by_cases h : a.2=0 ∨ b.2=0 ∨ a.2=b.2
  · rcases combine_eq_cases _ _ _ hd h with e|e|e
    · exact Or.inl (Or.inl e)
    · apply Or.inl; rw [e]; exact pa
    · apply Or.inl; rw [e]; exact pb
  · push Not at h
    exact Or.inr ⟨rfl,d,hd,a.2,pa.resolve_left h.1,b.2,pb.resolve_left h.2.1,h.1,h.2.1,h.2.2,rfl⟩
lemma op_lt (s t : Bool) : opIndex s t < 4 := by cases s <;> cases t <;> decide
lemma gate_priced (w : List Wire) (g : Gate) : priced w (counted g) (gate w g).2 := by
  obtain ⟨op,xs⟩ := g
  cases op with
  | and =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | mod _ | maj => exact Or.inl (Or.inl rfl)
  | _ => exact Or.inl (get_simple w _)

end PEqualNP.Outside.L_meta_12186.KFive

namespace PEqualNP.Outside.L_meta_12186.KFive

/- Trace the output backwards and keep the signals that still feed a gate. Each step uses one binary gate. Every surviving set separates every sampled pair, and its cardinality is at most one more than the remaining gate count. -/
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def Good (m a : ℕ) := ∀ i<m, a.testBit i ≠ a.testBit (m+i)

inductive Live (m : ℕ) : ℕ → Finset ℕ → Prop
  | done {a} (hg : Good m a) (nonzero : a≠0) : Live m 0 {a}
  | step {k U a b d} (hd : d<4) (ha : a≠0) (hb : b≠0) (diff : a≠b)
      (fresh : combine d a b ∉ insert a (insert b U))
      (next : Live m k (insert (combine d a b) U)) :
      Live m (k+1) (insert a (insert b U))

lemma liveNonzero {m k S} (h : Live m k S) : ∀ a∈S,a≠0 := by
  induction h with
  | done hg hn => simpa using hn
  | @step k U a b d hd ha hb ne fresh tail ih =>
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hb
    exact ih x (Finset.mem_insert_of_mem hx)
lemma liveSize {m k S} (h : Live m k S) : S.card≤k+1 := by
  induction h with
  | done hg hn => simp
  | @step k U a b d hd ha hb ne fresh tail ih =>
    have z : combine d a b ∉ U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    rw [Finset.card_insert_of_notMem z] at ih
    have u := Finset.card_insert_le a (insert b U)
    have v := Finset.card_insert_le b U
    omega
lemma combine_congr_bits (d a b i j : ℕ) (p : a.testBit i=a.testBit j) (q : b.testBit i=b.testBit j) :
    (combine d a b).testBit i=(combine d a b).testBit j := by
  rcases d with _|(_|(_|d)) <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,p,q]
lemma liveSeparates {m k S} (h : Live m k S) (i : ℕ) (hi : i<m) :
    ∃ a∈S,a.testBit i≠a.testBit (m+i) := by
  induction h with
  | done hg hn => exact ⟨_,Finset.mem_singleton_self _,hg i hi⟩
  | @step k U a b d hd ha hb ne fresh tail ih =>
    obtain ⟨x,hx,dist⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl|hx
    · by_cases v : a.testBit i=a.testBit (m+i)
      · exact ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),fun u => dist (combine_congr_bits _ _ _ _ _ v u)⟩
      · exact ⟨a,Finset.mem_insert_self _ _,v⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx),dist⟩

lemma pull {m k S w z p} (h : Live m k S) (op : priced w p z)
    (sub : ∀ a∈S, a∈reps w ++ [z]) :
    ∃ l T, l ≤ k + p.toNat ∧ Live m l T ∧ ∀ a∈T, a∈reps w := by
  by_cases needed : z∈S
  · by_cases available : z∈reps w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a∈reps w ∨ a=z) with old|rfl
      · exact old
      · exact available
    · rcases op with easy|⟨rfl,d,hd,a,xa,b,xb,na,nb,ab,rfl⟩
      · rcases easy with e|e
        · exact ((liveNonzero h z needed) e).elim
        · exact (available e).elim
      · let g := combine d a b
        let U := S.erase g
        have tail : Live m k (insert g U) := by change Live m k (insert g (S.erase g)); rw [Finset.insert_erase (show g∈S from needed)]; exact h
        have old (x : ℕ) (hx : x∈U) : x∈reps w := by
          obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hx
          have h' : x∈reps w ∨ x=g := by simpa using sub x mem
          exact h'.resolve_right ne
        have fresh : g ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e|h'
          · exact available (show g∈reps w by rw [e];exact xa)
          rcases Finset.mem_insert.mp h' with e|u
          · exact available (show g∈reps w by rw [e];exact xb)
          · exact available (old _ u)
        refine ⟨k+1,insert a (insert b U),by simp,Live.step hd na nb ab fresh tail,?_⟩
        simpa using And.intro xa (And.intro xb old)
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have ne : a≠z := fun e => needed (e ▸ ha)
    simpa [ne] using sub a ha

lemma extract {m out} (hg : Good m out) (hn : out≠0) (gs : List Gate) (w : List Wire)
    (found : out∈reps (execute gs w)) :
    ∃ k S, k≤gs.countP counted ∧ Live m k S ∧ ∀ a∈S, a∈reps w := by
  induction gs generalizing w with
  | nil => exact ⟨0,{out},by simp,Live.done hg hn,by simpa [execute] using found⟩
  | cons g gs ih =>
    obtain ⟨k,S,lim,h,sub⟩ := ih (w++[gate w g]) found
    have sub' : ∀ a∈S,a∈reps w ++ [(gate w g).2] := by simpa [reps] using sub
    obtain ⟨l,T,cost,ht,raw⟩ := pull h (gate_priced w g) sub'
    refine ⟨l,T,?_,ht,raw⟩
    cases e : counted g <;> simp [e,Bool.toNat] at cost ⊢ <;> omega

def separation (m a : ℕ) := a ^^^ (a >>> m)
def cover (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | a::t => separation m a ||| cover m t
def full (m : ℕ) := (1 <<< m)-1
def enough (m c : ℕ) := (c &&& full m) == full m
lemma coverBit (m i : ℕ) (v : List ℕ) : (cover m v).testBit i=true ↔
    ∃ a∈v,a.testBit i≠a.testBit (m+i) := by
  induction v with
  | nil => simp [cover]
  | cons a t ih =>
    simp only [cover,Nat.testBit_or,Bool.or_eq_true,ih,List.mem_cons,separation,Nat.testBit_xor,Nat.testBit_shiftRight]
    cases v1 : a.testBit i <;> cases v2 : a.testBit (m+i) <;> simp [v1,v2] <;> aesop
lemma enoughLive {m k S} (h : Live m k S) (v : List ℕ) (rep : v.toFinset=S) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have bit : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases hi : i<m
  · have ⟨x,hx,good⟩ := liveSeparates h i hi
    have xc : x∈v := List.mem_toFinset.mp (rep ▸ hx)
    have mark := (coverBit m i v).2 ⟨x,xc,good⟩
    simp [mark,bit,hi]
  · simp [bit,hi]
end PEqualNP.Outside.L_meta_12186.KFive

namespace PEqualNP.Outside.L_meta_12186.KFive

/- The search enumerates distinct operands, the four signed operations and the four choices of which operands are needed again. -/

def save (keep : Bool) (a : ℕ) (rest : List ℕ) := if keep then a::rest else rest
def without (v : List ℕ) (a b : ℕ) := v.filter (fun x => x != a && x != b)
def optionStep (m fuel : ℕ) (go : List ℕ → Bool) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) : Bool :=
  let len := 1+n+ka.toNat+kb.toNat
  len ≤ fuel+1 && enough m (((separation m z ||| cv) ||| (if ka then separation m a else 0)) |||
    (if kb then separation m b else 0)) && go (z::save ka a (save kb b rest))
def gateStep (m fuel : ℕ) (go : List ℕ → Bool) (v rest : List ℕ) (n cv a b z : ℕ) : Bool :=
  z != 0 && !(v.contains z) &&
  (optionStep m fuel go rest n cv a b z false false || optionStep m fuel go rest n cv a b z true false ||
   optionStep m fuel go rest n cv a b z false true || optionStep m fuel go rest n cv a b z true true)
def pairStep (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) (a b : ℕ) : Bool :=
  if a<b then
    let rest := without v a b
    let check := gateStep m fuel go v rest rest.length (cover m rest) a b
    check (a &&& b) || check (a ||| b) || check (a ^^^ (a &&& b)) || check (b ^^^ (a &&& b))
  else false
def anyGate (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) : Bool :=
  v.any (fun a => v.any (fun b => pairStep m fuel go v a b))
def terminal (m : ℕ) (v : List ℕ) := v.any (fun a => enough m (separation m a))
def search (m : ℕ) : ℕ → List ℕ → Bool
  | 0, v => terminal m v
  | fuel+1, v => terminal m v || anyGate m fuel (search m fuel) v

lemma surface (m a i : ℕ) : (separation m a).testBit i=true ↔ a.testBit i≠a.testBit (m+i) := by
  simp only [separation,Nat.testBit_xor,Nat.testBit_shiftRight]
  cases a.testBit i <;> cases a.testBit (m+i) <;> decide
lemma ends {m a} (h : Good m a) (v : List ℕ) (mem : a∈v) : terminal m v=true := by
  apply List.any_eq_true.mpr;refine ⟨a,mem,?_⟩
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i;rw [Nat.testBit_and]
  have e : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases l : i<m
  · simp [e,l,(surface _ _ _).2 (h i l)]
  · simp [e,l]
lemma option_ok {m fuel go rest a b z ka kb} (lim : (z::save ka a (save kb b rest)).length≤fuel+1)
    (cov : enough m (cover m (z::save ka a (save kb b rest)))=true)
    (next : go (z::save ka a (save kb b rest))=true) :
    optionStep m fuel go rest rest.length (cover m rest) a b z ka kb=true := by
  have size : 1+rest.length+ka.toNat+kb.toNat≤fuel+1 := by
    cases ka <;> cases kb <;> simp [save,Bool.toNat] at lim ⊢ <;> omega
  have eq : enough m (((separation m z ||| cover m rest) ||| (if ka then separation m a else 0)) ||| (if kb then separation m b else 0))=true := by
    cases ka <;> cases kb <;> simpa [save,cover,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using cov
  simp [optionStep,size,eq,next]
lemma gate_ok {m fuel go v rest n cv a b z ka kb} (nz : z≠0) (fresh : z∉v)
    (which : optionStep m fuel go rest n cv a b z ka kb=true) :
    gateStep m fuel go v rest n cv a b z=true := by
  cases ka <;> cases kb <;> simp [gateStep,nz,fresh,which]
lemma pair_ok {m fuel go v a b d} (ordered : a<b) (hd : d<4)
    (step : let rest := without v a b;gateStep m fuel go v rest rest.length (cover m rest) a b (combine d a b)=true) :
    pairStep m fuel go v a b=true := by
  interval_cases d <;> simp only [combine] at step <;> simp [pairStep,ordered,step]
lemma swapOp (d a b : ℕ) (hd : d<4) : ∃ e<4,combine d a b=combine e b a := by
  interval_cases d
  · exact ⟨0,by decide,Nat.and_comm a b⟩
  · exact ⟨1,by decide,Nat.or_comm a b⟩
  · exact ⟨3,by decide,by simp [combine,Nat.and_comm]⟩
  · exact ⟨2,by decide,by simp [combine,Nat.and_comm]⟩
lemma listNext {v : List ℕ} {a b z : ℕ} {U : Finset ℕ} (rep : v.toFinset=insert a (insert b U))
    (ab : a≠b) (fz : z∉insert a (insert b U)) (nd : v.Nodup) :
    let rest := without v a b
    let next := z::save (decide (a∈U)) a (save (decide (b∈U)) b rest)
    next.toFinset=insert z U ∧ next.Nodup := by
  dsimp only
  have mem (x : ℕ) : x∈without v a b ↔ x∈U ∧ x≠a ∧ x≠b := by
    simp only [without,List.mem_filter,Bool.and_eq_true,bne_iff_ne]
    have e : x∈v ↔ x=a ∨ x=b ∨ x∈U := by rw [← List.mem_toFinset,rep];simp
    tauto
  have nr := nd.filter (fun x => x != a && x != b)
  change (without v a b).Nodup at nr
  have md (x : ℕ) : (x∈save (decide (a∈U)) a (save (decide (b∈U)) b (without v a b))) ↔ x∈U := by
    by_cases xa : x=a
    · subst x; by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,ab]
    by_cases xb : x=b
    · subst x; by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,Ne.symm ab]
    by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,xa,xb]
  constructor
  · ext x;simp [md]
  · simp only [List.nodup_cons,md]
    refine ⟨fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m)),?_⟩
    have an : a∉without v a b := fun x => (mem _).1 x |>.2.1 rfl
    have bn : b∉without v a b := fun x => (mem _).1 x |>.2.2 rfl
    by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,nr,ab,an,bn]
lemma orderedStep {m fuel n U a b d v} {go : List ℕ→Bool} (hd : d<4)
    (lt : a<b) (nz : combine d a b≠0) (fresh : combine d a b∉insert a (insert b U))
    (rep : List.toFinset v=insert a (insert b U)) (nd : v.Nodup) (lim : n≤fuel)
    (tail : Live m n (insert (combine d a b) U))
    (nextOK : ∀ v : List ℕ, v.toFinset=insert (combine d a b) U → v.Nodup → go v=true) :
    pairStep m fuel go v a b=true := by
  let z := combine d a b
  let rest := without v a b
  let next := z::save (decide (a∈U)) a (save (decide (b∈U)) b rest)
  obtain ⟨r,nu⟩ := listNext (z:=z) rep (Nat.ne_of_lt lt) fresh nd
  have small := liveSize tail
  change (insert z U).card≤n+1 at small
  have length : next.length=(insert z U).card := by rw [←r,List.toFinset_card_of_nodup nu]
  have bound : next.length≤fuel+1 := by omega
  have coverOK := enoughLive tail next r
  have ok := option_ok bound coverOK (nextOK next r nu)
  apply pair_ok lt hd
  exact gate_ok nz (fun h => fresh (rep ▸ List.mem_toFinset.mpr h)) ok
lemma transition {m fuel n U a b d v} {go : List ℕ→Bool} (hd : d<4)
    (ab : a≠b) (fresh : combine d a b∉insert a (insert b U))
    (rep : List.toFinset v=insert a (insert b U)) (nd : v.Nodup) (lim : n≤fuel)
    (tail : Live m n (insert (combine d a b) U))
    (nextOK : ∀ v : List ℕ, v.toFinset=insert (combine d a b) U → v.Nodup → go v=true) :
    anyGate m fuel go v=true := by
  have ma : a∈v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_self _ _)
  have mb : b∈v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have nz := liveNonzero tail _ (Finset.mem_insert_self _ _)
  rcases lt_or_gt_of_ne ab with lt|gt
  · exact List.any_eq_true.mpr ⟨a,ma,List.any_eq_true.mpr ⟨b,mb,orderedStep hd lt nz fresh rep nd lim tail nextOK⟩⟩
  · obtain ⟨e,he,eq⟩ := swapOp d a b hd
    have rev : insert a (insert b U)=insert b (insert a U) := Finset.insert_comm a b U
    rw [rev] at fresh rep
    rw [eq] at fresh nz tail nextOK
    exact List.any_eq_true.mpr ⟨b,mb,List.any_eq_true.mpr ⟨a,ma,orderedStep he gt nz fresh rep nd lim tail nextOK⟩⟩

theorem complete (m fuel : ℕ) {n S} (h : Live m n S) (lim : n≤fuel)
    (v : List ℕ) (rep : v.toFinset=S) (nd : v.Nodup) : search m fuel v=true := by
  induction fuel generalizing n S v with
  | zero =>
    cases h with
    | done hg hn => exact ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self _))
    | step hd _ _ _ _ _ => omega
  | succ k ih =>
    rw [search,Bool.or_eq_true]
    cases h with
    | done hg hn => exact Or.inl (ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self _)))
    | step hd _ _ ab fresh tail =>
      exact Or.inr (transition hd ab fresh rep nd (by omega) tail (fun v hv nv => ih tail (by omega) v hv nv))
end PEqualNP.Outside.L_meta_12186.KFive

namespace PEqualNP.Outside.L_meta_12186.KFive

/- A restriction can force several live signals to zero. Projecting the rest of a trace saves at least one binary gate for each such signal. -/

structure Projection (m h : ℕ) where
  toFun : ℕ → ℕ
  atZero : toFun 0=0
  combineEq : ∀ d a b, d<4 → toFun (combine d a b)=combine d (toFun a) (toFun b)
  good : ∀ a, Good m a → Good h (toFun a)
  someRow : 0<h

def Possible (m k : ℕ) (av : List ℕ) :=
  ∃ j S, j≤k ∧ Live m j S ∧ ∀ x∈S,x∈av
def charge (av : List ℕ) (z : ℕ) := z != 0 && !(av.contains z)
lemma pullPaid {m k d a b : ℕ} {av : List ℕ} (hd : d<4) (ha : a∈av) (hb : b∈av)
    (later : Possible m k (av++[combine d a b])) :
    Possible m (k+(charge av (combine d a b)).toNat) av := by
  let w := av.map (fun x => (false,x))
  have repr : reps w=av := by simp [w,reps,List.map_map,Function.comp_def]
  obtain ⟨j,S,lim,live,sub⟩ := later
  have needed : ∀ x∈S,x∈reps w++[combine d a b] := by simpa [repr] using sub
  have price : priced w (charge av (combine d a b)) (combine d a b) := by
    by_cases nz : combine d a b=0
    · exact Or.inl (Or.inl nz)
    by_cases old : combine d a b∈av
    · exact Or.inl (Or.inr (repr ▸ old))
    have paid : charge av (combine d a b)=true := by simp [charge,nz,old]
    have special : ¬(a=0 ∨ b=0 ∨ a=b) := by
      intro h
      rcases combine_eq_cases _ _ _ hd h with zero|rfl'|rfl'
      · exact nz zero
      · exact old (by rw [rfl'];exact ha)
      · exact old (by rw [rfl'];exact hb)
    exact Or.inr ⟨paid,d,hd,a,repr ▸ ha,b,repr ▸ hb,
      fun x => special (Or.inl x),fun x => special (Or.inr (Or.inl x)),fun x => special (Or.inr (Or.inr x)),rfl⟩
  obtain ⟨l,T,le,ok,sub'⟩ := pull live price needed
  exact ⟨l,T,by omega,ok,by simpa [repr] using sub'⟩

def dead (p : ℕ→ℕ) (S : Finset ℕ) := (S.filter (fun x => p x=0)).card
lemma deadStay {p : ℕ→ℕ} {a : ℕ} {S : Finset ℕ} (h : p a≠0) : dead p (insert a S)=dead p S := by
  simp [dead,Finset.filter_insert,h]
lemma deadLimit (p : ℕ→ℕ) (a : ℕ) (S : Finset ℕ) : dead p (insert a S)≤dead p S+1 := by
  by_cases x : p a=0
  · simpa [dead,Finset.filter_insert,x] using Finset.card_insert_le a (S.filter (fun x => p x=0))
  · simp [deadStay x]
lemma deadMono (p : ℕ→ℕ) (a : ℕ) (S : Finset ℕ) : dead p S ≤ dead p (insert a S) := by
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
lemma deadGrow {p : ℕ→ℕ} {a : ℕ} {S : Finset ℕ} (z : p a=0) (fresh : a∉S) :
    dead p (insert a S)=dead p S+1 := by
  have nf : a∉S.filter (fun x => p x=0) := fun h => fresh (Finset.mem_filter.mp h).1
  simp [dead,Finset.filter_insert,z,Finset.card_insert_of_notMem nf]
lemma countCharge {m h d a b : ℕ} (p : Projection m h) (hd : d<4) (U : Finset ℕ)
    (fz : combine d a b∉insert a (insert b U)) (av : List ℕ) (ma : p.toFun a∈av) (mb : p.toFun b∈av) :
    (charge av (p.toFun (combine d a b))).toNat + dead p.toFun (insert a (insert b U)) ≤
      1+dead p.toFun (insert (combine d a b) U) := by
  have up := deadMono p.toFun (combine d a b) U
  have la := deadLimit p.toFun a (insert b U)
  have lb := deadLimit p.toFun b U
  have free (bad : p.toFun a=0 ∨ p.toFun b=0) : charge av (p.toFun (combine d a b))=false := by
    rw [p.combineEq _ _ _ hd]
    rcases combine_eq_cases _ _ _ hd (bad.imp_right Or.inl) with e|e|e <;> simp [charge,e,ma,mb]
  by_cases az : p.toFun a=0
  · rw [free (Or.inl az)];simp only [Bool.toNat_false,Nat.zero_add]
    by_cases bz : p.toFun b=0
    · have zz : p.toFun (combine d a b)=0 := by
        rw [p.combineEq _ _ _ hd,az,bz];interval_cases d <;> decide
      have fresh : combine d a b∉U := fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
      rw [deadGrow zz fresh];omega
    · rw [deadStay bz] at la;omega
  · rw [deadStay az]
    by_cases bz : p.toFun b=0
    · rw [free (Or.inr bz)];simp only [Bool.toNat_false,Nat.zero_add];omega
    · rw [deadStay bz];cases charge av (p.toFun (combine d a b)) <;> simp [Bool.toNat] <;> omega

theorem projectLive {m h k S} (p : Projection m h) (live : Live m k S) :
    ∃ j T,j+dead p.toFun S≤k ∧ Live h j T ∧ ∀ x∈T,x∈S.image p.toFun := by
  induction live with
  | @done a hg hn =>
    have gp := p.good a hg
    have nz : p.toFun a≠0 := by intro e;have x := gp 0 p.someRow;simp [e] at x
    exact ⟨0,{p.toFun a},by simp [dead,nz],Live.done gp nz,by simp⟩
  | @step k U a b d hd ha hb ab fz tail ih =>
    obtain ⟨j,T,cost,ok,raw⟩ := ih
    let av := ((insert a (insert b U)).image p.toFun).toList
    have ma : p.toFun a∈av := by simp [av]
    have mb : p.toFun b∈av := by simp [av]
    have later : Possible h j (av++[combine d (p.toFun a) (p.toFun b)]) := by
      refine ⟨j,T,le_rfl,ok,?_⟩
      intro z hz
      have has := raw _ hz
      simp only [Finset.image_insert,Finset.mem_insert] at has
      rcases has with rfl|old
      · simp [p.combineEq d a b hd]
      · have inav : z∈av := by simpa [av] using (Or.inr (Or.inr old) : z=p.toFun a ∨ z=p.toFun b ∨ z∈U.image p.toFun)
        simp [inav]
    obtain ⟨l,V,lim,good,sub⟩ := pullPaid hd ma mb later
    rw [←p.combineEq d a b hd] at lim
    have bound := countCharge p hd U fz av ma mb
    exact ⟨l,V,by omega,good,by simpa [av] using sub⟩
end PEqualNP.Outside.L_meta_12186.KFive

namespace PEqualNP.Outside.L_meta_12186.KFive

/- A restricted bank keeps selected pairs of rows. Duplicate one retained pair in the other positions to preserve the two-column representation. -/
lemma full_bit (m i : ℕ) : (full m).testBit i=decide (i<m) := by
  simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]

def half (m q r a : ℕ) := (a &&& q &&& full m) |||
    (if a.testBit r then ((full m ^^^ q) &&& full m) else 0)
def slice (m q r a : ℕ) := half m q r a ||| ((half m q r (a >>> m)) <<< m)
lemma half_bit (m q r a i : ℕ) : (half m q r a).testBit i =
    (decide (i<m) && (if q.testBit i then a.testBit i else a.testBit r)) := by
  cases e : a.testBit r <;> cases f : q.testBit i <;> by_cases l : i<m <;>
    simp [half,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,full_bit,e,f,l]
lemma slice_lo {m i : ℕ} (q r a : ℕ) (hi : i<m) : (slice m q r a).testBit i =
    a.testBit (if q.testBit i then i else r) := by
  cases e : q.testBit i <;> simp [slice,Nat.testBit_or,Nat.testBit_shiftLeft,half_bit,hi,e,(show ¬ (m ≤ i) from by omega)]
lemma slice_hi {m i : ℕ} (q r a : ℕ) (hi : i<m) : (slice m q r a).testBit (m+i) =
    a.testBit (m+(if q.testBit i then i else r)) := by
  have n : ¬ (m + i < m) := by omega
  cases e : q.testBit i <;> simp [slice,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_shiftRight,half_bit,hi,e,n]
lemma slice_above {m i : ℕ} (q r a : ℕ) (hi : 2 * m ≤ i) : (slice m q r a).testBit i=false := by
  simp [slice,Nat.testBit_or,Nat.testBit_shiftLeft,half_bit,(show ¬ (i < m) from by omega),(show ¬ (i - m < m) from by omega)]
lemma slice_hom (m q r d a b : ℕ) (hd : d<4) : slice m q r (combine d a b)=combine d (slice m q r a) (slice m q r b) := by
  apply Nat.eq_of_testBit_eq;intro i
  by_cases lo : i<m
  · rw [slice_lo _ _ _ lo]
    interval_cases d <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,slice_lo _ _ _ lo]
  by_cases upper : i<2*m
  · let j := i-m
    have h : j<m := by dsimp [j];omega
    have e : i=m+j := by dsimp [j];omega
    rw [e,slice_hi _ _ _ h]
    interval_cases d <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,slice_hi _ _ _ h]
  · have large := slice_above (m:=m) (i:=i) (hi := (show 2 * m ≤ i from by omega))
    interval_cases d <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,large]
def projection (m q r : ℕ) (hr : r<m) : Projection m m where
  toFun := slice m q r
  atZero := by simp [slice,half]
  combineEq := slice_hom m q r
  good := by
    intro a ga i hi
    rw [slice_lo _ _ _ hi,slice_hi _ _ _ hi]
    cases q.testBit i
    · exact ga r hr
    · exact ga i hi
  someRow := by omega

lemma enoughSup {m k S} (h : Live m k S) (v : List ℕ) (sub : ∀ x∈S,x∈v) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i
  rw [Nat.testBit_and,full_bit]
  by_cases hi : i<m
  · obtain ⟨x,hx,g⟩ := liveSeparates h i hi
    have bit := (coverBit m i v).2 ⟨x,sub _ hx,g⟩
    simp [bit,hi]
  · simp [hi]
def start (m fuel : ℕ) (av : List ℕ) :=
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  extra.sublists.any (fun t =>
    let s := (must++t).dedup
    s.length≤fuel+1 && enough m (cover m s) && search m fuel s)

theorem start_complete {m k S} (h : Live m k S) (av : List ℕ) (sub : ∀ x∈S,x∈av)
    (fuel : ℕ) (lim : k≤fuel) : start m fuel av=true := by
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  let t := extra.filter (fun x => decide (x∈S))
  let s := (must++t).dedup
  have inV (x : ℕ) (hx : x∈S) : x∈v := by simp [v,sub x hx,liveNonzero h x hx]
  have fixed (a : ℕ) (ha : a∈must) : a∈S := by
    by_contra absent
    have no := (List.mem_filter.mp ha).2
    have all (x : ℕ) (hx : x∈S) : x∈v.filter (fun y => y != a) := by
      have ne : x≠a := by rintro rfl;exact absent hx
      simp [inV x hx,ne]
    have yes := enoughSup h _ all
    simpa [needed,yes] using no
  have eq : s.toFinset=S := by
    ext x
    constructor
    · intro mem
      have e : x∈must ∨ x∈t := by simpa [s] using mem
      rcases e with l|r
      · exact fixed x l
      · simpa using (List.mem_filter.mp r).2
    · intro mem
      have raw := inV x mem
      cases H : needed x <;> simp [s,must,t,extra,H,raw,mem]
  have nd : s.Nodup := List.nodup_dedup _
  have size : s.length≤fuel+1 := by
    have vsize := liveSize h
    rw [←eq,List.toFinset_card_of_nodup nd] at vsize;omega
  have test := complete m fuel h lim s eq nd
  have cov := enoughLive h s eq
  apply List.any_eq_true.mpr
  refine ⟨t,List.mem_sublists.mpr (List.filter_sublist),?_⟩
  change (decide (s.length≤fuel+1) && enough m (cover m s) && search m fuel s)=true
  simp [size,cov,test]

def cutSearch (m q fuel : ℕ) (v : List ℕ) : Bool :=
  let r := min (Nat.log2 q) (m-1)
  let xs := v.map (slice m q r)
  let gone := xs.count 0
  gone≤fuel && start m (fuel-gone) xs

theorem cut_complete {m k S} (hm : 0<m) (h : Live m k S) (v : List ℕ) (rep : v.toFinset=S) (nd : v.Nodup)
    (q fuel : ℕ) (lim : k≤fuel) : cutSearch m q fuel v=true := by
  let r := min (Nat.log2 q) (m-1)
  let p := projection m q r (show r<m by dsimp [r];omega)
  obtain ⟨l,T,cost,live,sub⟩ := projectLive p h
  let xs := v.map (slice m q r)
  have fixed : dead p.toFun S=xs.count 0 := by
    rw [←rep];dsimp [dead]
    have E : v.toFinset.filter (fun x => p.toFun x=0) = (v.filter (fun x => decide (p.toFun x=0))).toFinset := by ext x;simp
    rw [E,List.toFinset_card_of_nodup (nd.filter _)]
    simp only [xs,List.count_eq_countP,List.countP_map,p,projection,Function.comp_apply]
    rw [List.countP_eq_length_filter]
    congr 2
  rw [fixed] at cost
  have has (x : ℕ) (hx : x∈T) : x∈xs := by simpa [xs,p,projection,←rep] using sub x hx
  have test := start_complete live xs has (fuel-xs.count 0) (by omega)
  change (decide (xs.count 0≤fuel) && start m (fuel-xs.count 0) xs)=true
  simp [test,show xs.count 0≤fuel by omega]
end PEqualNP.Outside.L_meta_12186.KFive

namespace PEqualNP.Outside.L_meta_12186.KFive

/- The certificate selects a restriction or enumerates a complete level of successors. Its hints can select any bank. Soundness follows from the projected trace and complete successor enumeration. -/
def oneOutput (m fuel : ℕ) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) : List (List ℕ) :=
  if optionStep m fuel (fun _ => true) rest n cv a b z ka kb then [z::save ka a (save kb b rest)] else []
def oneGate (m fuel : ℕ) (v rest : List ℕ) (n cv a b z : ℕ) :=
  if z != 0 && !(v.contains z) then
    oneOutput m fuel rest n cv a b z false false ++ oneOutput m fuel rest n cv a b z true false ++
    oneOutput m fuel rest n cv a b z false true ++ oneOutput m fuel rest n cv a b z true true
  else []
def onePair (m fuel : ℕ) (v : List ℕ) (a b : ℕ) :=
  if a<b then
    let rest := without v a b
    let gate := oneGate m fuel v rest rest.length (cover m rest) a b
    gate (a &&& b) ++ gate (a ||| b) ++ gate (a ^^^ (a &&& b)) ++ gate (b ^^^ (a &&& b))
  else []
def successors (m fuel : ℕ) (v : List ℕ) :=
  v.flatMap (fun a => v.flatMap (fun b => onePair m fuel v a b))
lemma output_any (m fuel : ℕ) (go : List ℕ→Bool) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) :
    (oneOutput m fuel rest n cv a b z ka kb).any go=optionStep m fuel go rest n cv a b z ka kb := by
  have E (t : Bool) (x : List ℕ) : ((if t then [x] else []) : List (List ℕ)).any go = (t && go x) := by cases t <;> simp
  unfold oneOutput
  rw [E]
  simp only [optionStep,Bool.and_true]
lemma gate_any (m fuel : ℕ) (go : List ℕ→Bool) (v rest : List ℕ) (n cv a b z : ℕ) :
    (oneGate m fuel v rest n cv a b z).any go=gateStep m fuel go v rest n cv a b z := by
  have E (t : Bool) (xs : List (List ℕ)) : (if t then xs else []).any go = (t && xs.any go) := by cases t <;> simp
  unfold oneGate gateStep
  rw [E]
  simp only [List.any_append,output_any,Bool.or_assoc,Bool.and_assoc]
lemma pair_any (m fuel : ℕ) (go : List ℕ→Bool) (v : List ℕ) (a b : ℕ) :
    (onePair m fuel v a b).any go=pairStep m fuel go v a b := by
  by_cases h : a<b <;> simp [onePair,pairStep,h,gate_any,Bool.or_assoc]
lemma successors_any (m fuel : ℕ) (go : List ℕ→Bool) (v : List ℕ) :
    (successors m fuel v).any go=anyGate m fuel go v := by simp [successors,anyGate,pair_any]
def feasible (m fuel : ℕ) (v : List ℕ) := ∃ k≤fuel,Live m k v.toFinset ∧ v.Nodup
theorem move {m fuel : ℕ} {v : List ℕ} (h : feasible m (fuel+1) v) :
    terminal m v=true ∨ ∃ w∈successors m fuel v,feasible m fuel w := by
  classical
  obtain ⟨k,lim,live,nd⟩ := h
  generalize e : v.toFinset=S at live
  cases live with
  | done hg hn => exact Or.inl (ends hg v (List.mem_toFinset.mp (e ▸ Finset.mem_singleton_self _)))
  | step hd ha hb ab fz tail =>
    let step := fun w => decide (feasible m fuel w)
    have hit := transition (go:=step) hd ab fz e nd (by omega : _≤fuel) tail (fun w rep nu => by
      apply decide_eq_true;exact ⟨_,by omega,rep ▸ tail,nu⟩)
    rw [←successors_any] at hit
    obtain ⟨w,hw,works⟩ := List.any_eq_true.mp hit
    exact Or.inr ⟨w,hw,of_decide_eq_true works⟩

def zeroPairs (m : ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, acc => acc
  | x::xs, code, acc => zeroPairs m xs (code >>> 1)
      (if code % 2=1 then acc ^^^ (acc &&& (x ||| (x >>> m))) else acc)

end PEqualNP.Outside.L_meta_12186.KFive

namespace PEqualNP.Outside.L_meta_12186.KFive

/- Permutations of sampled row pairs preserve every gate operation and the condition that the output separates all pairs. -/
def flipSwap (i j a : ℕ) := if a.testBit i = a.testBit j then a else a ^^^ ((1 <<< i) ||| (1 <<< j))
lemma swapBit (i j k a : ℕ) : (flipSwap i j a).testBit k =
    a.testBit (if k=i then j else if k=j then i else k) := by
  by_cases h : a.testBit i=a.testBit j
  · by_cases x : k=i <;> by_cases y : k=j <;> simp [flipSwap,h,x,y] <;> grind
  · have n : i≠j := fun e => h (e ▸ rfl)
    by_cases x : k=i
    · subst k
      cases p : a.testBit i <;> cases q : a.testBit j <;>
        simp_all [flipSwap,Nat.testBit_xor,Nat.testBit_or,Nat.shiftLeft_eq,Nat.testBit_two_pow]
    by_cases y : k=j
    · subst k
      cases p : a.testBit i <;> cases q : a.testBit j <;>
        simp_all [flipSwap,Nat.testBit_xor,Nat.testBit_or,Nat.shiftLeft_eq,Nat.testBit_two_pow]
    · simp [flipSwap,h,x,y,Nat.testBit_xor,Nat.testBit_or,Nat.shiftLeft_eq,Nat.testBit_two_pow,Ne.symm x,Ne.symm y]
lemma flipSwap_twice (i j a : ℕ) : flipSwap i j (flipSwap i j a)=a := by
  apply Nat.eq_of_testBit_eq;intro k
  by_cases x : k=i <;> by_cases y : k=j <;> by_cases n : i=j <;> simp_all [swapBit]
lemma flipSwap_hom (i j d a b : ℕ) (hd : d<4) : flipSwap i j (combine d a b)=combine d (flipSwap i j a) (flipSwap i j b) := by
  apply Nat.eq_of_testBit_eq;intro k
  interval_cases d <;> simp [swapBit,combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor]

def turn (m i j a : ℕ) := flipSwap i j (flipSwap (m+i) (m+j) a)
lemma turnGood {m i j a : ℕ} (hi : i<m) (hj : j<m) (g : Good m a) : Good m (turn m i j a) := by
  intro k hk
  have hm : m≠0 := by omega
  have ki : k≠m+i := by omega
  have kj : k≠m+j := by omega
  have ii : i≠m+i := by omega
  have ij : i≠m+j := by omega
  have ji : j≠m+i := by omega
  have jj : j≠m+j := by omega
  have ui : m+k≠i := by omega
  have uj : m+k≠j := by omega
  by_cases x : k=i
  · subst k;simp [turn,swapBit,ii,ij,ji,jj,ui,uj,hm];exact g _ hj
  by_cases y : k=j
  · subst k;simp [turn,swapBit,x,ii,ij,ji,jj,ui,uj,hm];exact g _ hi
  · simpa [turn,swapBit,x,y,ki,kj,ui,uj] using g k hk

theorem relabelLive {m k S} (f : ℕ→ℕ) (fz : f 0=0) (inj : Function.Injective f)
    (op : ∀ d a b,d<4 → f (combine d a b)=combine d (f a) (f b))
    (labels : ∀ a,Good m a → Good m (f a)) (live : Live m k S) : Live m k (S.image f) := by
  induction live with
  | done hg hn =>
    simp only [Finset.image_singleton]
    exact Live.done (labels _ hg) (fun h => hn (inj (h.trans fz.symm)))
  | @step k U a b d hd ha hb ne fresh tail ih =>
    rw [Finset.image_insert,Finset.image_insert]
    rw [Finset.image_insert,op d a b hd] at ih
    apply Live.step hd (fun h => ha (inj (h.trans fz.symm))) (fun h => hb (inj (h.trans fz.symm))) (fun h => ne (inj h)) _ ih
    rw [←op d a b hd,←Finset.image_insert,←Finset.image_insert]
    exact fun h => fresh ((Finset.mem_image.mp h).elim (fun x hh => inj hh.2 ▸ hh.1))
def permute (m : ℕ) : List (ℕ×ℕ) → ℕ → ℕ
  | [],a => a
  | (i,j)::ss,a => permute m ss (turn m i j a)
theorem perm_live {m k S} (ss : List (ℕ×ℕ)) (safe : ∀ p∈ss,p.1<m ∧ p.2<m) (h : Live m k S) :
    Live m k (S.image (permute m ss)) := by
  induction ss generalizing S with
  | nil => simpa [permute] using h
  | cons p ss ih =>
    obtain ⟨i,j⟩ := p
    obtain ⟨hi,hj⟩ := safe _ (List.mem_cons_self)
    have fi (a b : ℕ) : Function.Injective (flipSwap a b) := fun x y e =>
      (flipSwap_twice a b x).symm.trans ((congrArg (flipSwap a b) e).trans (flipSwap_twice a b y))
    have inj : Function.Injective (turn m i j) := (fi i j).comp (fi (m+i) (m+j))
    have names := relabelLive (turn m i j) (by simp [turn,flipSwap]) inj
      (fun d a b hd => by simp [turn,flipSwap_hom _ _ _ _ _ hd]) (fun _ => turnGood hi hj) h
    simpa [permute,Finset.image_image,Function.comp_def] using ih (fun p hp => safe _ (List.mem_cons_of_mem _ hp)) names
theorem perm_feasible {m fuel : ℕ} {v w : List ℕ} (ss : List (ℕ×ℕ)) (safe : ∀ p∈ss,p.1<m ∧ p.2<m)
    (eq : (v.map (permute m ss)).toFinset=w.toFinset) (nw : w.Nodup) (h : feasible m fuel v) : feasible m fuel w := by
  obtain ⟨k,lim,ok,_⟩ := h
  refine ⟨k,lim,?_,nw⟩
  have tr := perm_live ss safe ok
  have imageEq : (v.map (permute m ss)).toFinset = v.toFinset.image (permute m ss) := by ext x;simp
  rw [←eq,imageEq]
  exact tr
end PEqualNP.Outside.L_meta_12186.KFive

namespace PEqualNP.Outside.L_meta_12186.KFive
def Excluded (m k : ℕ) (v : List ℕ) := ¬feasible m k v
def Block (m k : ℕ) (vs : List (List ℕ)) (i n : ℕ) := ∀ v∈(vs.drop i).take n,Excluded m k v
lemma blocks_cover {m k width q : ℕ} {vs : List (List ℕ)} (pw : 0<width) (size : vs.length≤q*width)
    (all : ∀ j : Fin q,Block m k vs (j.val*width) width) : ∀ v∈vs,Excluded m k v := by
  intro v hv
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hv
  have split := Nat.div_add_mod' i width
  have within := Nat.mod_lt i pw
  have bound : i/width<q := (Nat.div_lt_iff_lt_mul pw).2 (by omega)
  apply all ⟨i/width,bound⟩ _
  apply List.mem_iff_getElem.mpr
  have ix : i % width<((vs.drop (i/width*width)).take width).length := by simp only [List.length_take,List.length_drop];omega
  refine ⟨i % width,ix,?_⟩
  simp only [List.getElem_take,List.getElem_drop]
  simp [split]
lemma join_exclusions {m k : ℕ} {v : List ℕ} (term : terminal m v=false)
    (no : ∀ w∈successors m k v,Excluded m k w) : Excluded m (k+1) v := by
  intro h
  rcases move h with e|⟨w,hw,hf⟩
  · exact Bool.noConfusion (term.symm.trans e)
  · exact no w hw hf
end PEqualNP.Outside.L_meta_12186.KFive

namespace PEqualNP.Outside.L_meta_12186.KFive

/- A stored bound proves that a smaller set of signals needs a stated number of gates. A receipt reconstructs all the restricted live signals from that set. Combining the bound with the zero signals lost by restriction excludes the proposed continuation. -/
structure FloorData where
  pairMask : ℕ
  lower : ℕ
  basis : List ℕ
deriving Inhabited
def Floor (m : ℕ) (s : FloorData) := ∀ k,Possible m k (0::s.basis) → s.lower≤k
theorem floorChecked {m : ℕ} {s : FloorData} (checked : start m (s.lower-1) (0::s.basis)=false) : Floor m s := by
  intro k poss
  by_contra small
  obtain ⟨j,S,le,live,sub⟩ := poss
  exact Bool.noConfusion (checked.symm.trans (start_complete live _ sub _ (by omega)))
lemma getMember {av : List ℕ} (zeroMem : 0∈av) (i : ℕ) : av.getD i 0∈av := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : av[i]? with
  | none => exact zeroMem
  | some t => exact List.mem_of_getElem? e

def instruction (av : List ℕ) (part : ℕ) :=
  let n := (part &&& 4095)-1
  combine (n % 4) (av.getD ((n >>> 2) &&& 15) 0) (av.getD ((n >>> 6) &&& 15) 0)
def replay : ℕ → ℕ → List ℕ → List ℕ
  | 0,_,av => av
  | k+1,code,av => if code=0 then av else replay k (code >>> 12) (av++[instruction av code])
def paidCount : ℕ → ℕ → ℕ
  | 0,_ => 0
  | k+1,code => if code=0 then 0 else paidCount k (code >>> 12)+1

theorem replay_back {m k : ℕ} (count code : ℕ) (av : List ℕ) (hasZero : 0∈av)
    (later : Possible m k (replay count code av)) : Possible m (k+paidCount count code) av := by
  induction count generalizing code av with
  | zero => simpa [replay,paidCount] using later
  | succ n ih =>
    by_cases stop : code=0
    · simpa [replay,paidCount,stop] using later
    rw [replay,ite_eq_right stop] at later
    have post := ih _ (av++[instruction av code]) (by simp [hasZero]) later
    let p := (code &&& 4095)-1
    have full := pullPaid (d:=p % 4) (Nat.mod_lt _ (by decide)) (getMember hasZero ((p >>> 2) &&& 15)) (getMember hasZero ((p >>> 6) &&& 15)) post
    obtain ⟨j,S,lim,live,sub⟩ := full
    refine ⟨j,S,?_,live,sub⟩
    rw [paidCount,ite_eq_right stop]
    have one (b : Bool) : b.toNat≤1 := by cases b <;> decide
    have bound := one (charge av (combine (p % 4) (av.getD ((p >>> 2) &&& 15) 0) (av.getD ((p >>> 6) &&& 15) 0)))
    omega

def contradictsFloor (m fuel : ℕ) (v : List ℕ) (s : FloorData) (code : ℕ) : Bool :=
  let r := min s.pairMask.log2 (m-1)
  let pv := v.map (slice m s.pairMask r)
  let av := replay 5 code (0::s.basis)
  fuel+paidCount 5 code<s.lower+pv.count 0 && pv.all (fun x => av.contains x)
lemma deadCount (f : ℕ→ℕ) {v : List ℕ} (nd : v.Nodup) :
    dead f v.toFinset=(v.map f).count 0 := by
  unfold dead
  have E : v.toFinset.filter (fun x => f x=0) = (v.filter (fun x => decide (f x=0))).toFinset := by ext x;simp
  rw [E,List.toFinset_card_of_nodup (nd.filter _)]
  simp only [List.count_eq_countP,List.countP_map]
  rw [List.countP_eq_length_filter]
  congr 2

theorem floor_consistent {m fuel : ℕ} (pos : 0<m) {v : List ℕ} (ok : feasible m fuel v) (s : FloorData)
    (known : Floor m s) (code : ℕ) : contradictsFloor m fuel v s code=false := by
  let r := min s.pairMask.log2 (m-1)
  let p := projection m s.pairMask r (show r<m by dsimp [r];omega)
  let pv := v.map p.toFun
  let av := replay 5 code (0::s.basis)
  obtain ⟨k,hk,live,nd⟩ := ok
  obtain ⟨l,T,lim,pr,inside⟩ := projectLive p live
  rw [deadCount _ nd] at lim
  apply Bool.eq_false_iff.mpr
  intro bad
  change (decide (fuel+paidCount 5 code < s.lower+pv.count 0) && pv.all (fun x => av.contains x))=true at bad
  simp only [Bool.and_eq_true] at bad
  obtain ⟨lo,mem⟩ := bad
  have low := of_decide_eq_true lo
  have final : Possible m l av := by
    refine ⟨l,T,le_rfl,pr,?_⟩
    intro x hx
    have active : x∈pv := by simpa [pv] using inside x hx
    exact List.contains_iff_mem.mp (List.all_eq_true.mp mem x active)
  have size := known _ (replay_back 5 code (0::s.basis) (by simp) final)
  change l+pv.count 0≤k at lim
  omega

def Memo := ℕ → FloorData × ℕ
def Certified (m : ℕ) (db : Memo) := ∀ i,Floor m (db i).1
inductive Advice where
  | plain
  | restrict (which : ℕ)
  | saved (index : ℕ)
  | fork (codes : ℕ) (nested : List Advice)
deriving Inhabited
def chooseAdvice (tag : ℕ) (gs : List Advice) : Advice :=
  if tag=1 then gs.headD .plain else if tag=0 then .plain else if tag<1024 then .restrict (tag-2) else .saved (tag-1024)
def memoRows (go : Advice → List ℕ → Bool) : List (List ℕ) → ℕ → List Advice → Bool
  | [],_,_ => false
  | v::vs,code,gs =>
    let tag := code &&& 4095
    go (chooseAdvice tag gs) v || memoRows go vs (code >>> 12) (if tag=1 then gs.tail else gs)
lemma memoRows_ok {go : Advice→List ℕ→Bool} {v : List ℕ} {vs : List (List ℕ)} (mem : v∈vs)
    (all : ∀ g,go g v=true) (code : ℕ) (gs : List Advice) : memoRows go vs code gs=true := by
  induction vs generalizing code gs with
  | nil => simp at mem
  | cons x xs ih =>
    rw [memoRows,Bool.or_eq_true]
    rcases List.mem_cons.mp mem with rfl|next
    · exact Or.inl (all _)
    · exact Or.inr (ih next _ _)
def audited (m : ℕ) (db : Memo) : ℕ → Advice → List ℕ → Bool
  | 0,_,v => terminal m v
  | k+1,.plain,v => search m (k+1) v
  | k+1,.restrict which,v => cutSearch m (zeroPairs m v which (full m)) (k+1) v
  | k+1,.saved i,v => !(contradictsFloor m (k+1) v (db i).1 (db i).2)
  | k+1,.fork code gs,v => terminal m v || memoRows (audited m db k) (successors m k v) code gs
theorem audited_complete {m : ℕ} (hm : 0<m) (db : Memo) (safe : Certified m db)
    (fuel : ℕ) (v : List ℕ) (h : feasible m fuel v) (g : Advice) : audited m db fuel g v=true := by
  induction fuel generalizing v g with
  | zero =>
    obtain ⟨j,lim,live,nd⟩ := h
    exact complete m 0 live lim v rfl nd
  | succ k ih =>
    cases g with
    | plain =>
      obtain ⟨j,lim,live,nd⟩ := h
      exact complete m (k+1) live lim v rfl nd
    | restrict which =>
      obtain ⟨j,lim,live,nd⟩ := h
      exact cut_complete hm live v rfl nd _ _ lim
    | saved i => simp [audited,floor_consistent hm h _ (safe i) _]
    | fork code gs =>
      rw [audited,Bool.or_eq_true]
      rcases move h with endNow|⟨w,hw,next⟩
      · exact Or.inl endNow
      · exact Or.inr (memoRows_ok hw (fun g => ih w next g) _ _)
lemma offAudit {m k v g} {db : Memo} (safe : Certified m db) (pos : 0<m) (e : audited m db k g v=false) : Excluded m k v := by
  intro h;exact Bool.noConfusion (e.symm.trans (audited_complete pos db safe k v h g))
lemma offMemoRows {m k : ℕ} {vs : List (List ℕ)} {i n code : ℕ} {gs : List Advice} {db : Memo}
    (safe : Certified m db) (pos : 0<m)
    (e : memoRows (audited m db k) ((vs.drop i).take n) code gs=false) : Block m k vs i n := by
  intro w hw h
  exact Bool.noConfusion (e.symm.trans (memoRows_ok hw (fun g => audited_complete pos db safe k w h g) code gs))
end PEqualNP.Outside.L_meta_12186.KFive

namespace PEqualNP.Outside.L_meta_12186.KFive



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def graph (x : Fin 5 → Bool) := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 3) || (x 2 && x 4) || (x 3 && x 4)

def posBits : ℕ := 0xc629494a316314a4a4c629463

def negBits : ℕ := 0x8220480a01411024048220441

def sample (bank : ℕ) (i : Fin 20) (j : Fin 5) := bank.testBit (5*i.val+j.val)

def inputs : List ℕ := [0x1045030cf,0x41120c333,0x1042830c3c,0x40a80c0fc0,0xaa000ff000]

def seeds : List Wire := inputs.map (fun a => (false,a))
theorem listed : ∀ i : Fin 20, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (20+i.val))=List.ofFn (sample negBits i) := by decide +kernel
theorem labels : ∀ i : Fin 20, graph (sample posBits i)=true ∧ graph (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 20, ∀ b∈inputs, b.testBit i.val≠b.testBit (20+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 20 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 5 C=graph) :
    ∃ k≤C.gates.countP counted, Live 20 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 5 → Bool) : C.eval (List.ofFn x)=graph x := congrFun eq x
  have good : Good 20 out.2 := by
    intro i hi same
    let j : Fin 20 := ⟨i,hi⟩
    have diff : read i out=read (20+i) out := by simp [read,same]
    have p := ev i;have n := ev (20+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa [reps,seeds,List.map_map,Function.comp_def] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩


theorem rawFloor {l : ℕ} {s : FloorData}
    (eq : s.lower=l+1) (nd : s.basis.Nodup) (liveAll : ∀ a ∈ s.basis, ∃ i : Fin 20, ∀ b ∈ s.basis, b.testBit i.val ≠ b.testBit (20+i.val) → b=a)
    (no : Excluded 20 l s.basis) : Floor 20 s := by
  intro k h
  by_contra! lo
  obtain ⟨j,S,hj,live,sub⟩ := h
  have sub' : ∀ a∈S,a∈s.basis := by
    intro a ha
    rcases List.mem_cons.mp (sub a ha) with e|e
    · exact False.elim (liveNonzero live a ha e)
    · exact e
  have es : S=s.basis.toFinset := by
    apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub' a ha))
    intro a ha
    obtain ⟨i,hi⟩ := liveAll a (List.mem_toFinset.mp ha)
    obtain ⟨v,hv,sep⟩ := liveSeparates live i.val i.isLt
    exact hi v (sub' v hv) sep ▸ hv
  exact no ⟨j,by omega,es ▸ live,nd⟩

def fl0 : FloorData := ⟨0xcf3c3,7,[0x1041030c3,0x41020c303,0x40280f0ffc,0xbac3cffc3c]⟩

def fl0k0 : List ℕ := [0x3,0x1041030c3,0x41020c303,0x40280f0ffc,0xbac3cffc3c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k0off : Excluded 20 5 fl0k0 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k0 = false).symm.trans (complete 20 5 live le fl0k0 rfl nd))

def fl0k1 : List ℕ := [0x51430f3c3,0x1041030c3,0x41020c303,0x40280f0ffc,0xbac3cffc3c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k1off : Excluded 20 5 fl0k1 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k1 = false).symm.trans (complete 20 5 live le fl0k1 rfl nd))

def fl0k2 : List ℕ := [0x1041030c0,0x1041030c3,0x41020c303,0x40280f0ffc,0xbac3cffc3c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k2off : Excluded 20 5 fl0k2 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k2 = false).symm.trans (complete 20 5 live le fl0k2 rfl nd))

def fl0k3 : List ℕ := [0x41020c300,0x1041030c3,0x41020c303,0x40280f0ffc,0xbac3cffc3c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k3off : Excluded 20 5 fl0k3 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k3 = false).symm.trans (complete 20 5 live le fl0k3 rfl nd))

def fl0k4 : List ℕ := [0xc0,0x1041030c3,0x40280f0ffc,0x41020c303,0xbac3cffc3c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k4off : Excluded 20 5 fl0k4 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k4 = false).symm.trans (complete 20 5 live le fl0k4 rfl nd))

def fl0k5 : List ℕ := [0x412c1f3fff,0x1041030c3,0x40280f0ffc,0x41020c303,0xbac3cffc3c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k5off : Excluded 20 5 fl0k5 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k5 = false).symm.trans (complete 20 5 live le fl0k5 rfl nd))

def fl0k6 : List ℕ := [0x104103003,0x1041030c3,0x40280f0ffc,0x41020c303,0xbac3cffc3c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k6off : Excluded 20 5 fl0k6 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k6 = false).symm.trans (complete 20 5 live le fl0k6 rfl nd))

def fl0k7 : List ℕ := [0x40280f0f3c,0x1041030c3,0x40280f0ffc,0x41020c303,0xbac3cffc3c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k7off : Excluded 20 5 fl0k7 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k7 = false).symm.trans (complete 20 5 live le fl0k7 rfl nd))

def fl0k8 : List ℕ := [0x3000,0x1041030c3,0xbac3cffc3c,0x41020c303,0x40280f0ffc]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k8off : Excluded 20 5 fl0k8 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k8 = false).symm.trans (complete 20 5 live le fl0k8 rfl nd))

def fl0k9 : List ℕ := [0xbbc7dffcff,0x1041030c3,0xbac3cffc3c,0x41020c303,0x40280f0ffc]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k9off : Excluded 20 5 fl0k9 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k9 = false).symm.trans (complete 20 5 live le fl0k9 rfl nd))

def fl0k10 : List ℕ := [0x1041000c3,0x1041030c3,0xbac3cffc3c,0x41020c303,0x40280f0ffc]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k10off : Excluded 20 5 fl0k10 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k10 = false).symm.trans (complete 20 5 live le fl0k10 rfl nd))

def fl0k11 : List ℕ := [0xbac3cfcc3c,0x1041030c3,0xbac3cffc3c,0x41020c303,0x40280f0ffc]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k11off : Excluded 20 5 fl0k11 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k11 = false).symm.trans (complete 20 5 live le fl0k11 rfl nd))

def fl0k12 : List ℕ := [0x300,0x41020c303,0x40280f0ffc,0x1041030c3,0xbac3cffc3c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k12off : Excluded 20 5 fl0k12 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k12 = false).symm.trans (complete 20 5 live le fl0k12 rfl nd))

def fl0k13 : List ℕ := [0x44382fcfff,0x41020c303,0x40280f0ffc,0x1041030c3,0xbac3cffc3c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k13off : Excluded 20 5 fl0k13 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k13 = false).symm.trans (complete 20 5 live le fl0k13 rfl nd))

def fl0k14 : List ℕ := [0x41020c003,0x41020c303,0x40280f0ffc,0x1041030c3,0xbac3cffc3c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k14off : Excluded 20 5 fl0k14 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k14 = false).symm.trans (complete 20 5 live le fl0k14 rfl nd))

def fl0k15 : List ℕ := [0x40280f0cfc,0x41020c303,0x40280f0ffc,0x1041030c3,0xbac3cffc3c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k15off : Excluded 20 5 fl0k15 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k15 = false).symm.trans (complete 20 5 live le fl0k15 rfl nd))

def fl0k16 : List ℕ := [0xc000,0x41020c303,0xbac3cffc3c,0x1041030c3,0x40280f0ffc]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k16off : Excluded 20 5 fl0k16 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k16 = false).symm.trans (complete 20 5 live le fl0k16 rfl nd))

def fl0k17 : List ℕ := [0xbed3efff3f,0x41020c303,0xbac3cffc3c,0x1041030c3,0x40280f0ffc]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k17off : Excluded 20 5 fl0k17 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k17 = false).symm.trans (complete 20 5 live le fl0k17 rfl nd))

def fl0k18 : List ℕ := [0x410200303,0x41020c303,0xbac3cffc3c,0x1041030c3,0x40280f0ffc]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k18off : Excluded 20 5 fl0k18 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k18 = false).symm.trans (complete 20 5 live le fl0k18 rfl nd))

def fl0k19 : List ℕ := [0xbac3cf3c3c,0x41020c303,0xbac3cffc3c,0x1041030c3,0x40280f0ffc]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k19off : Excluded 20 5 fl0k19 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k19 = false).symm.trans (complete 20 5 live le fl0k19 rfl nd))

def fl0k20 : List ℕ := [0xf0c3c,0x40280f0ffc,0xbac3cffc3c,0x1041030c3,0x41020c303]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k20off : Excluded 20 5 fl0k20 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k20 = false).symm.trans (complete 20 5 live le fl0k20 rfl nd))

def fl0k21 : List ℕ := [0xfaebcffffc,0x40280f0ffc,0xbac3cffc3c,0x1041030c3,0x41020c303]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k21off : Excluded 20 5 fl0k21 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k21 = false).symm.trans (complete 20 5 live le fl0k21 rfl nd))

def fl0k22 : List ℕ := [0x40280003c0,0x40280f0ffc,0xbac3cffc3c,0x1041030c3,0x41020c303]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k22off : Excluded 20 5 fl0k22 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k22 = false).symm.trans (complete 20 5 live le fl0k22 rfl nd))

def fl0k23 : List ℕ := [0xbac3c0f000,0x40280f0ffc,0xbac3cffc3c,0x1041030c3,0x41020c303]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl0k23off : Excluded 20 5 fl0k23 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl0k23 = false).symm.trans (complete 20 5 live le fl0k23 rfl nd))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floor0 : Floor 20 fl0 := by
  apply rawFloor (l:=6) rfl (by decide +kernel) (by decide +kernel)
  apply join_exclusions (by decide +kernel)
  intro v hv
  rw [show successors 20 5 fl0.basis = [fl0k0,fl0k1,fl0k2,fl0k3,fl0k4,fl0k5,fl0k6,fl0k7,fl0k8,fl0k9,fl0k10,fl0k11,fl0k12,fl0k13,fl0k14,fl0k15,fl0k16,fl0k17,fl0k18,fl0k19,fl0k20,fl0k21,fl0k22,fl0k23] by decide +kernel] at hv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact fl0k0off
  · exact fl0k1off
  · exact fl0k2off
  · exact fl0k3off
  · exact fl0k4off
  · exact fl0k5off
  · exact fl0k6off
  · exact fl0k7off
  · exact fl0k8off
  · exact fl0k9off
  · exact fl0k10off
  · exact fl0k11off
  · exact fl0k12off
  · exact fl0k13off
  · exact fl0k14off
  · exact fl0k15off
  · exact fl0k16off
  · exact fl0k17off
  · exact fl0k18off
  · exact fl0k19off
  · exact fl0k20off
  · exact fl0k21off
  · exact fl0k22off
  · exact fl0k23off

def fl1 : FloorData := ⟨0x3f03f,7,[0x10050300f,0x40120c033,0x10028f0ffc,0xeafc0fffc0]⟩

def fl1k0 : List ℕ := [0x3,0x10050300f,0x40120c033,0x10028f0ffc,0xeafc0fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k0off : Excluded 20 5 fl1k0 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k0 = false).symm.trans (complete 20 5 live le fl1k0 rfl nd))

def fl1k1 : List ℕ := [0x50170f03f,0x10050300f,0x40120c033,0x10028f0ffc,0xeafc0fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k1off : Excluded 20 5 fl1k1 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k1 = false).symm.trans (complete 20 5 live le fl1k1 rfl nd))

def fl1k2 : List ℕ := [0x10050300c,0x10050300f,0x40120c033,0x10028f0ffc,0xeafc0fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k2off : Excluded 20 5 fl1k2 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k2 = false).symm.trans (complete 20 5 live le fl1k2 rfl nd))

def fl1k3 : List ℕ := [0x40120c030,0x10050300f,0x40120c033,0x10028f0ffc,0xeafc0fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k3off : Excluded 20 5 fl1k3 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k3 = false).symm.trans (complete 20 5 live le fl1k3 rfl nd))

def fl1k4 : List ℕ := [0xc,0x10050300f,0x10028f0ffc,0x40120c033,0xeafc0fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k4off : Excluded 20 5 fl1k4 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k4 = false).symm.trans (complete 20 5 live le fl1k4 rfl nd))

def fl1k5 : List ℕ := [0x1102df3fff,0x10050300f,0x10028f0ffc,0x40120c033,0xeafc0fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k5off : Excluded 20 5 fl1k5 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k5 = false).symm.trans (complete 20 5 live le fl1k5 rfl nd))

def fl1k6 : List ℕ := [0x100503003,0x10050300f,0x10028f0ffc,0x40120c033,0xeafc0fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k6off : Excluded 20 5 fl1k6 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k6 = false).symm.trans (complete 20 5 live le fl1k6 rfl nd))

def fl1k7 : List ℕ := [0x10028f0ff0,0x10050300f,0x10028f0ffc,0x40120c033,0xeafc0fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k7off : Excluded 20 5 fl1k7 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k7 = false).symm.trans (complete 20 5 live le fl1k7 rfl nd))

def fl1k8 : List ℕ := [0x3000,0x10050300f,0xeafc0fffc0,0x40120c033,0x10028f0ffc]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k8off : Excluded 20 5 fl1k8 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k8 = false).symm.trans (complete 20 5 live le fl1k8 rfl nd))

def fl1k9 : List ℕ := [0xebfc5fffcf,0x10050300f,0xeafc0fffc0,0x40120c033,0x10028f0ffc]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k9off : Excluded 20 5 fl1k9 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k9 = false).symm.trans (complete 20 5 live le fl1k9 rfl nd))

def fl1k10 : List ℕ := [0x10050000f,0x10050300f,0xeafc0fffc0,0x40120c033,0x10028f0ffc]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k10off : Excluded 20 5 fl1k10 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k10 = false).symm.trans (complete 20 5 live le fl1k10 rfl nd))

def fl1k11 : List ℕ := [0xeafc0fcfc0,0x10050300f,0xeafc0fffc0,0x40120c033,0x10028f0ffc]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k11off : Excluded 20 5 fl1k11 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k11 = false).symm.trans (complete 20 5 live le fl1k11 rfl nd))

def fl1k12 : List ℕ := [0x30,0x40120c033,0x10028f0ffc,0x10050300f,0xeafc0fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k12off : Excluded 20 5 fl1k12 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k12 = false).symm.trans (complete 20 5 live le fl1k12 rfl nd))

def fl1k13 : List ℕ := [0x1403afcfff,0x40120c033,0x10028f0ffc,0x10050300f,0xeafc0fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k13off : Excluded 20 5 fl1k13 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k13 = false).symm.trans (complete 20 5 live le fl1k13 rfl nd))

def fl1k14 : List ℕ := [0x40120c003,0x40120c033,0x10028f0ffc,0x10050300f,0xeafc0fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k14off : Excluded 20 5 fl1k14 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k14 = false).symm.trans (complete 20 5 live le fl1k14 rfl nd))

def fl1k15 : List ℕ := [0x10028f0fcc,0x40120c033,0x10028f0ffc,0x10050300f,0xeafc0fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k15off : Excluded 20 5 fl1k15 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k15 = false).symm.trans (complete 20 5 live le fl1k15 rfl nd))

def fl1k16 : List ℕ := [0xc000,0x40120c033,0xeafc0fffc0,0x10050300f,0x10028f0ffc]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k16off : Excluded 20 5 fl1k16 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k16 = false).symm.trans (complete 20 5 live le fl1k16 rfl nd))

def fl1k17 : List ℕ := [0xeefd2ffff3,0x40120c033,0xeafc0fffc0,0x10050300f,0x10028f0ffc]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k17off : Excluded 20 5 fl1k17 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k17 = false).symm.trans (complete 20 5 live le fl1k17 rfl nd))

def fl1k18 : List ℕ := [0x401200033,0x40120c033,0xeafc0fffc0,0x10050300f,0x10028f0ffc]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k18off : Excluded 20 5 fl1k18 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k18 = false).symm.trans (complete 20 5 live le fl1k18 rfl nd))

def fl1k19 : List ℕ := [0xeafc0f3fc0,0x40120c033,0xeafc0fffc0,0x10050300f,0x10028f0ffc]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k19off : Excluded 20 5 fl1k19 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k19 = false).symm.trans (complete 20 5 live le fl1k19 rfl nd))

def fl1k20 : List ℕ := [0xf0fc0,0x10028f0ffc,0xeafc0fffc0,0x10050300f,0x40120c033]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k20off : Excluded 20 5 fl1k20 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k20 = false).symm.trans (complete 20 5 live le fl1k20 rfl nd))

def fl1k21 : List ℕ := [0xfafe8ffffc,0x10028f0ffc,0xeafc0fffc0,0x10050300f,0x40120c033]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k21off : Excluded 20 5 fl1k21 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k21 = false).symm.trans (complete 20 5 live le fl1k21 rfl nd))

def fl1k22 : List ℕ := [0x100280003c,0x10028f0ffc,0xeafc0fffc0,0x10050300f,0x40120c033]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k22off : Excluded 20 5 fl1k22 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k22 = false).symm.trans (complete 20 5 live le fl1k22 rfl nd))

def fl1k23 : List ℕ := [0xeafc00f000,0x10028f0ffc,0xeafc0fffc0,0x10050300f,0x40120c033]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl1k23off : Excluded 20 5 fl1k23 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl1k23 = false).symm.trans (complete 20 5 live le fl1k23 rfl nd))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floor1 : Floor 20 fl1 := by
  apply rawFloor (l:=6) rfl (by decide +kernel) (by decide +kernel)
  apply join_exclusions (by decide +kernel)
  intro v hv
  rw [show successors 20 5 fl1.basis = [fl1k0,fl1k1,fl1k2,fl1k3,fl1k4,fl1k5,fl1k6,fl1k7,fl1k8,fl1k9,fl1k10,fl1k11,fl1k12,fl1k13,fl1k14,fl1k15,fl1k16,fl1k17,fl1k18,fl1k19,fl1k20,fl1k21,fl1k22,fl1k23] by decide +kernel] at hv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact fl1k0off
  · exact fl1k1off
  · exact fl1k2off
  · exact fl1k3off
  · exact fl1k4off
  · exact fl1k5off
  · exact fl1k6off
  · exact fl1k7off
  · exact fl1k8off
  · exact fl1k9off
  · exact fl1k10off
  · exact fl1k11off
  · exact fl1k12off
  · exact fl1k13off
  · exact fl1k14off
  · exact fl1k15off
  · exact fl1k16off
  · exact fl1k17off
  · exact fl1k18off
  · exact fl1k19off
  · exact fl1k20off
  · exact fl1k21off
  · exact fl1k22off
  · exact fl1k23off

def fl2 : FloorData := ⟨0xfff,7,[0x45000cf,0x11200333,0x428ffc3c,0xffa80fffc0]⟩

def fl2k0 : List ℕ := [0x3,0x45000cf,0x11200333,0x428ffc3c,0xffa80fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k0off : Excluded 20 5 fl2k0 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k0 = false).symm.trans (complete 20 5 live le fl2k0 rfl nd))

def fl2k1 : List ℕ := [0x157003ff,0x45000cf,0x11200333,0x428ffc3c,0xffa80fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k1off : Excluded 20 5 fl2k1 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k1 = false).symm.trans (complete 20 5 live le fl2k1 rfl nd))

def fl2k2 : List ℕ := [0x45000cc,0x45000cf,0x11200333,0x428ffc3c,0xffa80fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k2off : Excluded 20 5 fl2k2 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k2 = false).symm.trans (complete 20 5 live le fl2k2 rfl nd))

def fl2k3 : List ℕ := [0x11200330,0x45000cf,0x11200333,0x428ffc3c,0xffa80fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k3off : Excluded 20 5 fl2k3 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k3 = false).symm.trans (complete 20 5 live le fl2k3 rfl nd))

def fl2k4 : List ℕ := [0xc,0x45000cf,0x428ffc3c,0x11200333,0xffa80fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k4off : Excluded 20 5 fl2k4 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k4 = false).symm.trans (complete 20 5 live le fl2k4 rfl nd))

def fl2k5 : List ℕ := [0x46dffcff,0x45000cf,0x428ffc3c,0x11200333,0xffa80fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k5off : Excluded 20 5 fl2k5 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k5 = false).symm.trans (complete 20 5 live le fl2k5 rfl nd))

def fl2k6 : List ℕ := [0x45000c3,0x45000cf,0x428ffc3c,0x11200333,0xffa80fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k6off : Excluded 20 5 fl2k6 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k6 = false).symm.trans (complete 20 5 live le fl2k6 rfl nd))

def fl2k7 : List ℕ := [0x428ffc30,0x45000cf,0x428ffc3c,0x11200333,0xffa80fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k7off : Excluded 20 5 fl2k7 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k7 = false).symm.trans (complete 20 5 live le fl2k7 rfl nd))

def fl2k8 : List ℕ := [0xc0,0x45000cf,0xffa80fffc0,0x11200333,0x428ffc3c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k8off : Excluded 20 5 fl2k8 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k8 = false).symm.trans (complete 20 5 live le fl2k8 rfl nd))

def fl2k9 : List ℕ := [0xffac5fffcf,0x45000cf,0xffa80fffc0,0x11200333,0x428ffc3c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k9off : Excluded 20 5 fl2k9 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k9 = false).symm.trans (complete 20 5 live le fl2k9 rfl nd))

def fl2k10 : List ℕ := [0x450000f,0x45000cf,0xffa80fffc0,0x11200333,0x428ffc3c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k10off : Excluded 20 5 fl2k10 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k10 = false).symm.trans (complete 20 5 live le fl2k10 rfl nd))

def fl2k11 : List ℕ := [0xffa80fff00,0x45000cf,0xffa80fffc0,0x11200333,0x428ffc3c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k11off : Excluded 20 5 fl2k11 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k11 = false).symm.trans (complete 20 5 live le fl2k11 rfl nd))

def fl2k12 : List ℕ := [0x30,0x11200333,0x428ffc3c,0x45000cf,0xffa80fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k12off : Excluded 20 5 fl2k12 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k12 = false).symm.trans (complete 20 5 live le fl2k12 rfl nd))

def fl2k13 : List ℕ := [0x53afff3f,0x11200333,0x428ffc3c,0x45000cf,0xffa80fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k13off : Excluded 20 5 fl2k13 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k13 = false).symm.trans (complete 20 5 live le fl2k13 rfl nd))

def fl2k14 : List ℕ := [0x11200303,0x11200333,0x428ffc3c,0x45000cf,0xffa80fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k14off : Excluded 20 5 fl2k14 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k14 = false).symm.trans (complete 20 5 live le fl2k14 rfl nd))

def fl2k15 : List ℕ := [0x428ffc0c,0x11200333,0x428ffc3c,0x45000cf,0xffa80fffc0]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k15off : Excluded 20 5 fl2k15 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k15 = false).symm.trans (complete 20 5 live le fl2k15 rfl nd))

def fl2k16 : List ℕ := [0x300,0x11200333,0xffa80fffc0,0x45000cf,0x428ffc3c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k16off : Excluded 20 5 fl2k16 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k16 = false).symm.trans (complete 20 5 live le fl2k16 rfl nd))

def fl2k17 : List ℕ := [0xffb92ffff3,0x11200333,0xffa80fffc0,0x45000cf,0x428ffc3c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k17off : Excluded 20 5 fl2k17 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k17 = false).symm.trans (complete 20 5 live le fl2k17 rfl nd))

def fl2k18 : List ℕ := [0x11200033,0x11200333,0xffa80fffc0,0x45000cf,0x428ffc3c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k18off : Excluded 20 5 fl2k18 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k18 = false).symm.trans (complete 20 5 live le fl2k18 rfl nd))

def fl2k19 : List ℕ := [0xffa80ffcc0,0x11200333,0xffa80fffc0,0x45000cf,0x428ffc3c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k19off : Excluded 20 5 fl2k19 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k19 = false).symm.trans (complete 20 5 live le fl2k19 rfl nd))

def fl2k20 : List ℕ := [0xffc00,0x428ffc3c,0xffa80fffc0,0x45000cf,0x11200333]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k20off : Excluded 20 5 fl2k20 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k20 = false).symm.trans (complete 20 5 live le fl2k20 rfl nd))

def fl2k21 : List ℕ := [0xffea8ffffc,0x428ffc3c,0xffa80fffc0,0x45000cf,0x11200333]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k21off : Excluded 20 5 fl2k21 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k21 = false).symm.trans (complete 20 5 live le fl2k21 rfl nd))

def fl2k22 : List ℕ := [0x4280003c,0x428ffc3c,0xffa80fffc0,0x45000cf,0x11200333]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k22off : Excluded 20 5 fl2k22 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k22 = false).symm.trans (complete 20 5 live le fl2k22 rfl nd))

def fl2k23 : List ℕ := [0xffa80003c0,0x428ffc3c,0xffa80fffc0,0x45000cf,0x11200333]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl2k23off : Excluded 20 5 fl2k23 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl2k23 = false).symm.trans (complete 20 5 live le fl2k23 rfl nd))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floor2 : Floor 20 fl2 := by
  apply rawFloor (l:=6) rfl (by decide +kernel) (by decide +kernel)
  apply join_exclusions (by decide +kernel)
  intro v hv
  rw [show successors 20 5 fl2.basis = [fl2k0,fl2k1,fl2k2,fl2k3,fl2k4,fl2k5,fl2k6,fl2k7,fl2k8,fl2k9,fl2k10,fl2k11,fl2k12,fl2k13,fl2k14,fl2k15,fl2k16,fl2k17,fl2k18,fl2k19,fl2k20,fl2k21,fl2k22,fl2k23] by decide +kernel] at hv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact fl2k0off
  · exact fl2k1off
  · exact fl2k2off
  · exact fl2k3off
  · exact fl2k4off
  · exact fl2k5off
  · exact fl2k6off
  · exact fl2k7off
  · exact fl2k8off
  · exact fl2k9off
  · exact fl2k10off
  · exact fl2k11off
  · exact fl2k12off
  · exact fl2k13off
  · exact fl2k14off
  · exact fl2k15off
  · exact fl2k16off
  · exact fl2k17off
  · exact fl2k18off
  · exact fl2k19off
  · exact fl2k20off
  · exact fl2k21off
  · exact fl2k22off
  · exact fl2k23off

def fl3 : FloorData := ⟨0xfcf30,7,[0x41100c330,0x1042030c30,0x40a00c3fcf,0xab0cfff0cf]⟩

def fl3k0 : List ℕ := [0x30,0x41100c330,0x1042030c30,0x40a00c3fcf,0xab0cfff0cf]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k0off : Excluded 20 5 fl3k0 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k0 = false).symm.trans (complete 20 5 live le fl3k0 rfl nd))

def fl3k1 : List ℕ := [0x145303cf30,0x41100c330,0x1042030c30,0x40a00c3fcf,0xab0cfff0cf]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k1off : Excluded 20 5 fl3k1 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k1 = false).symm.trans (complete 20 5 live le fl3k1 rfl nd))

def fl3k2 : List ℕ := [0x41100c300,0x41100c330,0x1042030c30,0x40a00c3fcf,0xab0cfff0cf]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k2off : Excluded 20 5 fl3k2 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k2 = false).symm.trans (complete 20 5 live le fl3k2 rfl nd))

def fl3k3 : List ℕ := [0x1042030c00,0x41100c330,0x1042030c30,0x40a00c3fcf,0xab0cfff0cf]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k3off : Excluded 20 5 fl3k3 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k3 = false).symm.trans (complete 20 5 live le fl3k3 rfl nd))

def fl3k4 : List ℕ := [0x300,0x41100c330,0x40a00c3fcf,0x1042030c30,0xab0cfff0cf]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k4off : Excluded 20 5 fl3k4 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k4 = false).symm.trans (complete 20 5 live le fl3k4 rfl nd))

def fl3k5 : List ℕ := [0x44b10cffff,0x41100c330,0x40a00c3fcf,0x1042030c30,0xab0cfff0cf]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k5off : Excluded 20 5 fl3k5 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k5 = false).symm.trans (complete 20 5 live le fl3k5 rfl nd))

def fl3k6 : List ℕ := [0x41100c030,0x41100c330,0x40a00c3fcf,0x1042030c30,0xab0cfff0cf]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k6off : Excluded 20 5 fl3k6 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k6 = false).symm.trans (complete 20 5 live le fl3k6 rfl nd))

def fl3k7 : List ℕ := [0x40a00c3ccf,0x41100c330,0x40a00c3fcf,0x1042030c30,0xab0cfff0cf]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k7off : Excluded 20 5 fl3k7 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k7 = false).symm.trans (complete 20 5 live le fl3k7 rfl nd))

def fl3k8 : List ℕ := [0xc000,0x41100c330,0xab0cfff0cf,0x1042030c30,0x40a00c3fcf]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k8off : Excluded 20 5 fl3k8 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k8 = false).symm.trans (complete 20 5 live le fl3k8 rfl nd))

def fl3k9 : List ℕ := [0xaf1dfff3ff,0x41100c330,0xab0cfff0cf,0x1042030c30,0x40a00c3fcf]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k9off : Excluded 20 5 fl3k9 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k9 = false).symm.trans (complete 20 5 live le fl3k9 rfl nd))

def fl3k10 : List ℕ := [0x411000330,0x41100c330,0xab0cfff0cf,0x1042030c30,0x40a00c3fcf]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k10off : Excluded 20 5 fl3k10 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k10 = false).symm.trans (complete 20 5 live le fl3k10 rfl nd))

def fl3k11 : List ℕ := [0xab0cff30cf,0x41100c330,0xab0cfff0cf,0x1042030c30,0x40a00c3fcf]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k11off : Excluded 20 5 fl3k11 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k11 = false).symm.trans (complete 20 5 live le fl3k11 rfl nd))

def fl3k12 : List ℕ := [0xc00,0x1042030c30,0x40a00c3fcf,0x41100c330,0xab0cfff0cf]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k12off : Excluded 20 5 fl3k12 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k12 = false).symm.trans (complete 20 5 live le fl3k12 rfl nd))

def fl3k13 : List ℕ := [0x50e20f3fff,0x1042030c30,0x40a00c3fcf,0x41100c330,0xab0cfff0cf]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k13off : Excluded 20 5 fl3k13 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k13 = false).symm.trans (complete 20 5 live le fl3k13 rfl nd))

def fl3k14 : List ℕ := [0x1042030030,0x1042030c30,0x40a00c3fcf,0x41100c330,0xab0cfff0cf]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k14off : Excluded 20 5 fl3k14 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k14 = false).symm.trans (complete 20 5 live le fl3k14 rfl nd))

def fl3k15 : List ℕ := [0x40a00c33cf,0x1042030c30,0x40a00c3fcf,0x41100c330,0xab0cfff0cf]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k15off : Excluded 20 5 fl3k15 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k15 = false).symm.trans (complete 20 5 live le fl3k15 rfl nd))

def fl3k16 : List ℕ := [0x30000,0x1042030c30,0xab0cfff0cf,0x41100c330,0x40a00c3fcf]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k16off : Excluded 20 5 fl3k16 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k16 = false).symm.trans (complete 20 5 live le fl3k16 rfl nd))

def fl3k17 : List ℕ := [0xbb4efffcff,0x1042030c30,0xab0cfff0cf,0x41100c330,0x40a00c3fcf]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k17off : Excluded 20 5 fl3k17 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k17 = false).symm.trans (complete 20 5 live le fl3k17 rfl nd))

def fl3k18 : List ℕ := [0x1042000c30,0x1042030c30,0xab0cfff0cf,0x41100c330,0x40a00c3fcf]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k18off : Excluded 20 5 fl3k18 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k18 = false).symm.trans (complete 20 5 live le fl3k18 rfl nd))

def fl3k19 : List ℕ := [0xab0cfcf0cf,0x1042030c30,0xab0cfff0cf,0x41100c330,0x40a00c3fcf]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k19off : Excluded 20 5 fl3k19 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k19 = false).symm.trans (complete 20 5 live le fl3k19 rfl nd))

def fl3k20 : List ℕ := [0xc30cf,0x40a00c3fcf,0xab0cfff0cf,0x41100c330,0x1042030c30]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k20off : Excluded 20 5 fl3k20 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k20 = false).symm.trans (complete 20 5 live le fl3k20 rfl nd))

def fl3k21 : List ℕ := [0xebacffffcf,0x40a00c3fcf,0xab0cfff0cf,0x41100c330,0x1042030c30]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k21off : Excluded 20 5 fl3k21 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k21 = false).symm.trans (complete 20 5 live le fl3k21 rfl nd))

def fl3k22 : List ℕ := [0x40a0000f00,0x40a00c3fcf,0xab0cfff0cf,0x41100c330,0x1042030c30]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k22off : Excluded 20 5 fl3k22 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k22 = false).symm.trans (complete 20 5 live le fl3k22 rfl nd))

def fl3k23 : List ℕ := [0xab0cf3c000,0x40a00c3fcf,0xab0cfff0cf,0x41100c330,0x1042030c30]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl3k23off : Excluded 20 5 fl3k23 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl3k23 = false).symm.trans (complete 20 5 live le fl3k23 rfl nd))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floor3 : Floor 20 fl3 := by
  apply rawFloor (l:=6) rfl (by decide +kernel) (by decide +kernel)
  apply join_exclusions (by decide +kernel)
  intro v hv
  rw [show successors 20 5 fl3.basis = [fl3k0,fl3k1,fl3k2,fl3k3,fl3k4,fl3k5,fl3k6,fl3k7,fl3k8,fl3k9,fl3k10,fl3k11,fl3k12,fl3k13,fl3k14,fl3k15,fl3k16,fl3k17,fl3k18,fl3k19,fl3k20,fl3k21,fl3k22,fl3k23] by decide +kernel] at hv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact fl3k0off
  · exact fl3k1off
  · exact fl3k2off
  · exact fl3k3off
  · exact fl3k4off
  · exact fl3k5off
  · exact fl3k6off
  · exact fl3k7off
  · exact fl3k8off
  · exact fl3k9off
  · exact fl3k10off
  · exact fl3k11off
  · exact fl3k12off
  · exact fl3k13off
  · exact fl3k14off
  · exact fl3k15off
  · exact fl3k16off
  · exact fl3k17off
  · exact fl3k18off
  · exact fl3k19off
  · exact fl3k20off
  · exact fl3k21off
  · exact fl3k22off
  · exact fl3k23off

def fl4 : FloorData := ⟨0xf3ccc,7,[0x1044030cc,0x1040830c0c,0x40880ccff3,0xae333ff333]⟩

def fl4k0 : List ℕ := [0xc,0x1044030cc,0x1040830c0c,0x40880ccff3,0xae333ff333]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k0off : Excluded 20 5 fl4k0 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k0 = false).symm.trans (complete 20 5 live le fl4k0 rfl nd))

def fl4k1 : List ℕ := [0x1144c33ccc,0x1044030cc,0x1040830c0c,0x40880ccff3,0xae333ff333]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k1off : Excluded 20 5 fl4k1 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k1 = false).symm.trans (complete 20 5 live le fl4k1 rfl nd))

def fl4k2 : List ℕ := [0x1044030c0,0x1044030cc,0x1040830c0c,0x40880ccff3,0xae333ff333]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k2off : Excluded 20 5 fl4k2 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k2 = false).symm.trans (complete 20 5 live le fl4k2 rfl nd))

def fl4k3 : List ℕ := [0x1040830c00,0x1044030cc,0x1040830c0c,0x40880ccff3,0xae333ff333]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k3off : Excluded 20 5 fl4k3 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k3 = false).symm.trans (complete 20 5 live le fl4k3 rfl nd))

def fl4k4 : List ℕ := [0xc0,0x1044030cc,0x40880ccff3,0x1040830c0c,0xae333ff333]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k4off : Excluded 20 5 fl4k4 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k4 = false).symm.trans (complete 20 5 live le fl4k4 rfl nd))

def fl4k5 : List ℕ := [0x418c4cffff,0x1044030cc,0x40880ccff3,0x1040830c0c,0xae333ff333]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k5off : Excluded 20 5 fl4k5 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k5 = false).symm.trans (complete 20 5 live le fl4k5 rfl nd))

def fl4k6 : List ℕ := [0x10440300c,0x1044030cc,0x40880ccff3,0x1040830c0c,0xae333ff333]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k6off : Excluded 20 5 fl4k6 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k6 = false).symm.trans (complete 20 5 live le fl4k6 rfl nd))

def fl4k7 : List ℕ := [0x40880ccf33,0x1044030cc,0x40880ccff3,0x1040830c0c,0xae333ff333]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k7off : Excluded 20 5 fl4k7 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k7 = false).symm.trans (complete 20 5 live le fl4k7 rfl nd))

def fl4k8 : List ℕ := [0x3000,0x1044030cc,0xae333ff333,0x1040830c0c,0x40880ccff3]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k8off : Excluded 20 5 fl4k8 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k8 = false).symm.trans (complete 20 5 live le fl4k8 rfl nd))

def fl4k9 : List ℕ := [0xaf377ff3ff,0x1044030cc,0xae333ff333,0x1040830c0c,0x40880ccff3]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k9off : Excluded 20 5 fl4k9 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k9 = false).symm.trans (complete 20 5 live le fl4k9 rfl nd))

def fl4k10 : List ℕ := [0x1044000cc,0x1044030cc,0xae333ff333,0x1040830c0c,0x40880ccff3]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k10off : Excluded 20 5 fl4k10 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k10 = false).symm.trans (complete 20 5 live le fl4k10 rfl nd))

def fl4k11 : List ℕ := [0xae333fc333,0x1044030cc,0xae333ff333,0x1040830c0c,0x40880ccff3]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k11off : Excluded 20 5 fl4k11 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k11 = false).symm.trans (complete 20 5 live le fl4k11 rfl nd))

def fl4k12 : List ℕ := [0xc00,0x1040830c0c,0x40880ccff3,0x1044030cc,0xae333ff333]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k12off : Excluded 20 5 fl4k12 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k12 = false).symm.trans (complete 20 5 live le fl4k12 rfl nd))

def fl4k13 : List ℕ := [0x50c88fcfff,0x1040830c0c,0x40880ccff3,0x1044030cc,0xae333ff333]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k13off : Excluded 20 5 fl4k13 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k13 = false).symm.trans (complete 20 5 live le fl4k13 rfl nd))

def fl4k14 : List ℕ := [0x104083000c,0x1040830c0c,0x40880ccff3,0x1044030cc,0xae333ff333]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k14off : Excluded 20 5 fl4k14 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k14 = false).symm.trans (complete 20 5 live le fl4k14 rfl nd))

def fl4k15 : List ℕ := [0x40880cc3f3,0x1040830c0c,0x40880ccff3,0x1044030cc,0xae333ff333]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k15off : Excluded 20 5 fl4k15 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k15 = false).symm.trans (complete 20 5 live le fl4k15 rfl nd))

def fl4k16 : List ℕ := [0x30000,0x1040830c0c,0xae333ff333,0x1044030cc,0x40880ccff3]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k16off : Excluded 20 5 fl4k16 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k16 = false).symm.trans (complete 20 5 live le fl4k16 rfl nd))

def fl4k17 : List ℕ := [0xbe73bfff3f,0x1040830c0c,0xae333ff333,0x1044030cc,0x40880ccff3]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k17off : Excluded 20 5 fl4k17 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k17 = false).symm.trans (complete 20 5 live le fl4k17 rfl nd))

def fl4k18 : List ℕ := [0x1040800c0c,0x1040830c0c,0xae333ff333,0x1044030cc,0x40880ccff3]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k18off : Excluded 20 5 fl4k18 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k18 = false).symm.trans (complete 20 5 live le fl4k18 rfl nd))

def fl4k19 : List ℕ := [0xae333cf333,0x1040830c0c,0xae333ff333,0x1044030cc,0x40880ccff3]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k19off : Excluded 20 5 fl4k19 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k19 = false).symm.trans (complete 20 5 live le fl4k19 rfl nd))

def fl4k20 : List ℕ := [0xcc333,0x40880ccff3,0xae333ff333,0x1044030cc,0x1040830c0c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k20off : Excluded 20 5 fl4k20 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k20 = false).symm.trans (complete 20 5 live le fl4k20 rfl nd))

def fl4k21 : List ℕ := [0xeebb3ffff3,0x40880ccff3,0xae333ff333,0x1044030cc,0x1040830c0c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k21off : Excluded 20 5 fl4k21 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k21 = false).symm.trans (complete 20 5 live le fl4k21 rfl nd))

def fl4k22 : List ℕ := [0x4088000cc0,0x40880ccff3,0xae333ff333,0x1044030cc,0x1040830c0c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k22off : Excluded 20 5 fl4k22 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k22 = false).symm.trans (complete 20 5 live le fl4k22 rfl nd))

def fl4k23 : List ℕ := [0xae33333000,0x40880ccff3,0xae333ff333,0x1044030cc,0x1040830c0c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem fl4k23off : Excluded 20 5 fl4k23 := by
  intro h
  obtain ⟨k,le,live,nd⟩ := h
  exact Bool.noConfusion ((by decide +kernel : search 20 5 fl4k23 = false).symm.trans (complete 20 5 live le fl4k23 rfl nd))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floor4 : Floor 20 fl4 := by
  apply rawFloor (l:=6) rfl (by decide +kernel) (by decide +kernel)
  apply join_exclusions (by decide +kernel)
  intro v hv
  rw [show successors 20 5 fl4.basis = [fl4k0,fl4k1,fl4k2,fl4k3,fl4k4,fl4k5,fl4k6,fl4k7,fl4k8,fl4k9,fl4k10,fl4k11,fl4k12,fl4k13,fl4k14,fl4k15,fl4k16,fl4k17,fl4k18,fl4k19,fl4k20,fl4k21,fl4k22,fl4k23] by decide +kernel] at hv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact fl4k0off
  · exact fl4k1off
  · exact fl4k2off
  · exact fl4k3off
  · exact fl4k4off
  · exact fl4k5off
  · exact fl4k6off
  · exact fl4k7off
  · exact fl4k8off
  · exact fl4k9off
  · exact fl4k10off
  · exact fl4k11off
  · exact fl4k12off
  · exact fl4k13off
  · exact fl4k14off
  · exact fl4k15off
  · exact fl4k16off
  · exact fl4k17off
  · exact fl4k18off
  · exact fl4k19off
  · exact fl4k20off
  · exact fl4k21off
  · exact fl4k22off
  · exact fl4k23off

def fl5 : FloorData := ⟨0xf0c00,4,[0x1040030c00,0x40800cffff,0xaf3ffff3ff]⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floor5 : Floor 20 fl5 := floorChecked (by decide +kernel)

def fl6 : FloorData := ⟨0xc30c0,4,[0x1040030c0,0x40080fcfff,0xbef3ffff3f]⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floor6 : Floor 20 fl6 := floorChecked (by decide +kernel)

def fl7 : FloorData := ⟨0xcc300,4,[0x41000c300,0x40200f3fff,0xbbcffffcff]⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floor7 : Floor 20 fl7 := floorChecked (by decide +kernel)

def fl8 : FloorData := ⟨0xf003,4,[0x100103003,0x4002fcfff,0xfaffcffffc]⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floor8 : Floor 20 fl8 := floorChecked (by decide +kernel)

def fl9 : FloorData := ⟨0x3c3,4,[0x41000c3,0x102fff3f,0xffebcffffc]⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floor9 : Floor 20 fl9 := floorChecked (by decide +kernel)

def fl10 : FloorData := ⟨0x3c030,4,[0x40100c030,0x10020f3fff,0xebfcffffcf]⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floor10 : Floor 20 fl10 := floorChecked (by decide +kernel)

def fl11 : FloorData := ⟨0xf30,4,[0x11000330,0x420ffcff,0xffacffffcf]⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floor11 : Floor 20 fl11 := floorChecked (by decide +kernel)

def fl12 : FloorData := ⟨0x3300c,4,[0x10040300c,0x10008fcfff,0xeeff3ffff3]⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floor12 : Floor 20 fl12 := floorChecked (by decide +kernel)

def fl13 : FloorData := ⟨0xccc,4,[0x44000cc,0x408fff3f,0xffbb3ffff3]⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floor13 : Floor 20 fl13 := floorChecked (by decide +kernel)

def fl14 : FloorData := ⟨0x3f,4,[0x50000f,0x12ffff3,0xfffe8ffffc]⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floor14 : Floor 20 fl14 := floorChecked (by decide +kernel)

def floorData (i : ℕ) : FloorData := if i < 7 then if i < 3 then if i < 1 then fl0 else if i < 2 then fl1 else fl2 else if i < 5 then if i < 4 then fl3 else fl4 else if i < 6 then fl5 else fl6 else if i < 11 then if i < 9 then if i < 8 then fl7 else fl8 else if i < 10 then fl9 else fl10 else if i < 13 then if i < 12 then fl11 else fl12 else if i < 14 then fl13 else fl14

def receipt (i : ℕ) : ℕ × ℕ := if i < 174 then if i < 87 then if i < 43 then if i < 21 then if i < 10 then if i < 5 then if i < 2 then if i < 1 then (0,0x86) else (1,0xd6086) else if i < 3 then (2,0x11a0d6086) else if i < 4 then (0,0xd6086) else (3,0xd6086) else if i < 7 then if i < 6 then (4,0xd6086) else (2,0x11b0d6086) else if i < 8 then (0,0xd7086) else if i < 9 then (3,0xd7086) else (4,0xd7086) else if i < 15 then if i < 12 then if i < 11 then (5,0x87) else (6,0x87) else if i < 13 then (7,0x87) else if i < 14 then (2,0xd6086) else (0,0x116086) else if i < 18 then if i < 16 then (3,0x116086) else if i < 17 then (4,0x116086) else (1,0x11a0d6086) else if i < 19 then (1,0x11b0d6086) else if i < 20 then (0,0x117086) else (3,0x117086) else if i < 32 then if i < 26 then if i < 23 then if i < 22 then (4,0x117086) else (5,0xc7) else if i < 24 then (6,0xc7) else if i < 25 then (7,0xc7) else (5,0x0) else if i < 29 then if i < 27 then (5,0x86) else if i < 28 then (6,0x86) else (4,0xc60ca086) else if i < 30 then (7,0x0) else if i < 31 then (3,0xca086) else (6,0x0) else if i < 37 then if i < 34 then if i < 33 then (7,0x86) else (3,0xc60ca086) else if i < 35 then (4,0xca086) else if i < 36 then (5,0xc6) else (6,0xc6) else if i < 40 then if i < 38 then (4,0x10610a086) else if i < 39 then (3,0x10a086) else (7,0xc6) else if i < 41 then (3,0x10610a086) else if i < 42 then (4,0x10a086) else (3,0x86) else if i < 65 then if i < 54 then if i < 48 then if i < 45 then if i < 44 then (4,0xca0c6086) else (0,0xc6086) else if i < 46 then (0,0xca0c6086) else if i < 47 then (4,0xc6086) else (4,0x10a106086) else if i < 51 then if i < 49 then (0,0x106086) else if i < 50 then (0,0x10a106086) else (4,0x106086) else if i < 52 then (4,0x86) else if i < 53 then (3,0xca0c6086) else (0,0xca086) else if i < 59 then if i < 56 then if i < 55 then (0,0xc60ca086) else (3,0xc6086) else if i < 57 then (3,0x10a106086) else if i < 58 then (0,0x10a086) else (0,0x10610a086) else if i < 62 then if i < 60 then (3,0x106086) else if i < 61 then (8,0x86) else (9,0x86) else if i < 63 then (1,0xd7086) else if i < 64 then (2,0x11a0d7086) else (3,0xd6087) else if i < 76 then if i < 70 then if i < 67 then if i < 66 then (4,0xd6087) else (2,0xd7086) else if i < 68 then (3,0x116087) else if i < 69 then (4,0x116087) else (1,0x11a0d7086) else if i < 73 then if i < 71 then (3,0x87) else if i < 72 then (4,0xc6087) else (10,0x87) else if i < 74 then (4,0x106087) else if i < 75 then (11,0x87) else (4,0x87) else if i < 81 then if i < 78 then if i < 77 then (3,0xc6087) else (12,0x87) else if i < 79 then (3,0x106087) else if i < 80 then (13,0x87) else (1,0x86) else if i < 84 then if i < 82 then (2,0x116086) else if i < 83 then (1,0x116086) else (3,0x1160c6) else if i < 85 then (4,0x1160c6) else if i < 86 then (0,0x11a0d6086) else (1,0x117086) else if i < 130 then if i < 108 then if i < 97 then if i < 92 then if i < 89 then if i < 88 then (3,0x1170c6) else (4,0x1170c6) else if i < 90 then (0,0x11b0d6086) else if i < 91 then (5,0xcb) else (12,0xc7) else if i < 94 then if i < 93 then (10,0xc7) else (5,0xca) else if i < 95 then (12,0xc6) else if i < 96 then (4,0x10610e0c6) else (10,0x0) else if i < 102 then if i < 99 then if i < 98 then (3,0x10e0c6) else (12,0x0) else if i < 100 then (10,0xc6) else if i < 101 then (3,0x10610e0c6) else (4,0x10e0c6) else if i < 105 then if i < 103 then (3,0xc6) else if i < 104 then (12,0x86) else (4,0xca0860c6) else if i < 106 then (1,0xc6086) else if i < 107 then (10,0x86) else (1,0xca0c6086) else if i < 119 then if i < 113 then if i < 110 then if i < 109 then (4,0x860c6) else (4,0x10e1060c6) else if i < 111 then (1,0x106086) else if i < 112 then (1,0x10a106086) else (4,0x1060c6) else if i < 116 then if i < 114 then (4,0xc6) else if i < 115 then (3,0xca0860c6) else (1,0xca086) else if i < 117 then (1,0xc60ca086) else if i < 118 then (3,0x860c6) else (3,0x10e1060c6) else if i < 124 then if i < 121 then if i < 120 then (1,0x10a086) else (1,0x10610a086) else if i < 122 then (3,0x1060c6) else if i < 123 then (2,0x18e116086) else (1,0x14e086) else if i < 127 then if i < 125 then (3,0x14a0c6) else if i < 126 then (4,0x14a0c6) else (2,0x190116086) else if i < 128 then (1,0x150086) else if i < 129 then (3,0x14c0c6) else (4,0x14c0c6) else if i < 152 then if i < 141 then if i < 135 then if i < 132 then if i < 131 then (5,0x88) else (12,0x4c) else if i < 133 then (10,0x4c) else if i < 134 then (4,0x860ca0c6) else (3,0xca0c6) else if i < 138 then if i < 136 then (3,0x860ca0c6) else if i < 137 then (4,0xca0c6) else (14,0x86) else if i < 139 then (2,0xda117086) else if i < 140 then (3,0x960c7) else (4,0x960c7) else if i < 146 then if i < 143 then if i < 142 then (2,0x117086) else (3,0x1160c7) else if i < 144 then (4,0x1160c7) else if i < 145 then (0,0x11a0d7086) else (3,0xc7) else if i < 149 then if i < 147 then (4,0x860c7) else if i < 148 then (4,0x1060c7) else (11,0xc7) else if i < 150 then (4,0xc7) else if i < 151 then (3,0x860c7) else (3,0x1060c7) else if i < 163 then if i < 157 then if i < 154 then if i < 153 then (13,0xc7) else (2,0x86) else if i < 155 then (3,0x106) else if i < 156 then (13,0x0) else (13,0x86) else if i < 160 then if i < 158 then (4,0x10a086106) else if i < 159 then (11,0x0) else (2,0xc6086) else if i < 161 then (11,0x86) else if i < 162 then (2,0xca0c6086) else (4,0x86106) else if i < 168 then if i < 165 then if i < 164 then (13,0xc6) else (4,0x10e0c6106) else if i < 166 then (2,0x106086) else if i < 167 then (11,0xc6) else (2,0x10a106086) else if i < 171 then if i < 169 then (4,0xc6106) else if i < 170 then (4,0x106) else (3,0x10a086106) else if i < 172 then (2,0xca086) else if i < 173 then (2,0xc60ca086) else (3,0x86106) else if i < 261 then if i < 217 then if i < 195 then if i < 184 then if i < 179 then if i < 176 then if i < 175 then (3,0x10e0c6106) else (2,0x10a086) else if i < 177 then (2,0x10610a086) else if i < 178 then (3,0xc6106) else (2,0x14e086) else if i < 181 then if i < 180 then (3,0x14a106) else (4,0x14a106) else if i < 182 then (1,0x18e116086) else if i < 183 then (2,0x150086) else (1,0x190116086) else if i < 189 then if i < 186 then if i < 185 then (3,0x14c106) else (4,0x14c106) else if i < 187 then (5,0xc8) else if i < 188 then (13,0x4c) else (11,0x4c) else if i < 192 then if i < 190 then (4,0x8610a106) else if i < 191 then (3,0x10a106) else (3,0x8610a106) else if i < 193 then (4,0x10a106) else if i < 194 then (2,0x152086) else (3,0x14e106) else if i < 206 then if i < 200 then if i < 197 then if i < 196 then (4,0x14e106) else (0,0x18e116086) else if i < 198 then (2,0x154086) else if i < 199 then (3,0x150106) else (4,0x150106) else if i < 203 then if i < 201 then (0,0x190116086) else if i < 202 then (5,0xcc) else (13,0x50) else if i < 204 then (11,0x50) else if i < 205 then (4,0xc610e106) else (3,0x10e106) else if i < 211 then if i < 208 then if i < 207 then (3,0xc610e106) else (4,0x10e106) else if i < 209 then (1,0xda117086) else if i < 210 then (3,0x96107) else (4,0x96107) else if i < 214 then if i < 212 then (3,0xd6107) else if i < 213 then (4,0xd6107) else (0,0xda117086) else if i < 215 then (3,0x107) else if i < 216 then (4,0x86107) else (4,0xc6107) else if i < 239 then if i < 228 then if i < 222 then if i < 219 then if i < 218 then (4,0x107) else (3,0x86107) else if i < 220 then (3,0xc6107) else if i < 221 then (3,0x0) else (4,0x0) else if i < 225 then if i < 223 then (3,0xca) else if i < 224 then (3,0x860ca) else (3,0xcb) else if i < 226 then (0,0xc7086) else if i < 227 then (3,0x10a) else (3,0x8610a) else if i < 233 then if i < 230 then if i < 229 then (3,0x10b) else (0,0x107086) else if i < 231 then (3,0x1460ca) else if i < 232 then (3,0x14610a) else (4,0xc7086) else if i < 236 then if i < 234 then (4,0x107086) else if i < 235 then (3,0x10e086) else (4,0x10e086) else if i < 237 then (1,0x8e0c6086) else if i < 238 then (2,0x8e0c6086) else (0,0x10e086) else if i < 250 then if i < 244 then if i < 241 then if i < 240 then (3,0x8610e) else (3,0x10e) else if i < 242 then (3,0xc610e) else if i < 243 then (3,0x10f) else (1,0x107086) else if i < 247 then if i < 245 then (3,0x14610e) else if i < 246 then (4,0x870c6) else (4,0x1070c6) else if i < 248 then (3,0x10a0c6) else if i < 249 then (4,0x10a0c6) else (1,0x4e0ca086) else if i < 255 then if i < 252 then if i < 251 then (2,0x92106086) else (1,0x4e086) else if i < 253 then (1,0xca04e086) else if i < 254 then (3,0xc60ca) else (1,0x50086) else if i < 258 then if i < 256 then (3,0xcc) else if i < 257 then (1,0x10e086) else (3,0xc610a) else if i < 259 then (4,0x87106) else if i < 260 then (4,0xc7106) else (3,0xca106) else if i < 304 then if i < 282 then if i < 271 then if i < 266 then if i < 263 then if i < 262 then (4,0xca106) else (2,0x4e0ca086) else if i < 264 then (2,0x5210a086) else if i < 265 then (2,0x4e086) else (2,0xca04e086) else if i < 268 then if i < 267 then (3,0x10610a) else (2,0x50086) else if i < 269 then (3,0x10c) else if i < 270 then (2,0x10e086) else (3,0x1060ca) else if i < 276 then if i < 273 then if i < 272 then (2,0x52086) else (2,0x10a052086) else if i < 274 then (3,0x10610e) else if i < 275 then (2,0x54086) else (3,0x110) else if i < 279 then if i < 277 then (4,0xca) else if i < 278 then (4,0x860ca) else (4,0xcb) else if i < 280 then (0,0xcb086) else if i < 281 then (4,0x10a) else (4,0x8610a) else if i < 293 then if i < 287 then if i < 284 then if i < 283 then (4,0x10b) else (0,0x10b086) else if i < 285 then (4,0x1460ca) else if i < 286 then (4,0x14610a) else (3,0xc7086) else if i < 290 then if i < 288 then (3,0x107086) else if i < 289 then (4,0x8610e) else (4,0x10e) else if i < 291 then (4,0xc610e) else if i < 292 then (4,0x10f) else (1,0x10b086) else if i < 298 then if i < 295 then if i < 294 then (4,0x14610e) else (3,0x870c6) else if i < 296 then (3,0x1070c6) else if i < 297 then (1,0x8e086) else (1,0xc608e086) else if i < 301 then if i < 299 then (4,0xc60ca) else if i < 300 then (1,0x90086) else (4,0xcc) else if i < 302 then (4,0xc610a) else if i < 303 then (3,0x87106) else (3,0xc7106) else if i < 326 then if i < 315 then if i < 309 then if i < 306 then if i < 305 then (2,0x8e086) else (2,0xc608e086) else if i < 307 then (4,0x10610a) else if i < 308 then (2,0x90086) else (4,0x10c) else if i < 312 then if i < 310 then (4,0x1060ca) else if i < 311 then (2,0x92086) else (2,0x106092086) else if i < 313 then (4,0x10610e) else if i < 314 then (2,0x94086) else (4,0x110) else if i < 320 then if i < 317 then if i < 316 then (3,0x10e10a0ca) else (3,0x10a0ca) else if i < 318 then (3,0x10a10e0ca) else if i < 319 then (3,0x10e0ca) else (2,0x19610e086) else if i < 323 then if i < 321 then (3,0x1480ca) else if i < 322 then (4,0xc60860ca) else (3,0xc60860ca) else if i < 324 then (4,0x860c60ca) else if i < 325 then (3,0x860c60ca) else (3,0x10e0ca10a) else if i < 337 then if i < 331 then if i < 328 then if i < 327 then (3,0xca10a) else (1,0x19610e086) else if i < 329 then (3,0x14810a) else if i < 330 then (4,0x10608610a) else (3,0x10608610a) else if i < 334 then if i < 332 then (4,0x8610610a) else if i < 333 then (3,0x8610610a) else (3,0xca10e10a) else if i < 335 then (3,0x10e10a) else if i < 336 then (0,0x19610e086) else (3,0x14810e) else if i < 342 then if i < 339 then if i < 338 then (4,0x1060c610e) else (3,0x1060c610e) else if i < 340 then (4,0xc610610e) else if i < 341 then (3,0xc610610e) else (3,0x10a0ca10e) else if i < 345 then if i < 343 then (3,0xca10e) else if i < 344 then (3,0xca10a10e) else (3,0x10a10e) else if i < 346 then (0,0x0) else if i < 347 then (1,0x0) else (2,0x0)

def database (i : ℕ) : FloorData × ℕ := (floorData (receipt i).1,(receipt i).2)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorOk (i : ℕ) : Floor 20 (floorData i) := by
  unfold floorData
  repeat' split
  all_goals first | exact floor0 | exact floor1 | exact floor2 | exact floor3 | exact floor4 | exact floor5 | exact floor6 | exact floor7 | exact floor8 | exact floor9 | exact floor10 | exact floor11 | exact floor12 | exact floor13 | exact floor14

theorem certifiedDB : Certified 20 database := fun i => floorOk (receipt i).1

def s0 : List ℕ := [0x3,0x1045030cf,0x41120c333,0x1042830c3c,0x40a80c0fc0,0xaa000ff000]

def s1 : List ℕ := [0x51570f3ff,0x1045030cf,0x41120c333,0x1042830c3c,0x40a80c0fc0,0xaa000ff000]

def s2 : List ℕ := [0x1045030cc,0x1045030cf,0x41120c333,0x1042830c3c,0x40a80c0fc0,0xaa000ff000]

def s3 : List ℕ := [0x41120c330,0x1045030cf,0x41120c333,0x1042830c3c,0x40a80c0fc0,0xaa000ff000]

def s4 : List ℕ := [0xc,0x1045030cf,0x1042830c3c,0x41120c333,0x40a80c0fc0,0xaa000ff000]

def s5 : List ℕ := [0x1146d33cff,0x1045030cf,0x1042830c3c,0x41120c333,0x40a80c0fc0,0xaa000ff000]

def s6 : List ℕ := [0x1045030c3,0x1045030cf,0x1042830c3c,0x41120c333,0x40a80c0fc0,0xaa000ff000]

def s7 : List ℕ := [0x1042830c30,0x1045030cf,0x1042830c3c,0x41120c333,0x40a80c0fc0,0xaa000ff000]

def s8 : List ℕ := [0xc0,0x1045030cf,0x40a80c0fc0,0x41120c333,0x1042830c3c,0xaa000ff000]

def s9 : List ℕ := [0x41ac5c3fcf,0x1045030cf,0x40a80c0fc0,0x41120c333,0x1042830c3c,0xaa000ff000]

def s10 : List ℕ := [0x10450300f,0x1045030cf,0x40a80c0fc0,0x41120c333,0x1042830c3c,0xaa000ff000]

def s11 : List ℕ := [0x40a80c0f00,0x1045030cf,0x40a80c0fc0,0x41120c333,0x1042830c3c,0xaa000ff000]

def s12 : List ℕ := [0x3000,0x1045030cf,0xaa000ff000,0x41120c333,0x1042830c3c,0x40a80c0fc0]

def s13 : List ℕ := [0xab045ff0cf,0x1045030cf,0xaa000ff000,0x41120c333,0x1042830c3c,0x40a80c0fc0]

def s14 : List ℕ := [0x1045000cf,0x1045030cf,0xaa000ff000,0x41120c333,0x1042830c3c,0x40a80c0fc0]

def s15 : List ℕ := [0xaa000fc000,0x1045030cf,0xaa000ff000,0x41120c333,0x1042830c3c,0x40a80c0fc0]

def s16 : List ℕ := [0x30,0x41120c333,0x1042830c3c,0x1045030cf,0x40a80c0fc0,0xaa000ff000]

def s17 : List ℕ := [0x1453a3cf3f,0x41120c333,0x1042830c3c,0x1045030cf,0x40a80c0fc0,0xaa000ff000]

def s18 : List ℕ := [0x41120c303,0x41120c333,0x1042830c3c,0x1045030cf,0x40a80c0fc0,0xaa000ff000]

def s19 : List ℕ := [0x1042830c0c,0x41120c333,0x1042830c3c,0x1045030cf,0x40a80c0fc0,0xaa000ff000]

def s20 : List ℕ := [0x300,0x41120c333,0x40a80c0fc0,0x1045030cf,0x1042830c3c,0xaa000ff000]

def s21 : List ℕ := [0x44b92ccff3,0x41120c333,0x40a80c0fc0,0x1045030cf,0x1042830c3c,0xaa000ff000]

def s22 : List ℕ := [0x41120c033,0x41120c333,0x40a80c0fc0,0x1045030cf,0x1042830c3c,0xaa000ff000]

def s23 : List ℕ := [0x40a80c0cc0,0x41120c333,0x40a80c0fc0,0x1045030cf,0x1042830c3c,0xaa000ff000]

def s24 : List ℕ := [0xc000,0x41120c333,0xaa000ff000,0x1045030cf,0x1042830c3c,0x40a80c0fc0]

def s25 : List ℕ := [0xae112ff333,0x41120c333,0xaa000ff000,0x1045030cf,0x1042830c3c,0x40a80c0fc0]

def s26 : List ℕ := [0x411200333,0x41120c333,0xaa000ff000,0x1045030cf,0x1042830c3c,0x40a80c0fc0]

def s27 : List ℕ := [0xaa000f3000,0x41120c333,0xaa000ff000,0x1045030cf,0x1042830c3c,0x40a80c0fc0]

def s28 : List ℕ := [0xc00,0x1042830c3c,0x40a80c0fc0,0x1045030cf,0x41120c333,0xaa000ff000]

def s29 : List ℕ := [0x50ea8f0ffc,0x1042830c3c,0x40a80c0fc0,0x1045030cf,0x41120c333,0xaa000ff000]

def s30 : List ℕ := [0x104283003c,0x1042830c3c,0x40a80c0fc0,0x1045030cf,0x41120c333,0xaa000ff000]

def s31 : List ℕ := [0x40a80c03c0,0x1042830c3c,0x40a80c0fc0,0x1045030cf,0x41120c333,0xaa000ff000]

def s32 : List ℕ := [0x30000,0x1042830c3c,0xaa000ff000,0x1045030cf,0x41120c333,0x40a80c0fc0]

def s33 : List ℕ := [0xba428ffc3c,0x1042830c3c,0xaa000ff000,0x1045030cf,0x41120c333,0x40a80c0fc0]

def s34 : List ℕ := [0x1042800c3c,0x1042830c3c,0xaa000ff000,0x1045030cf,0x41120c333,0x40a80c0fc0]

def s35 : List ℕ := [0xaa000cf000,0x1042830c3c,0xaa000ff000,0x1045030cf,0x41120c333,0x40a80c0fc0]

def s36 : List ℕ := [0xc0000,0x40a80c0fc0,0xaa000ff000,0x1045030cf,0x41120c333,0x1042830c3c]

def s37 : List ℕ := [0xeaa80fffc0,0x40a80c0fc0,0xaa000ff000,0x1045030cf,0x41120c333,0x1042830c3c]

def s38 : List ℕ := [0x40a8000fc0,0x40a80c0fc0,0xaa000ff000,0x1045030cf,0x41120c333,0x1042830c3c]

def s39 : List ℕ := [0xaa0003f000,0x40a80c0fc0,0xaa000ff000,0x1045030cf,0x41120c333,0x1042830c3c]

def t0 : List ℕ := [0x3c,0x1042830c3c,0x1045030cf,0x41120c333,0x40a80c0fc0,0xaa000ff000]

def t1 : List ℕ := [0x3c,0x51570f3ff,0x1042830c3c,0x1045030cf,0x41120c333,0x40a80c0fc0,0xaa000ff000]

def t2 : List ℕ := [0x1557f3ffff,0x1042830c3c,0x1045030cf,0x41120c333,0x40a80c0fc0,0xaa000ff000]

def t3 : List ℕ := [0x1557f3ffff,0x51570f3ff,0x1042830c3c,0x1045030cf,0x41120c333,0x40a80c0fc0,0xaa000ff000]

def t4 : List ℕ := [0x51570f3c3,0x1042830c3c,0x1045030cf,0x41120c333,0x40a80c0fc0,0xaa000ff000]

def t5 : List ℕ := [0x51570f3c3,0x51570f3ff,0x1042830c3c,0x1045030cf,0x41120c333,0x40a80c0fc0,0xaa000ff000]

def t6 : List ℕ := [0x1042830c00,0x1042830c3c,0x1045030cf,0x41120c333,0x40a80c0fc0,0xaa000ff000]

def t7 : List ℕ := [0x1042830c00,0x51570f3ff,0x1042830c3c,0x1045030cf,0x41120c333,0x40a80c0fc0,0xaa000ff000]

def t8 : List ℕ := [0x3c0,0x40a80c0fc0,0x1045030cf,0x41120c333,0x1042830c3c,0xaa000ff000]

def t9 : List ℕ := [0x3c0,0x51570f3ff,0x40a80c0fc0,0x1045030cf,0x41120c333,0x1042830c3c,0xaa000ff000]

def t10 : List ℕ := [0x45bd7cffff,0x40a80c0fc0,0x1045030cf,0x41120c333,0x1042830c3c,0xaa000ff000]

def t11 : List ℕ := [0x45bd7cffff,0x51570f3ff,0x40a80c0fc0,0x1045030cf,0x41120c333,0x1042830c3c,0xaa000ff000]

def t12 : List ℕ := [0x51570f03f,0x40a80c0fc0,0x1045030cf,0x41120c333,0x1042830c3c,0xaa000ff000]

def t13 : List ℕ := [0x51570f03f,0x51570f3ff,0x40a80c0fc0,0x1045030cf,0x41120c333,0x1042830c3c,0xaa000ff000]

def t14 : List ℕ := [0x40a80c0c00,0x40a80c0fc0,0x1045030cf,0x41120c333,0x1042830c3c,0xaa000ff000]

def t15 : List ℕ := [0x40a80c0c00,0x51570f3ff,0x40a80c0fc0,0x1045030cf,0x41120c333,0x1042830c3c,0xaa000ff000]

def t16 : List ℕ := [0xf000,0xaa000ff000,0x1045030cf,0x41120c333,0x1042830c3c,0x40a80c0fc0]

def t17 : List ℕ := [0xf000,0x51570f3ff,0xaa000ff000,0x1045030cf,0x41120c333,0x1042830c3c,0x40a80c0fc0]

def t18 : List ℕ := [0xaf157ff3ff,0xaa000ff000,0x1045030cf,0x41120c333,0x1042830c3c,0x40a80c0fc0]

def t19 : List ℕ := [0xaf157ff3ff,0x51570f3ff,0xaa000ff000,0x1045030cf,0x41120c333,0x1042830c3c,0x40a80c0fc0]

def t20 : List ℕ := [0x5157003ff,0xaa000ff000,0x1045030cf,0x41120c333,0x1042830c3c,0x40a80c0fc0]

def t21 : List ℕ := [0x5157003ff,0x51570f3ff,0xaa000ff000,0x1045030cf,0x41120c333,0x1042830c3c,0x40a80c0fc0]

def t22 : List ℕ := [0xaa000f0000,0xaa000ff000,0x1045030cf,0x41120c333,0x1042830c3c,0x40a80c0fc0]

def t23 : List ℕ := [0xaa000f0000,0x51570f3ff,0xaa000ff000,0x1045030cf,0x41120c333,0x1042830c3c,0x40a80c0fc0]

def t24 : List ℕ := [0x41120c330,0x1045030cf,0x41120c333,0x1042830c3c,0x40a80c0fc0,0xaa000ff000]

def t25 : List ℕ := [0x41120c330,0x51570f3ff,0x41120c333,0x1042830c3c,0x40a80c0fc0,0xaa000ff000]

def t26 : List ℕ := [0x41120c330,0x1045030cf,0x51570f3ff,0x41120c333,0x1042830c3c,0x40a80c0fc0,0xaa000ff000]

def t27 : List ℕ := [0x3,0x51570f3ff,0x1042830c3c,0x40a80c0fc0,0xaa000ff000]

def t28 : List ℕ := [0x3,0x1045030cf,0x51570f3ff,0x1042830c3c,0x40a80c0fc0,0xaa000ff000]

def t29 : List ℕ := [0x3,0x41120c333,0x51570f3ff,0x1042830c3c,0x40a80c0fc0,0xaa000ff000]

def t30 : List ℕ := [0x3,0x1045030cf,0x41120c333,0x51570f3ff,0x1042830c3c,0x40a80c0fc0,0xaa000ff000]

def t31 : List ℕ := [0x1045030cc,0x1045030cf,0x51570f3ff,0x1042830c3c,0x40a80c0fc0,0xaa000ff000]

def t32 : List ℕ := [0x1045030cc,0x1045030cf,0x41120c333,0x51570f3ff,0x1042830c3c,0x40a80c0fc0,0xaa000ff000]

def t33 : List ℕ := [0x41120c330,0x41120c333,0x51570f3ff,0x1042830c3c,0x40a80c0fc0,0xaa000ff000]

def t34 : List ℕ := [0x41120c330,0x1045030cf,0x41120c333,0x51570f3ff,0x1042830c3c,0x40a80c0fc0,0xaa000ff000]

def t35 : List ℕ := [0xc,0x1045030cf,0x1042830c3c,0x51570f3ff,0x41120c333,0x40a80c0fc0,0xaa000ff000]

def t36 : List ℕ := [0x1146d33cff,0x1042830c3c,0x51570f3ff,0x41120c333,0x40a80c0fc0,0xaa000ff000]

def t37 : List ℕ := [0x1146d33cff,0x1045030cf,0x1042830c3c,0x51570f3ff,0x41120c333,0x40a80c0fc0,0xaa000ff000]

def t38 : List ℕ := [0x1045030c3,0x1042830c3c,0x51570f3ff,0x41120c333,0x40a80c0fc0,0xaa000ff000]

def t39 : List ℕ := [0x1045030c3,0x1045030cf,0x1042830c3c,0x51570f3ff,0x41120c333,0x40a80c0fc0,0xaa000ff000]

def t40 : List ℕ := [0x1042830c30,0x1045030cf,0x1042830c3c,0x51570f3ff,0x41120c333,0x40a80c0fc0,0xaa000ff000]

def t41 : List ℕ := [0xc0,0x1045030cf,0x40a80c0fc0,0x51570f3ff,0x41120c333,0x1042830c3c,0xaa000ff000]

def t42 : List ℕ := [0x41ac5c3fcf,0x40a80c0fc0,0x51570f3ff,0x41120c333,0x1042830c3c,0xaa000ff000]

def t43 : List ℕ := [0x41ac5c3fcf,0x1045030cf,0x40a80c0fc0,0x51570f3ff,0x41120c333,0x1042830c3c,0xaa000ff000]

def t44 : List ℕ := [0x10450300f,0x40a80c0fc0,0x51570f3ff,0x41120c333,0x1042830c3c,0xaa000ff000]

def t45 : List ℕ := [0x10450300f,0x1045030cf,0x40a80c0fc0,0x51570f3ff,0x41120c333,0x1042830c3c,0xaa000ff000]

def t46 : List ℕ := [0x40a80c0f00,0x1045030cf,0x40a80c0fc0,0x51570f3ff,0x41120c333,0x1042830c3c,0xaa000ff000]

def t47 : List ℕ := [0x3000,0x1045030cf,0xaa000ff000,0x51570f3ff,0x41120c333,0x1042830c3c,0x40a80c0fc0]

def t48 : List ℕ := [0xab045ff0cf,0xaa000ff000,0x51570f3ff,0x41120c333,0x1042830c3c,0x40a80c0fc0]

def t49 : List ℕ := [0xab045ff0cf,0x1045030cf,0xaa000ff000,0x51570f3ff,0x41120c333,0x1042830c3c,0x40a80c0fc0]

def t50 : List ℕ := [0x1045000cf,0xaa000ff000,0x51570f3ff,0x41120c333,0x1042830c3c,0x40a80c0fc0]

def t51 : List ℕ := [0x1045000cf,0x1045030cf,0xaa000ff000,0x51570f3ff,0x41120c333,0x1042830c3c,0x40a80c0fc0]

def t52 : List ℕ := [0xaa000fc000,0x1045030cf,0xaa000ff000,0x51570f3ff,0x41120c333,0x1042830c3c,0x40a80c0fc0]

def t53 : List ℕ := [0x1045030cc,0x41120c333,0x1045030cf,0x1042830c3c,0x40a80c0fc0,0xaa000ff000]

def t54 : List ℕ := [0x1045030cc,0x51570f3ff,0x1045030cf,0x1042830c3c,0x40a80c0fc0,0xaa000ff000]

def t55 : List ℕ := [0x1045030cc,0x41120c333,0x51570f3ff,0x1045030cf,0x1042830c3c,0x40a80c0fc0,0xaa000ff000]

def t56 : List ℕ := [0x30,0x41120c333,0x1042830c3c,0x51570f3ff,0x1045030cf,0x40a80c0fc0,0xaa000ff000]

def t57 : List ℕ := [0x1453a3cf3f,0x1042830c3c,0x51570f3ff,0x1045030cf,0x40a80c0fc0,0xaa000ff000]

def t58 : List ℕ := [0x1453a3cf3f,0x41120c333,0x1042830c3c,0x51570f3ff,0x1045030cf,0x40a80c0fc0,0xaa000ff000]

def t59 : List ℕ := [0x41120c303,0x1042830c3c,0x51570f3ff,0x1045030cf,0x40a80c0fc0,0xaa000ff000]

def t60 : List ℕ := [0x41120c303,0x41120c333,0x1042830c3c,0x51570f3ff,0x1045030cf,0x40a80c0fc0,0xaa000ff000]

def t61 : List ℕ := [0x1042830c0c,0x41120c333,0x1042830c3c,0x51570f3ff,0x1045030cf,0x40a80c0fc0,0xaa000ff000]

def t62 : List ℕ := [0x300,0x41120c333,0x40a80c0fc0,0x51570f3ff,0x1045030cf,0x1042830c3c,0xaa000ff000]

def t63 : List ℕ := [0x44b92ccff3,0x40a80c0fc0,0x51570f3ff,0x1045030cf,0x1042830c3c,0xaa000ff000]

def t64 : List ℕ := [0x44b92ccff3,0x41120c333,0x40a80c0fc0,0x51570f3ff,0x1045030cf,0x1042830c3c,0xaa000ff000]

def t65 : List ℕ := [0x41120c033,0x40a80c0fc0,0x51570f3ff,0x1045030cf,0x1042830c3c,0xaa000ff000]

def t66 : List ℕ := [0x41120c033,0x41120c333,0x40a80c0fc0,0x51570f3ff,0x1045030cf,0x1042830c3c,0xaa000ff000]

def t67 : List ℕ := [0x40a80c0cc0,0x41120c333,0x40a80c0fc0,0x51570f3ff,0x1045030cf,0x1042830c3c,0xaa000ff000]

def t68 : List ℕ := [0xc000,0x41120c333,0xaa000ff000,0x51570f3ff,0x1045030cf,0x1042830c3c,0x40a80c0fc0]

def t69 : List ℕ := [0xae112ff333,0xaa000ff000,0x51570f3ff,0x1045030cf,0x1042830c3c,0x40a80c0fc0]

def t70 : List ℕ := [0xae112ff333,0x41120c333,0xaa000ff000,0x51570f3ff,0x1045030cf,0x1042830c3c,0x40a80c0fc0]

def t71 : List ℕ := [0x411200333,0xaa000ff000,0x51570f3ff,0x1045030cf,0x1042830c3c,0x40a80c0fc0]

def t72 : List ℕ := [0x411200333,0x41120c333,0xaa000ff000,0x51570f3ff,0x1045030cf,0x1042830c3c,0x40a80c0fc0]

def t73 : List ℕ := [0xaa000f3000,0x41120c333,0xaa000ff000,0x51570f3ff,0x1045030cf,0x1042830c3c,0x40a80c0fc0]

def t74 : List ℕ := [0xc00,0x1042830c3c,0x40a80c0fc0,0x51570f3ff,0x1045030cf,0x41120c333,0xaa000ff000]

def t75 : List ℕ := [0x50ea8f0ffc,0x1042830c3c,0x40a80c0fc0,0x51570f3ff,0x1045030cf,0x41120c333,0xaa000ff000]

def t76 : List ℕ := [0x104283003c,0x1042830c3c,0x40a80c0fc0,0x51570f3ff,0x1045030cf,0x41120c333,0xaa000ff000]

def t77 : List ℕ := [0x40a80c03c0,0x1042830c3c,0x40a80c0fc0,0x51570f3ff,0x1045030cf,0x41120c333,0xaa000ff000]

def t78 : List ℕ := [0x30000,0x1042830c3c,0xaa000ff000,0x51570f3ff,0x1045030cf,0x41120c333,0x40a80c0fc0]

def t79 : List ℕ := [0xba428ffc3c,0x1042830c3c,0xaa000ff000,0x51570f3ff,0x1045030cf,0x41120c333,0x40a80c0fc0]

def t80 : List ℕ := [0x1042800c3c,0x1042830c3c,0xaa000ff000,0x51570f3ff,0x1045030cf,0x41120c333,0x40a80c0fc0]

def t81 : List ℕ := [0xaa000cf000,0x1042830c3c,0xaa000ff000,0x51570f3ff,0x1045030cf,0x41120c333,0x40a80c0fc0]

def t82 : List ℕ := [0xc0000,0x40a80c0fc0,0xaa000ff000,0x51570f3ff,0x1045030cf,0x41120c333,0x1042830c3c]

def t83 : List ℕ := [0xeaa80fffc0,0x40a80c0fc0,0xaa000ff000,0x51570f3ff,0x1045030cf,0x41120c333,0x1042830c3c]

def t84 : List ℕ := [0x40a8000fc0,0x40a80c0fc0,0xaa000ff000,0x51570f3ff,0x1045030cf,0x41120c333,0x1042830c3c]

def t85 : List ℕ := [0xaa0003f000,0x40a80c0fc0,0xaa000ff000,0x51570f3ff,0x1045030cf,0x41120c333,0x1042830c3c]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not0 : Excluded 20 7 t0 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not1 : Excluded 20 7 t1 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x0 : Block 20 6 (successors 20 6 t2) 0 3 := offMemoRows (code:=0x1401401) (gs:=[(.fork 0x405000000405404000000404403000000403401000000401402000000000000402000005 [])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x1 : Block 20 6 (successors 20 6 t2) 3 3 := offMemoRows (code:=0x1001001) (gs:=[(.fork 0x401401000000 []),(.fork 0x409000409409409409409409408000408408408408408408407000407407407407407407406401406000000406401000 []),(.fork 0x40c40900040b40800040a407401000401 [])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x2 : Block 20 6 (successors 20 6 t2) 6 3 := offMemoRows (code:=0x40d401401) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x3 : Block 20 6 (successors 20 6 t2) 9 3 := offMemoRows (code:=0x100140d) (gs:=[(.fork 0x40d00000000000041100000041100541000000041040f00000040f40e00000040e00040d []),(.fork 0x40d40d [])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x4 : Block 20 6 (successors 20 6 t2) 12 3 := offMemoRows (code:=0x40d001001) (gs:=[(.fork 0x41241241500041541541541541541541400041441441441441441441300041341341341341341341200000041240d000 []),(.fork 0x41841500041741400041641340d00040d [])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x5 : Block 20 6 (successors 20 6 t2) 15 3 := offMemoRows (code:=0x41940040d) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x6 : Block 20 6 (successors 20 6 t2) 18 3 := offMemoRows (code:=0x1400400) (gs:=[(.fork 0x42200c41d42242242240142200141e00c41f41e41e41e40141e00100000040100040140140140141a401401401401005400400000008 [(.fork 0x41c00041d41c00000040141a40140140140141b401401401000000000000 []),(.fork 0x42100041f42100000040141a401401401401420401401401000000000000 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x7 : Block 20 6 (successors 20 6 t2) 21 3 := offMemoRows (code:=0x400400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x8 : Block 20 6 (successors 20 6 t2) 24 3 := offMemoRows (code:=0x1400400) (gs:=[(.fork 0x40d00500000842900c41d42942942940d42900142600c41f42642642640d42600100000040d00040d40d40d40d42340d40d40d400400 [(.fork 0x42500041d42500000040d42340d40d40d40d42440d40d40d []),(.fork 0x42800041f42800000040d42340d40d40d40d42740d40d40d [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x9 : Block 20 6 (successors 20 6 t2) 27 3 := offMemoRows (code:=0x400400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x10 : Block 20 6 (successors 20 6 t2) 30 3 := offMemoRows (code:=0x41f42a400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x11 : Block 20 6 (successors 20 6 t2) 33 3 := offMemoRows (code:=0x42a42a42a) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x12 : Block 20 6 (successors 20 6 t2) 36 3 := offMemoRows (code:=0x42a42a42a) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x13 : Block 20 6 (successors 20 6 t2) 39 3 := offMemoRows (code:=0x42a42a42a) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x14 : Block 20 6 (successors 20 6 t2) 42 3 := offMemoRows (code:=0x42a00142a) (gs:=[(.fork 0x42e00c41d42e42e42e40142e00142c00c41942c42c42c40142c00100000040100040140140140141b40140140140100542a42a000008 [(.fork 0x42b00041d42b00000040141b40140140140141a401401401000000000000 []),(.fork 0x42d00041942d00000040141b401401401401420401401401000000000000 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x15 : Block 20 6 (successors 20 6 t2) 45 3 := offMemoRows (code:=0x42a42a42a) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x16 : Block 20 6 (successors 20 6 t2) 48 3 := offMemoRows (code:=0x42a00142a) (gs:=[(.fork 0x40d00500000843200c41d43243243240d43200143000c41943043043040d43000100000040d00040d40d40d40d42440d40d40d42a42a [(.fork 0x42f00041d42f00000040d42440d40d40d40d42340d40d40d []),(.fork 0x43100041943100000040d42440d40d40d40d42740d40d40d [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x17 : Block 20 6 (successors 20 6 t2) 51 3 := offMemoRows (code:=0x42a42a42a) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x18 : Block 20 6 (successors 20 6 t2) 54 3 := offMemoRows (code:=0x43341d433) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x19 : Block 20 6 (successors 20 6 t2) 57 3 := offMemoRows (code:=0x43342a433) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x20 : Block 20 6 (successors 20 6 t2) 60 3 := offMemoRows (code:=0x1433433) (gs:=[(.fork 0x43700c41f43743743740143700143500c419435435435401435001000000401000401401401401420401401401401005433433000008 [(.fork 0x43400041f43400000040142040140140140141a401401401000000000000 []),(.fork 0x43600041943600000040142040140140140141b401401401000000000000 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x21 : Block 20 6 (successors 20 6 t2) 63 3 := offMemoRows (code:=0x433433433) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x22 : Block 20 6 (successors 20 6 t2) 66 3 := offMemoRows (code:=0x1433433) (gs:=[(.fork 0x40d00500000843b00c41f43b43b43b40d43b00143900c41943943943940d43900100000040d00040d40d40d40d42740d40d40d433433 [(.fork 0x43800041f43800000040d42740d40d40d40d42340d40d40d []),(.fork 0x43a00041943a00000040d42740d40d40d40d42440d40d40d [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x23 : Block 20 6 (successors 20 6 t2) 69 3 := offMemoRows (code:=0x433433433) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x24 : Block 20 6 (successors 20 6 t2) 72 3 := offMemoRows (code:=0x5401433) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block2x25 : Block 20 6 (successors 20 6 t2) 75 3 := offMemoRows (code:=0x40d401) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not2 : Excluded 20 7 t2 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=3) (q:=26) (by decide) (by decide +kernel)
  intro j; fin_cases j
  · exact block2x0
  · exact block2x1
  · exact block2x2
  · exact block2x3
  · exact block2x4
  · exact block2x5
  · exact block2x6
  · exact block2x7
  · exact block2x8
  · exact block2x9
  · exact block2x10
  · exact block2x11
  · exact block2x12
  · exact block2x13
  · exact block2x14
  · exact block2x15
  · exact block2x16
  · exact block2x17
  · exact block2x18
  · exact block2x19
  · exact block2x20
  · exact block2x21
  · exact block2x22
  · exact block2x23
  · exact block2x24
  · exact block2x25

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block3x0 : Block 20 6 (successors 20 6 t3) 0 3 := offMemoRows (code:=0x16001401) (gs:=[(.fork 0x40400043c000000 [])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block3x1 : Block 20 6 (successors 20 6 t3) 3 3 := offMemoRows (code:=0x140d401) (gs:=[(.fork 0x40f00043d [])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block3x2 : Block 20 6 (successors 20 6 t3) 6 3 := offMemoRows (code:=0x40040d016) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block3x3 : Block 20 6 (successors 20 6 t3) 9 3 := offMemoRows (code:=0x400400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block3x4 : Block 20 6 (successors 20 6 t3) 12 3 := offMemoRows (code:=0x419400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block3x5 : Block 20 6 (successors 20 6 t3) 15 3 := offMemoRows (code:=0x400400419) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block3x6 : Block 20 6 (successors 20 6 t3) 18 3 := offMemoRows (code:=0x419001401) (gs:=[(.fork 0x437001000403000401401403403403 [(.fork 0x434403401403 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block3x7 : Block 20 6 (successors 20 6 t3) 21 3 := offMemoRows (code:=0x140d401) (gs:=[(.fork 0x43b00100040e00040d40d40e40e40e [(.fork 0x43840e40d40e [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block3x8 : Block 20 6 (successors 20 6 t3) 24 3 := offMemoRows (code:=0x40040d419) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block3x9 : Block 20 6 (successors 20 6 t3) 27 3 := offMemoRows (code:=0x400001419) (gs:=[(.fork 0x41d00041e41f00040040100141a41a401401 [(.fork 0x421401403403 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block3x10 : Block 20 6 (successors 20 6 t3) 30 3 := offMemoRows (code:=0x41f400001) (gs:=[(.fork 0x41d00042641f00040040d00142342340d40d [(.fork 0x42840d40e40e [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block3x11 : Block 20 6 (successors 20 6 t3) 33 3 := offMemoRows (code:=0x42a41f42a) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block3x12 : Block 20 6 (successors 20 6 t3) 36 3 := offMemoRows (code:=0x42a433433) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block3x13 : Block 20 6 (successors 20 6 t3) 39 3 := offMemoRows (code:=0x42a42a42a) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block3x14 : Block 20 6 (successors 20 6 t3) 42 3 := offMemoRows (code:=0x143342a) (gs:=[(.fork 0x41d00142e00041942c41940142e00040141b401 [(.fork 0x41942d42e43741b401420401437 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block3x15 : Block 20 6 (successors 20 6 t3) 45 3 := offMemoRows (code:=0x42a00142a) (gs:=[(.fork 0x41d00143200041943041940d43200040d42440d [(.fork 0x41943143243b42440d42740d43b [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block3x16 : Block 20 6 (successors 20 6 t3) 48 3 := offMemoRows (code:=0x41d43341d) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block3x17 : Block 20 6 (successors 20 6 t3) 51 3 := offMemoRows (code:=0x42a42a42a) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block3x18 : Block 20 6 (successors 20 6 t3) 54 3 := offMemoRows (code:=0x433001433) (gs:=[(.fork 0x41f001437000419435419401437000401420401 [(.fork 0x41943643742e42040141b401437 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block3x19 : Block 20 6 (successors 20 6 t3) 57 3 := offMemoRows (code:=0x433001) (gs:=[(.fork 0x41f00143b00041943941940d43b00040d42740d [(.fork 0x41943a43b43242740d42440d43b [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not3 : Excluded 20 7 t3 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=3) (q:=20) (by decide) (by decide +kernel)
  intro j; fin_cases j
  · exact block3x0
  · exact block3x1
  · exact block3x2
  · exact block3x3
  · exact block3x4
  · exact block3x5
  · exact block3x6
  · exact block3x7
  · exact block3x8
  · exact block3x9
  · exact block3x10
  · exact block3x11
  · exact block3x12
  · exact block3x13
  · exact block3x14
  · exact block3x15
  · exact block3x16
  · exact block3x17
  · exact block3x18
  · exact block3x19

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x0 : Block 20 6 (successors 20 6 t4) 0 3 := offMemoRows (code:=0x400400419) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x1 : Block 20 6 (successors 20 6 t4) 3 3 := offMemoRows (code:=0x143e43e) (gs:=[(.fork 0x44100044144144144144144044000044044044044044044040340340340340340343e00041943e43f00000043f [])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x2 : Block 20 6 (successors 20 6 t4) 6 3 := offMemoRows (code:=0x419419419) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x3 : Block 20 6 (successors 20 6 t4) 9 3 := offMemoRows (code:=0x44243e43e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x4 : Block 20 6 (successors 20 6 t4) 12 3 := offMemoRows (code:=0x419001442) (gs:=[(.fork 0x44200000044500044544400044444444444444444344300044344344344344344340e40e40e40e40e40e419442 [])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x5 : Block 20 6 (successors 20 6 t4) 15 3 := offMemoRows (code:=0x442419419) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x6 : Block 20 6 (successors 20 6 t4) 18 3 := offMemoRows (code:=0x400400442) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x7 : Block 20 6 (successors 20 6 t4) 21 3 := offMemoRows (code:=0x400400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x8 : Block 20 6 (successors 20 6 t4) 24 3 := offMemoRows (code:=0x400400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x9 : Block 20 6 (successors 20 6 t4) 27 3 := offMemoRows (code:=0x446446446) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x10 : Block 20 6 (successors 20 6 t4) 30 3 := offMemoRows (code:=0x446446446) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x11 : Block 20 6 (successors 20 6 t4) 33 3 := offMemoRows (code:=0x446446446) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x12 : Block 20 6 (successors 20 6 t4) 36 3 := offMemoRows (code:=0x446446446) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x13 : Block 20 6 (successors 20 6 t4) 39 3 := offMemoRows (code:=0x446446446) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x14 : Block 20 6 (successors 20 6 t4) 42 3 := offMemoRows (code:=0x446446446) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x15 : Block 20 6 (successors 20 6 t4) 45 3 := offMemoRows (code:=0x446001446) (gs:=[(.fork 0x44700044744744644644744743e44700042c42c41900042c41943e41943e43e43e44844743e005446446000000 [])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x16 : Block 20 6 (successors 20 6 t4) 48 3 := offMemoRows (code:=0x446446446) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x17 : Block 20 6 (successors 20 6 t4) 51 3 := offMemoRows (code:=0x446001446) (gs:=[(.fork 0x44200500000044900044944944644644944944244900043043041900043041944241944244244244a449446446 [])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x18 : Block 20 6 (successors 20 6 t4) 54 3 := offMemoRows (code:=0x446446446) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x19 : Block 20 6 (successors 20 6 t4) 57 3 := offMemoRows (code:=0x446446446) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x20 : Block 20 6 (successors 20 6 t4) 60 3 := offMemoRows (code:=0x44b44b446) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x21 : Block 20 6 (successors 20 6 t4) 63 3 := offMemoRows (code:=0x44b446446) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x22 : Block 20 6 (successors 20 6 t4) 66 3 := offMemoRows (code:=0x44644b44b) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x23 : Block 20 6 (successors 20 6 t4) 69 3 := offMemoRows (code:=0x44b44b44b) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x24 : Block 20 6 (successors 20 6 t4) 72 3 := offMemoRows (code:=0x44b44b001) (gs:=[(.fork 0x44c00044c44c44c44c44c44c43e44c00043543541900043541943e41943e43e43e44d44c43e00544b44b000000 [])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x25 : Block 20 6 (successors 20 6 t4) 75 3 := offMemoRows (code:=0x44b44b44b) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x26 : Block 20 6 (successors 20 6 t4) 78 3 := offMemoRows (code:=0x44b44b001) (gs:=[(.fork 0x44200500000044e00044e44e44e44e44e44e44244e00043943941900043941944241944244244244f44e44b44b [])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x27 : Block 20 6 (successors 20 6 t4) 81 3 := offMemoRows (code:=0x43e44b44b) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block4x28 : Block 20 6 (successors 20 6 t4) 84 3 := offMemoRows (code:=0x44243e005) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not4 : Excluded 20 7 t4 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=3) (q:=29) (by decide) (by decide +kernel)
  intro j; fin_cases j
  · exact block4x0
  · exact block4x1
  · exact block4x2
  · exact block4x3
  · exact block4x4
  · exact block4x5
  · exact block4x6
  · exact block4x7
  · exact block4x8
  · exact block4x9
  · exact block4x10
  · exact block4x11
  · exact block4x12
  · exact block4x13
  · exact block4x14
  · exact block4x15
  · exact block4x16
  · exact block4x17
  · exact block4x18
  · exact block4x19
  · exact block4x20
  · exact block4x21
  · exact block4x22
  · exact block4x23
  · exact block4x24
  · exact block4x25
  · exact block4x26
  · exact block4x27
  · exact block4x28

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not5 : Excluded 20 7 t5 := offAudit (g:=(.saved 25)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not6 : Excluded 20 7 t6 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not7 : Excluded 20 7 t7 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not8 : Excluded 20 7 t8 := offAudit (g:=(.saved 80)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not9 : Excluded 20 7 t9 := offAudit (g:=(.saved 80)) certifiedDB (by decide) (by decide +kernel)

def cx10 : List (ℕ × ℕ) := [(2,6),(3,7),(4,8),(5,9),(10,11),(16,18),(17,19)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not10 : Excluded 20 7 t10 := fun h => not2 (perm_feasible cx10 (by decide +kernel) (by decide +kernel) (by decide +kernel) h)

def cx11 : List (ℕ × ℕ) := [(2,6),(3,7),(4,8),(5,9),(10,11),(16,18),(17,19)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not11 : Excluded 20 7 t11 := fun h => not3 (perm_feasible cx11 (by decide +kernel) (by decide +kernel) (by decide +kernel) h)

def cx12 : List (ℕ × ℕ) := [(2,6),(3,7),(4,8),(5,9),(10,11),(16,18),(17,19)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not12 : Excluded 20 7 t12 := fun h => not4 (perm_feasible cx12 (by decide +kernel) (by decide +kernel) (by decide +kernel) h)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not13 : Excluded 20 7 t13 := offAudit (g:=(.saved 25)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not14 : Excluded 20 7 t14 := offAudit (g:=(.saved 80)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not15 : Excluded 20 7 t15 := offAudit (g:=(.saved 80)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not16 : Excluded 20 7 t16 := offAudit (g:=(.saved 153)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not17 : Excluded 20 7 t17 := offAudit (g:=(.saved 153)) certifiedDB (by decide) (by decide +kernel)

def cx18 : List (ℕ × ℕ) := [(2,12),(3,13),(4,14),(5,15),(6,12),(7,13),(8,14),(9,15),(10,17),(11,16),(16,19),(17,18)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not18 : Excluded 20 7 t18 := fun h => not2 (perm_feasible cx18 (by decide +kernel) (by decide +kernel) (by decide +kernel) h)

def cx19 : List (ℕ × ℕ) := [(2,12),(3,13),(4,14),(5,15),(6,12),(7,13),(8,14),(9,15),(10,17),(11,16),(16,19),(17,18)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not19 : Excluded 20 7 t19 := fun h => not3 (perm_feasible cx19 (by decide +kernel) (by decide +kernel) (by decide +kernel) h)

def cx20 : List (ℕ × ℕ) := [(2,12),(3,13),(4,14),(5,15),(6,12),(7,13),(8,14),(9,15),(10,17),(11,16),(16,19),(17,18)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not20 : Excluded 20 7 t20 := fun h => not4 (perm_feasible cx20 (by decide +kernel) (by decide +kernel) (by decide +kernel) h)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not21 : Excluded 20 7 t21 := offAudit (g:=(.saved 25)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not22 : Excluded 20 7 t22 := offAudit (g:=(.saved 153)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not23 : Excluded 20 7 t23 := offAudit (g:=(.saved 153)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not24 : Excluded 20 7 t24 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not25 : Excluded 20 7 t25 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not26 : Excluded 20 7 t26 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not27 : Excluded 20 7 t27 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not28 : Excluded 20 7 t28 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not29 : Excluded 20 7 t29 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not30 : Excluded 20 7 t30 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not31 : Excluded 20 7 t31 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not32 : Excluded 20 7 t32 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not33 : Excluded 20 7 t33 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not34 : Excluded 20 7 t34 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not35 : Excluded 20 7 t35 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x0 : Block 20 6 (successors 20 6 t36) 0 3 := offMemoRows (code:=0x1001469) (gs:=[(.fork 0x4050054de4de40540542c40500140540546940500100040540540540500002443c40540540540542c02446042c46902441d469000000 [(.fork 0x43c40540540540542d00046042d000000000000420405405405405 []),(.fork 0x43c40540540540546b00041d46b00000000000046a405405405405 [])]),(.fork 0x100041d40500040542c40543c40546041d469 [(.fork 0x40543c4054df41d46b4df46a405 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x1 : Block 20 6 (successors 20 6 t36) 3 3 := offMemoRows (code:=0x46941d001) (gs:=[(.fork 0x4090054e04e04094094e140900040946941d40940940940900000040a4e14e10004e14e14e04e041d00046941d [])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x2 : Block 20 6 (successors 20 6 t36) 6 3 := offMemoRows (code:=0x100149f) (gs:=[(.fork 0x49f0240000004100054e24e241041043041000141041049f41000100041041041041000002443d41041041041043002449e43041d49f [(.fork 0x43d41041041041043100049e431427410410410410 []),(.fork 0x4a100000000000000043d41041041041041d4a10000004a0410410410410 [])]),(.fork 0x100041d41000041043041043d41049e41d49f [(.fork 0x41043d4104e341d4a14e34a0410 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x3 : Block 20 6 (successors 20 6 t36) 9 3 := offMemoRows (code:=0x49f41d001) (gs:=[(.fork 0x4150054e44e44154154e541500041549f41d4154154154150000004164e54e50004e54e54e44e441d00049f41d [])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x4 : Block 20 6 (successors 20 6 t36) 12 3 := offMemoRows (code:=0x4dc4dc4dc) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x5 : Block 20 6 (successors 20 6 t36) 15 3 := offMemoRows (code:=0x400001400) (gs:=[(.fork 0x4220014de4de41d42242242246942200142242200042200102300e40042246946946900000143c41a43c41a00500002a41d4694de4de469001400400007032 [(.fork 0x0 []),(.fork 0x41c00046041c00000046740340340340300000000000040341a403403403 []),(.fork 0x43c4e64e64e64e60000004674e64e64e64e646b00041f46b000000 []),(.fork 0x43c41a43c41a003000000467420467420003000000000000 []),(.fork 0x0 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x6 : Block 20 6 (successors 20 6 t36) 18 3 := offMemoRows (code:=0x400400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x7 : Block 20 6 (successors 20 6 t36) 21 3 := offMemoRows (code:=0x400001400) (gs:=[(.fork 0x49f0010070324290014e24e241d42942942949f42900142942900042900102300e40042949f49f49f00000143d42343d42300500002a41d49f4e24e2400400 [(.fork 0x42500049e42500000049c40e40e40e40e40e42340e40e40e []),(.fork 0x4a100000000000000043d4e74e74e74e700000049c4e74e74e74e741f4a1 []),(.fork 0x43d42343d42300300000049c42749c427003 []),(.fork 0x0 []),(.fork 0x0 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x8 : Block 20 6 (successors 20 6 t36) 24 3 := offMemoRows (code:=0x400400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x9 : Block 20 6 (successors 20 6 t36) 27 3 := offMemoRows (code:=0x433433433) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x10 : Block 20 6 (successors 20 6 t36) 30 3 := offMemoRows (code:=0x433433433) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x11 : Block 20 6 (successors 20 6 t36) 33 3 := offMemoRows (code:=0x400400433) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x12 : Block 20 6 (successors 20 6 t36) 36 3 := offMemoRows (code:=0x400400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x13 : Block 20 6 (successors 20 6 t36) 39 3 := offMemoRows (code:=0x419433400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x14 : Block 20 6 (successors 20 6 t36) 42 3 := offMemoRows (code:=0x400400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x15 : Block 20 6 (successors 20 6 t36) 45 3 := offMemoRows (code:=0x1001469) (gs:=[(.fork 0x42e02442e42e40342e00146042e403005466466403403469403001000403403403403000014467403403403403469014419469000000 [(.fork 0x42b00046042b00000046740340340340300000040341a403403403000000 []),(.fork 0x46740340340340346b00041946b00000000000046a403403403403 [])]),(.fork 0x142e46000000040346740341940342e419469 [(.fork 0x46740347542e41946b47546a403 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x16 : Block 20 6 (successors 20 6 t36) 48 3 := offMemoRows (code:=0x469419001) (gs:=[(.fork 0x4e80004e84e84074e80004e84e849149140700549149140746900000041900040741940740740740c4e8469419 [])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x17 : Block 20 6 (successors 20 6 t36) 51 3 := offMemoRows (code:=0x100149f) (gs:=[(.fork 0x49f01400000043202443243240e43200149e43240e00549a49a40e40e49f40e00100040e40e40e40e00001449c40e40e40e40e41949f [(.fork 0x42f00049e42f00000049c40e40e40e40e40e42340e40e40e []),(.fork 0x4a100000000000000049c40e40e40e40e4194a10000004a040e40e40e40e [])]),(.fork 0x143249e00000040e49c40e41940e43241949f [(.fork 0x49c40e4ad4324194a14ad4a040e [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x18 : Block 20 6 (successors 20 6 t36) 54 3 := offMemoRows (code:=0x49f419001) (gs:=[(.fork 0x4e90004e94e94134e90004e94e94d64d64130054d64d641349f0000004190004134194134134134184e949f419 [])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x19 : Block 20 6 (successors 20 6 t36) 57 3 := offMemoRows (code:=0x433433433) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x20 : Block 20 6 (successors 20 6 t36) 60 3 := offMemoRows (code:=0x433433433) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x21 : Block 20 6 (successors 20 6 t36) 63 3 := offMemoRows (code:=0x43341d433) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x22 : Block 20 6 (successors 20 6 t36) 66 3 := offMemoRows (code:=0x433001433) (gs:=[(.fork 0x4a146b00146b4a14190000010014a146b41900000100146b40040043343342a43343343343340040042a42a42a42a42a42a42a4a141d0000010014a146b41d00000100146b43343342a42a42a42a42a42a42a4a141f0000010014a146b41f00000100146b [(.fork 0x43c40440440440400000046740440440440446b00041f46b000000 []),(.fork 0x42240443c40440446740441f46b []),(.fork 0x4a100000000000000043d40f40f40f40f00000049c40f40f40f40f41f4a1 []),(.fork 0x42940f43d40f40f49c40f41f4a1 []),(.fork 0x43c40540540540500000046a40540540540546b00041d46b000000 []),(.fork 0x41e40543c40546a40541e41d46b []),(.fork 0x4a100000000000000043d4104104104100000004a041041041041041d4a1 []),(.fork 0x42641043d4104a041042641d4a1 []),(.fork 0x46740340340340300000046a40340340340346b00041946b000000 []),(.fork 0x43746740346a40342e43741946b []),(.fork 0x4a100000000000000049c40e40e40e40e0000004a040e40e40e40e4194a1 []),(.fork 0x43b49c40e4a040e43243b4194a1 []),(.fork 0x4eb4ea0000000000004ea00000000000000000000000046b [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x23 : Block 20 6 (successors 20 6 t36) 69 3 := offMemoRows (code:=0x433433400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x24 : Block 20 6 (successors 20 6 t36) 72 3 := offMemoRows (code:=0x433433433) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x25 : Block 20 6 (successors 20 6 t36) 75 3 := offMemoRows (code:=0x4dc4dc4dc) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x26 : Block 20 6 (successors 20 6 t36) 78 3 := offMemoRows (code:=0x433001433) (gs:=[(.fork 0x2a41943543343341946946646643500146646643543546943500143543500043500101300e46946946900000146742046742000546900143343300701a [(.fork 0x0 []),(.fork 0x43c405405405405436000460436000000420405405405405000000 []),(.fork 0x43c47c47c47c47c00000046747c47c47c47c4ec00041f4ec000000 []),(.fork 0x43c41a43c41a003000000467420467420003000000000000 []),(.fork 0x0 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x27 : Block 20 6 (successors 20 6 t36) 81 3 := offMemoRows (code:=0x433433433) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x28 : Block 20 6 (successors 20 6 t36) 84 3 := offMemoRows (code:=0x433001433) (gs:=[(.fork 0x49f00100701a00002a41943943343341949f49a49a43900149a49a43943949f43900143943900043900101300e49f49f49f00000149c42749c427005433433 [(.fork 0x43d41041041041043a00049e43a427410410410410 []),(.fork 0x4ed00000000000000043d4b34b34b34b300000049c4b34b34b34b341f4ed []),(.fork 0x43d42343d42300300000049c42749c427003 []),(.fork 0x0 []),(.fork 0x0 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x29 : Block 20 6 (successors 20 6 t36) 87 3 := offMemoRows (code:=0x433433433) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x30 : Block 20 6 (successors 20 6 t36) 90 3 := offMemoRows (code:=0x469001469) (gs:=[(.fork 0x14eb0010014eb01a4ee4eb0160160000000010014ee032026026000000469 [(.fork 0x0 []),(.fork 0x0 []),(.fork 0x0 []),(.fork 0x0 []),(.fork 0x4eb0000000000004ef0000000000004ef46b000000000000 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block36x31 : Block 20 6 (successors 20 6 t36) 93 3 := offMemoRows (code:=0x49f) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not36 : Excluded 20 7 t36 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=3) (q:=32) (by decide) (by decide +kernel)
  intro j; fin_cases j
  · exact block36x0
  · exact block36x1
  · exact block36x2
  · exact block36x3
  · exact block36x4
  · exact block36x5
  · exact block36x6
  · exact block36x7
  · exact block36x8
  · exact block36x9
  · exact block36x10
  · exact block36x11
  · exact block36x12
  · exact block36x13
  · exact block36x14
  · exact block36x15
  · exact block36x16
  · exact block36x17
  · exact block36x18
  · exact block36x19
  · exact block36x20
  · exact block36x21
  · exact block36x22
  · exact block36x23
  · exact block36x24
  · exact block36x25
  · exact block36x26
  · exact block36x27
  · exact block36x28
  · exact block36x29
  · exact block36x30
  · exact block36x31

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not37 : Excluded 20 7 t37 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not38 : Excluded 20 7 t38 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not39 : Excluded 20 7 t39 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not40 : Excluded 20 7 t40 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not41 : Excluded 20 7 t41 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

def cx42 : List (ℕ × ℕ) := [(2,6),(3,7),(4,8),(5,9),(10,11),(16,18),(17,19)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not42 : Excluded 20 7 t42 := fun h => not36 (perm_feasible cx42 (by decide +kernel) (by decide +kernel) (by decide +kernel) h)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not43 : Excluded 20 7 t43 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not44 : Excluded 20 7 t44 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not45 : Excluded 20 7 t45 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not46 : Excluded 20 7 t46 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not47 : Excluded 20 7 t47 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

def cx48 : List (ℕ × ℕ) := [(2,12),(3,13),(4,14),(5,15),(6,12),(7,13),(8,14),(9,15),(10,17),(11,16),(16,19),(17,18)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not48 : Excluded 20 7 t48 := fun h => not36 (perm_feasible cx48 (by decide +kernel) (by decide +kernel) (by decide +kernel) h)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not49 : Excluded 20 7 t49 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not50 : Excluded 20 7 t50 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not51 : Excluded 20 7 t51 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not52 : Excluded 20 7 t52 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not53 : Excluded 20 7 t53 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not54 : Excluded 20 7 t54 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not55 : Excluded 20 7 t55 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not56 : Excluded 20 7 t56 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

def cx57 : List (ℕ × ℕ) := [(0,1),(2,4),(3,5),(6,8),(7,9),(12,14),(13,15)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not57 : Excluded 20 7 t57 := fun h => not36 (perm_feasible cx57 (by decide +kernel) (by decide +kernel) (by decide +kernel) h)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not58 : Excluded 20 7 t58 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not59 : Excluded 20 7 t59 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not60 : Excluded 20 7 t60 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not61 : Excluded 20 7 t61 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not62 : Excluded 20 7 t62 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

def cx63 : List (ℕ × ℕ) := [(0,1),(2,8),(3,9),(4,6),(5,7),(10,11),(12,14),(13,15),(16,18),(17,19)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not63 : Excluded 20 7 t63 := fun h => not36 (perm_feasible cx63 (by decide +kernel) (by decide +kernel) (by decide +kernel) h)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not64 : Excluded 20 7 t64 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not65 : Excluded 20 7 t65 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not66 : Excluded 20 7 t66 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not67 : Excluded 20 7 t67 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not68 : Excluded 20 7 t68 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

def cx69 : List (ℕ × ℕ) := [(0,1),(2,14),(3,15),(4,12),(5,13),(6,12),(7,13),(8,14),(9,15),(10,17),(11,16),(12,14),(13,15),(16,19),(17,18)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not69 : Excluded 20 7 t69 := fun h => not36 (perm_feasible cx69 (by decide +kernel) (by decide +kernel) (by decide +kernel) h)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not70 : Excluded 20 7 t70 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not71 : Excluded 20 7 t71 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not72 : Excluded 20 7 t72 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not73 : Excluded 20 7 t73 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not74 : Excluded 20 7 t74 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x0 : Block 20 6 (successors 20 6 t75) 0 3 := offMemoRows (code:=0x3203250d) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x1 : Block 20 6 (successors 20 6 t75) 3 3 := offMemoRows (code:=0x45040050d) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x2 : Block 20 6 (successors 20 6 t75) 6 3 := offMemoRows (code:=0x400400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x3 : Block 20 6 (successors 20 6 t75) 9 3 := offMemoRows (code:=0x1450400) (gs:=[(.fork 0x102600102a53c00102600102a50000800000050d00e00000000150050d500 [(.fork 0x53b0000000000000000000000000005004ee4ee []),(.fork 0x0 []),(.fork 0x0 []),(.fork 0x0 []),(.fork 0x0 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x4 : Block 20 6 (successors 20 6 t75) 12 3 := offMemoRows (code:=0x400400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x5 : Block 20 6 (successors 20 6 t75) 15 3 := offMemoRows (code:=0x5450001) (gs:=[(.fork 0x102600102a53e00102600102a4ee00800000050d00e0000000014ee50d4ee [(.fork 0x53d0000000000000000000000000004ee5004ee []),(.fork 0x0 []),(.fork 0x0 []),(.fork 0x0 []),(.fork 0x0 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x6 : Block 20 6 (successors 20 6 t75) 18 3 := offMemoRows (code:=0x143c41a) (gs:=[(.fork 0x51c00000051c4e60000004e640100000040140300000040353f00000000000053f000005 [])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x7 : Block 20 6 (successors 20 6 t75) 21 3 := offMemoRows (code:=0x1a001001) (gs:=[(.fork 0x4e600043c000000 []),(.fork 0x40300041a000000 [])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x8 : Block 20 6 (successors 20 6 t75) 24 3 := offMemoRows (code:=0x800141a) (gs:=[(.fork 0x407000000000 [])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x9 : Block 20 6 (successors 20 6 t75) 27 3 := offMemoRows (code:=0x40043c001) (gs:=[(.fork 0x540000000 [])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x10 : Block 20 6 (successors 20 6 t75) 30 3 := offMemoRows (code:=0x400001001) (gs:=[(.fork 0x51501451551540151500141d5154df0144df4df4014df00141f4df40100540040000000c00000040100040140140140141a401401401 [(.fork 0x54100041d54100000000000040141a40140140140141b401401401000000 []),(.fork 0x54200041f54200000000000040141a401401401401420401401401000000 [])]),(.fork 0x41d4df00041f40100141a41a400401401 [(.fork 0x542401403403 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x11 : Block 20 6 (successors 20 6 t75) 33 3 := offMemoRows (code:=0x400400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x12 : Block 20 6 (successors 20 6 t75) 36 3 := offMemoRows (code:=0x1450400) (gs:=[(.fork 0x52a01452a52a40352a00146052a4fd0144fd4fd4034fd0014624fd40300545040300040340340340300000c00000040341a403403403 [(.fork 0x54300046054300000000000040341a403403403000000467403403403403 []),(.fork 0x54400046254400000000000040341a40340340300000046a403403403403 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x13 : Block 20 6 (successors 20 6 t75) 39 3 := offMemoRows (code:=0x450450001) (gs:=[(.fork 0x4604fd00046240340300141a41a450403 [(.fork 0x544403401403 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x14 : Block 20 6 (successors 20 6 t75) 42 3 := offMemoRows (code:=0x450450450) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x15 : Block 20 6 (successors 20 6 t75) 45 3 := offMemoRows (code:=0xe00e50d) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x16 : Block 20 6 (successors 20 6 t75) 48 3 := offMemoRows (code:=0x14de50d) (gs:=[(.fork 0x51c0054de4de51c51c46951c00151c51c42c51c00100051c51c51c51c00002443c51c51c51c51c46902441d46942c02446042c000000 [(.fork 0x43c51c51c51c51c46b00041d46b00000000000046a51c51c51c51c []),(.fork 0x43c51c51c51c51c42d00046042d00000000000042051c51c51c51c [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x17 : Block 20 6 (successors 20 6 t75) 51 3 := offMemoRows (code:=0x4de0014de) (gs:=[(.fork 0x51c00151c43c43c51c41d42c4604de [(.fork 0x51c4e642d4e6 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x18 : Block 20 6 (successors 20 6 t75) 54 3 := offMemoRows (code:=0x4de4de4de) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x19 : Block 20 6 (successors 20 6 t75) 57 3 := offMemoRows (code:=0x4004de001) (gs:=[(.fork 0x5150014de4de51551546951500151551500051500141d51502301a46946946900000143c41a43c41a00740051546900140040000b03200002a41d4694de4de [(.fork 0x0 []),(.fork 0x54100046054100000000000046740340340340300000040341a403403403 []),(.fork 0x43c4e64e64e64e646b00041f46b0000004674e64e64e64e6000000 []),(.fork 0x43c41a43c41a003000000000000467420467420003000000 []),(.fork 0x0 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x20 : Block 20 6 (successors 20 6 t75) 60 3 := offMemoRows (code:=0x14de4de) (gs:=[(.fork 0x52a0014de4de52a52a42c52a00152a52a00052a00146052a02301a42c42c42c00000143c41a43c41a00745052a42c00145042c46042c00b03200002a4de4de [(.fork 0x0 []),(.fork 0x54300041d54300000000000000000040141a40140140140141b401401401 []),(.fork 0x43c4e64e64e64e642d00046242d00000041b4e64e64e64e6000000 []),(.fork 0x43c41a43c41a00300000000000000000046a41b46a41b003 []),(.fork 0x0 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x21 : Block 20 6 (successors 20 6 t75) 63 3 := offMemoRows (code:=0x4de4504de) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x22 : Block 20 6 (successors 20 6 t75) 66 3 := offMemoRows (code:=0x5144de4de) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x23 : Block 20 6 (successors 20 6 t75) 69 3 := offMemoRows (code:=0x4de4de4de) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x24 : Block 20 6 (successors 20 6 t75) 72 3 := offMemoRows (code:=0x15144de) (gs:=[(.fork 0x100153500800153501601600000050d53500102a43000102a50d032000000 [(.fork 0x0 []),(.fork 0x0 []),(.fork 0x53550e00000043100000000000000000050e []),(.fork 0x0 []),(.fork 0x0 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x25 : Block 20 6 (successors 20 6 t75) 75 3 := offMemoRows (code:=0x15144de) (gs:=[(.fork 0x4e60055144e64e64e64734e60014e64e64354e60010004e64e64e64e600002443c4e64e64e64e647302441f473435024462435000000 [(.fork 0x43c4e64e64e64e647400041f4740000000000004674e64e64e64e6 []),(.fork 0x43c4e64e64e64e643600046243600000000000041b4e64e64e64e6 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x26 : Block 20 6 (successors 20 6 t75) 78 3 := offMemoRows (code:=0x514001514) (gs:=[(.fork 0x4e60014e643c43c4e641f435462514 [(.fork 0x4e651c4364e6 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x27 : Block 20 6 (successors 20 6 t75) 81 3 := offMemoRows (code:=0x514514514) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x28 : Block 20 6 (successors 20 6 t75) 84 3 := offMemoRows (code:=0x400514001) (gs:=[(.fork 0x4df0015144df4df4df4734df0014df4df0004df00141f4df02301a47347347300000143c41a43c41a0074004df47300140040000b03200002a41f473514514 [(.fork 0x0 []),(.fork 0x54200046254200000000000046a40340340340300000040341a403403403 []),(.fork 0x43c51c51c51c51c47400041d47400000046a51c51c51c51c000000 []),(.fork 0x43c41a43c41a00300000000000046a41b46a41b003000000 []),(.fork 0x0 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x29 : Block 20 6 (successors 20 6 t75) 87 3 := offMemoRows (code:=0x1514514) (gs:=[(.fork 0x4fd0015144fd4fd4fd4354fd0014fd4fd0004fd0014624fd02301a43543543500000143c41a43c41a0074504fd43500145043546243500b03200002a514514 [(.fork 0x0 []),(.fork 0x54400041f54400000000000000000040141a401401401401420401401401 []),(.fork 0x43c51c51c51c51c43600046043600000042051c51c51c51c000000 []),(.fork 0x43c41a43c41a003000000000000000000467420467420003 []),(.fork 0x0 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x30 : Block 20 6 (successors 20 6 t75) 90 3 := offMemoRows (code:=0x514450514) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x31 : Block 20 6 (successors 20 6 t75) 93 3 := offMemoRows (code:=0x4de4de514) (gs:=[]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem block75x32 : Block 20 6 (successors 20 6 t75) 96 3 := offMemoRows (code:=0x514001) (gs:=[(.fork 0x100150e00800150e01601600000050d50e00102a43900102a50d032000000 [(.fork 0x0 []),(.fork 0x0 []),(.fork 0x50e53500000043a00000000000000000050e []),(.fork 0x0 []),(.fork 0x0 [])])]) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not75 : Excluded 20 7 t75 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=3) (q:=33) (by decide) (by decide +kernel)
  intro j; fin_cases j
  · exact block75x0
  · exact block75x1
  · exact block75x2
  · exact block75x3
  · exact block75x4
  · exact block75x5
  · exact block75x6
  · exact block75x7
  · exact block75x8
  · exact block75x9
  · exact block75x10
  · exact block75x11
  · exact block75x12
  · exact block75x13
  · exact block75x14
  · exact block75x15
  · exact block75x16
  · exact block75x17
  · exact block75x18
  · exact block75x19
  · exact block75x20
  · exact block75x21
  · exact block75x22
  · exact block75x23
  · exact block75x24
  · exact block75x25
  · exact block75x26
  · exact block75x27
  · exact block75x28
  · exact block75x29
  · exact block75x30
  · exact block75x31
  · exact block75x32

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not76 : Excluded 20 7 t76 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not77 : Excluded 20 7 t77 := offAudit (g:=(.saved 80)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not78 : Excluded 20 7 t78 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)

def cx79 : List (ℕ × ℕ) := [(6,12),(7,13),(8,14),(9,15),(10,16),(11,17),(18,19)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not79 : Excluded 20 7 t79 := fun h => not75 (perm_feasible cx79 (by decide +kernel) (by decide +kernel) (by decide +kernel) h)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not80 : Excluded 20 7 t80 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not81 : Excluded 20 7 t81 := offAudit (g:=(.saved 153)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not82 : Excluded 20 7 t82 := offAudit (g:=(.saved 80)) certifiedDB (by decide) (by decide +kernel)

def cx83 : List (ℕ × ℕ) := [(2,6),(3,7),(4,8),(5,9),(6,12),(7,13),(8,14),(9,15),(10,18),(11,19),(16,19),(17,18)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not83 : Excluded 20 7 t83 := fun h => not75 (perm_feasible cx83 (by decide +kernel) (by decide +kernel) (by decide +kernel) h)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not84 : Excluded 20 7 t84 := offAudit (g:=(.saved 80)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem not85 : Excluded 20 7 t85 := offAudit (g:=(.saved 153)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem secondLayer : successors 20 7 s1 = [t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28,t29,t30,t31,t32,t33,t34,t35,t36,t37,t38,t39,t40,t41,t42,t43,t44,t45,t46,t47,t48,t49,t50,t51,t52,t53,t54,t55,t56,t57,t58,t59,t60,t61,t62,t63,t64,t65,t66,t67,t68,t69,t70,t71,t72,t73,t74,t75,t76,t77,t78,t79,t80,t81,t82,t83,t84,t85] := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos1 : Excluded 20 8 s1 := by
  apply join_exclusions (by decide +kernel)
  intro v hv
  rw [secondLayer] at hv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact not0
  · exact not1
  · exact not2
  · exact not3
  · exact not4
  · exact not5
  · exact not6
  · exact not7
  · exact not8
  · exact not9
  · exact not10
  · exact not11
  · exact not12
  · exact not13
  · exact not14
  · exact not15
  · exact not16
  · exact not17
  · exact not18
  · exact not19
  · exact not20
  · exact not21
  · exact not22
  · exact not23
  · exact not24
  · exact not25
  · exact not26
  · exact not27
  · exact not28
  · exact not29
  · exact not30
  · exact not31
  · exact not32
  · exact not33
  · exact not34
  · exact not35
  · exact not36
  · exact not37
  · exact not38
  · exact not39
  · exact not40
  · exact not41
  · exact not42
  · exact not43
  · exact not44
  · exact not45
  · exact not46
  · exact not47
  · exact not48
  · exact not49
  · exact not50
  · exact not51
  · exact not52
  · exact not53
  · exact not54
  · exact not55
  · exact not56
  · exact not57
  · exact not58
  · exact not59
  · exact not60
  · exact not61
  · exact not62
  · exact not63
  · exact not64
  · exact not65
  · exact not66
  · exact not67
  · exact not68
  · exact not69
  · exact not70
  · exact not71
  · exact not72
  · exact not73
  · exact not74
  · exact not75
  · exact not76
  · exact not77
  · exact not78
  · exact not79
  · exact not80
  · exact not81
  · exact not82
  · exact not83
  · exact not84
  · exact not85

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos0 : Excluded 20 8 s0 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos2 : Excluded 20 8 s2 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos3 : Excluded 20 8 s3 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos4 : Excluded 20 8 s4 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

def swaps5 : List (ℕ × ℕ) := [(0,2),(1,3),(4,5),(8,10),(9,11),(14,16),(15,17)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos5 : Excluded 20 8 s5 := fun h => nos1 (perm_feasible swaps5 (by decide +kernel) (by decide +kernel) (by decide +kernel) h)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos6 : Excluded 20 8 s6 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos7 : Excluded 20 8 s7 := offAudit (g:=(.saved 345)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos8 : Excluded 20 8 s8 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

def swaps9 : List (ℕ × ℕ) := [(0,6),(1,7),(2,6),(3,7),(4,9),(5,8),(8,11),(9,10),(14,18),(15,19),(16,18),(17,19)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos9 : Excluded 20 8 s9 := fun h => nos1 (perm_feasible swaps9 (by decide +kernel) (by decide +kernel) (by decide +kernel) h)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos10 : Excluded 20 8 s10 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos11 : Excluded 20 8 s11 := offAudit (g:=(.saved 346)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos12 : Excluded 20 8 s12 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

def swaps13 : List (ℕ × ℕ) := [(0,12),(1,13),(2,12),(3,13),(4,15),(5,14),(6,12),(7,13),(8,17),(9,16),(10,15),(11,14),(14,19),(15,18),(16,17)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos13 : Excluded 20 8 s13 := fun h => nos1 (perm_feasible swaps13 (by decide +kernel) (by decide +kernel) (by decide +kernel) h)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos14 : Excluded 20 8 s14 := offAudit (g:=(.saved 220)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos15 : Excluded 20 8 s15 := offAudit (g:=(.saved 347)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos16 : Excluded 20 8 s16 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

def swaps17 : List (ℕ × ℕ) := [(0,4),(1,5),(2,5),(3,4),(6,8),(7,9),(8,10),(9,11),(12,14),(13,15),(14,16),(15,17)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos17 : Excluded 20 8 s17 := fun h => nos1 (perm_feasible swaps17 (by decide +kernel) (by decide +kernel) (by decide +kernel) h)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos18 : Excluded 20 8 s18 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos19 : Excluded 20 8 s19 := offAudit (g:=(.saved 345)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos20 : Excluded 20 8 s20 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

def swaps21 : List (ℕ × ℕ) := [(0,8),(1,9),(2,9),(3,8),(4,7),(5,6),(6,7),(8,11),(9,10),(12,14),(13,15),(14,18),(15,19),(16,18),(17,19)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos21 : Excluded 20 8 s21 := fun h => nos1 (perm_feasible swaps21 (by decide +kernel) (by decide +kernel) (by decide +kernel) h)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos22 : Excluded 20 8 s22 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos23 : Excluded 20 8 s23 := offAudit (g:=(.saved 346)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos24 : Excluded 20 8 s24 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

def swaps25 : List (ℕ × ℕ) := [(0,14),(1,15),(2,15),(3,14),(4,13),(5,12),(6,13),(7,12),(8,17),(9,16),(10,15),(11,14),(12,17),(13,16),(14,19),(15,18)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos25 : Excluded 20 8 s25 := fun h => nos1 (perm_feasible swaps25 (by decide +kernel) (by decide +kernel) (by decide +kernel) h)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos26 : Excluded 20 8 s26 := offAudit (g:=(.saved 221)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos27 : Excluded 20 8 s27 := offAudit (g:=(.saved 347)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos28 : Excluded 20 8 s28 := offAudit (g:=(.saved 345)) certifiedDB (by decide) (by decide +kernel)

def swaps29 : List (ℕ × ℕ) := [(0,10),(1,11),(2,3),(4,7),(5,6),(8,9),(12,16),(13,17),(14,18),(15,19)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos29 : Excluded 20 8 s29 := fun h => nos1 (perm_feasible swaps29 (by decide +kernel) (by decide +kernel) (by decide +kernel) h)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos30 : Excluded 20 8 s30 := offAudit (g:=(.saved 345)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos31 : Excluded 20 8 s31 := offAudit (g:=(.saved 346)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos32 : Excluded 20 8 s32 := offAudit (g:=(.saved 345)) certifiedDB (by decide) (by decide +kernel)

def swaps33 : List (ℕ × ℕ) := [(0,16),(1,17),(2,3),(4,13),(5,12),(6,12),(7,13),(8,15),(9,14),(10,16),(11,17),(12,16),(13,17),(14,19),(15,18)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos33 : Excluded 20 8 s33 := fun h => nos1 (perm_feasible swaps33 (by decide +kernel) (by decide +kernel) (by decide +kernel) h)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos34 : Excluded 20 8 s34 := offAudit (g:=(.saved 345)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos35 : Excluded 20 8 s35 := offAudit (g:=(.saved 347)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos36 : Excluded 20 8 s36 := offAudit (g:=(.saved 346)) certifiedDB (by decide) (by decide +kernel)

def swaps37 : List (ℕ × ℕ) := [(0,18),(1,19),(2,7),(3,6),(4,13),(5,12),(6,9),(7,8),(8,15),(9,14),(10,18),(11,19),(12,19),(13,18),(14,17),(15,16)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos37 : Excluded 20 8 s37 := fun h => nos1 (perm_feasible swaps37 (by decide +kernel) (by decide +kernel) (by decide +kernel) h)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos38 : Excluded 20 8 s38 := offAudit (g:=(.saved 346)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem nos39 : Excluded 20 8 s39 := offAudit (g:=(.saved 347)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem firstLayer : successors 20 8 inputs = [s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,s37,s38,s39] := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem noinputs : Excluded 20 9 inputs := by
  apply join_exclusions (by decide +kernel)
  intro v hv
  rw [firstLayer] at hv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact nos0
  · exact nos1
  · exact nos2
  · exact nos3
  · exact nos4
  · exact nos5
  · exact nos6
  · exact nos7
  · exact nos8
  · exact nos9
  · exact nos10
  · exact nos11
  · exact nos12
  · exact nos13
  · exact nos14
  · exact nos15
  · exact nos16
  · exact nos17
  · exact nos18
  · exact nos19
  · exact nos20
  · exact nos21
  · exact nos22
  · exact nos23
  · exact nos24
  · exact nos25
  · exact nos26
  · exact nos27
  · exact nos28
  · exact nos29
  · exact nos30
  · exact nos31
  · exact nos32
  · exact nos33
  · exact nos34
  · exact nos35
  · exact nos36
  · exact nos37
  · exact nos38
  · exact nos39


end PEqualNP.Outside.L_meta_12186.KFive

namespace PEqualNP.Outside.L_meta_12186

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (3900735488 * 2 ^ 32 + 2147483648)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [7, 2]⟩, ⟨.or, [6, 8]⟩,
    ⟨.and, [6, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [12, 5]⟩,
    ⟨.or, [11, 13]⟩, ⟨.and, [11, 5]⟩, ⟨.and, [10, 14]⟩, ⟨.and, [9, 15]⟩,
    ⟨.or, [16, 17]⟩], 18⟩

theorem witness_mono : Monotone2 witness := by
  simp [Monotone2, witness]

theorem witness_size : witness.size = 13 := rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem witness_eval : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = target x := by
  decide +kernel

theorem replaceWithLower
    (lower : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x) →
      (∃ g ∈ C.gates, g.op = .not) → 13 ≤ C.size) :
    ∀ s : ℕ, HasCircuitSize 6 target s →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
        ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  intro s H
  obtain ⟨C, legal, budget, computes⟩ := H
  by_cases hasNot : ∃ g ∈ C.gates, g.op = .not
  · refine ⟨witness, witness_mono, ?_, witness_eval⟩
    rw [witness_size]
    exact (lower C legal computes hasNot).trans budget
  · exact ⟨C, fun g hg => ⟨(legal g hg).1.imp_right (·.resolve_right fun h => hasNot ⟨g, hg, h⟩),
      (legal g hg).2⟩, budget, computes⟩

end PEqualNP.Outside.L_meta_12186

namespace PEqualNP.Outside.L_meta_12186

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The five-variable lower bound comes from L-meta-10612.
-- The first-gate argument generalizes the approach of L-meta-11865.
def idx6 (i : Fin 6) : Fin 7 := ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩

theorem idx6_inj : Function.Injective idx6 := by
  intro i j h
  exact Fin.ext (congrArg (fun v : Fin 7 => v.val) h)

def remaining (p : Fin 6) (i : Fin 5) : Fin 7 := idx6 (p.succAbove i)

theorem remaining_inj (p : Fin 6) : Function.Injective (remaining p) :=
  idx6_inj.comp Fin.succAbove_right_injective

def place (p : Fin 6) (x : Fin 5 → Bool) (j : Fin 7) : Bool :=
  decide (∃ i : Fin 5, remaining p i = j ∧ x i = true)

theorem place_here (p : Fin 6) (x : Fin 5 → Bool) (i : Fin 5) :
    place p x (remaining p i) = x i := by
  cases hx : x i <;> simp [place, (remaining_inj p).eq_iff, hx]

def fullTarget (y : Fin 7 → Bool) : Bool := target (fun i => y (idx6 i))

def row6 (p : Fin 6) (x : Fin 7 → Bool) : Fin 7 → Bool :=
  Function.update (fun j => !x j) (idx6 p) true

def phase6 (p : Fin 6) (w : BF) : BF :=
  fun x => Bool.xor (w (row6 p x)) (w (row6 p (fun _ => false)))

theorem phase6_rst (p : Fin 6) (w : BF) : rst (idx6 p) (phase6 p w) = phase6 p w := by
  have same (x : Fin 7 → Bool) :
      row6 p (Function.update x (idx6 p) false) = row6 p x := by
    funext j
    by_cases h : j = idx6 p <;> simp [row6, h, Function.update_of_ne]
  funext x
  simp only [rst, phase6, same]

theorem phase6_self (p : Fin 6) : phase6 p (var (idx6 p)) = zF := by
  funext x
  simp [phase6, row6, var, zF, Bool.xor, Function.update_self]

theorem phase6_ne (p i : Fin 6) (h : i ≠ p) : phase6 p (var (idx6 i)) = var (idx6 i) := by
  funext x
  have hne : idx6 i ≠ idx6 p := fun e => h (idx6_inj e)
  cases hx : x (idx6 i) <;> simp [phase6, row6, var, Function.update_of_ne hne, hx, Bool.xor]

theorem phase6_run {C : Fin 4 → BF → BF → Prop} (p : Fin 6)
    {ys ws : List BF} {s : ℕ} (h : TR gF C ys s ws) :
    TR gF (fun _ _ _ => True) (ys.map (phase6 p)) s (ws.map (phase6 p)) := by
  refine TR.ind (P := fun s ws =>
    TR gF (fun _ _ _ => True) (ys.map (phase6 p)) s (ws.map (phase6 p)))
    h TR.done ?_ ?_
  · intro s a b perm _ ih
    exact TR.perm (perm.map _) ih
  · intro s a b r k u _ _ ih
    obtain ⟨k', hk'⟩ := phaseGate k (a (row6 p (fun _ => false))) (b (row6 p (fun _ => false)))
    have hg : phase6 p (gF k a b) = gF k' (phase6 p a) (phase6 p b) :=
      funext fun x => hk' (a (row6 p x)) (b (row6 p x))
    rw [List.map_append, List.map_replicate, hg] at ih
    exact TR.step k' u trivial ih

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cofactor_table : ∀ (p : Fin 6) (x : Fin 5 → Bool),
    phase6 p fullTarget (place p x) = KFive.graph x := by
  decide +kernel

theorem phase6_nonzero (p : Fin 6) : phase6 p fullTarget ≠ zF := by
  intro he
  have known := cofactor_table p (fun _ => true)
  rw [he] at known
  exact Bool.noConfusion known

def source6 (w : BF) : Prop := ∃ i : Fin 6, w = var (idx6 i)
def coSource (p : Fin 6) (w : BF) : Prop := ∃ i : Fin 5, w = var (remaining p i)

def bankRows : List (Fin 5 → Bool) :=
  (List.finRange 20).map (KFive.sample KFive.posBits) ++
    (List.finRange 20).map (KFive.sample KFive.negBits)

set_option maxRecDepth 8000 in
theorem bankInput : ∀ i : Fin 5, enc (fun x : Fin 5 → Bool => x i) bankRows ∈ KFive.inputs := by
  decide +kernel

def bankOutput : ℕ := enc KFive.graph bankRows

set_option maxRecDepth 8000 in
theorem bankGoodFin : ∀ i : Fin 20, bankOutput.testBit i.val ≠ bankOutput.testBit (20+i.val) := by
  decide +kernel

theorem bankGood : KFive.Good 20 bankOutput := fun i hi => bankGoodFin ⟨i, hi⟩

theorem bankNonzero : bankOutput ≠ 0 := by
  intro eq
  have fail := bankGood 0 (by decide)
  simp [eq] at fail

theorem possibleOfUC :
    ∀ (t : ℕ) (S : ℕ → Prop) (av : List ℕ),
      (∀ a, S a → a ∈ av) →
      UC gN (fun _ => True) t S bankOutput → KFive.Possible 20 t av
  | 0, S, av, inside, hu => by
    refine ⟨0, {bankOutput}, le_rfl, KFive.Live.done bankGood bankNonzero, ?_⟩
    intro a ha
    obtain rfl := Finset.mem_singleton.mp ha
    exact inside bankOutput hu
  | t+1, S, av, inside, hu => by
    rcases hu with hu | ⟨k, a, b, _, ha, hb, ht⟩
    · obtain ⟨n, V, h, hv, hs⟩ := possibleOfUC t S av inside hu
      exact ⟨n, V, by omega, hv, hs⟩
    · have next := possibleOfUC t (fun x => x = gN k a b ∨ S x) (av ++ [gN k a b]) (by
        rintro x (rfl | hx)
        · simp
        · exact List.mem_append_left _ (inside x hx)) ht
      have moved := KFive.pullPaid k.isLt (inside a ha) (inside b hb) next
      obtain ⟨n, V, h, hv, hs⟩ := moved
      have cap : (KFive.charge av (KFive.combine k.val a b)).toNat ≤ 1 := by
        cases KFive.charge av (KFive.combine k.val a b) <;> decide
      exact ⟨n, V, by omega, hv, hs⟩

theorem K5_floor (t : ℕ) (h : UC (fun (k : Fin 4) (a b : (Fin 5 → Bool) → Bool) => fun x => zeroGate k (a x) (b x))
    (fun _ => True) t (fun w => ∃ i : Fin 5, w = (fun x => x i)) KFive.graph) : 10 ≤ t := by
  by_contra! small
  have encoded : UC gN (fun _ => True) t (fun a => a ∈ KFive.inputs) bankOutput := by
    exact UC_map (fun w => enc w bankRows) (fun k a b => enc_gate k a b bankRows) t _ _ KFive.graph
      (by rintro w ⟨i, rfl⟩; exact bankInput i) h
  obtain ⟨k, S, lim, lv, sub⟩ := possibleOfUC t _ KFive.inputs (fun _ h => h) encoded
  rw [KFive.initial lv sub] at lv
  exact KFive.noinputs ⟨k, by omega, lv, by decide⟩

theorem cofactor_floor (p : Fin 6) (t : ℕ)
    (h : UC gF (fun _ => True) t (coSource p) (phase6 p fullTarget)) : 10 ≤ t := by
  let project (w : BF) (x : Fin 5 → Bool) := w (place p x)
  let g5 (k : Fin 4) (a b : (Fin 5 → Bool) → Bool) := fun x => zeroGate k (a x) (b x)
  have mapped := UC_map (G' := g5) project (fun _ _ _ => rfl) t _ (fun w => ∃ i : Fin 5, w = fun x => x i)
    (phase6 p fullTarget) (by
      rintro w ⟨i, rfl⟩
      exact ⟨i, funext fun x => place_here p x i⟩) h
  have eq : project (phase6 p fullTarget) = KFive.graph := funext fun x => by
    change phase6 p fullTarget (place p x) = KFive.graph x
    exact cofactor_table p x
  rw [eq] at mapped
  exact K5_floor t mapped

set_option maxRecDepth 6000 in
theorem atMostOneUse {C : Fin 4 → BF → BF → Prop} (p : Fin 6) (r : List BF) (t : ℕ)
    (ht : t ≤ 11) (inputs : ∀ w ∈ r, source6 w)
    (run : TR gF C [fullTarget] t (var (idx6 p) :: r)) : var (idx6 p) ∉ r := by
  let rs := r.map (phase6 p)
  have pinRun : TR gF (fun _ _ _ => True) [phase6 p fullTarget] t (zF :: rs) := by
    simpa only [List.map_cons, List.map_nil, phase6_self, rs] using phase6_run p run
  have hn : rst (idx6 p) (phase6 p fullTarget) ≠ zF := by
    rw [phase6_rst]
    exact phase6_nonzero p
  obtain ⟨_, cut⟩ := pot_dead (idx6 p) hn pinRun
  have alive : ∀ w ∈ zF :: rs, rst (idx6 p) w ≠ zF → coSource p (rst (idx6 p) w) := by
    intro w hw hne
    rcases List.mem_cons.1 hw with eq | rest
    · subst w
      exact (hne (by rfl)).elim
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 rest
      rw [phase6_rst] at hne ⊢
      obtain ⟨i, rfl⟩ := inputs v hv
      by_cases hi : i = p
      · subst i
        exact (hne (phase6_self p)).elim
      · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hi
        exact ⟨j, by rw [phase6_ne p i hi, remaining, hj]⟩
  have compression : UC gF (fun _ => True) (t - dcount (idx6 p) (zF :: rs))
      (coSource p) (rst (idx6 p) (phase6 p fullTarget)) := cut _ alive
  rw [phase6_rst] at compression
  have need := cofactor_floor p _ compression
  rw [dcount_cons, if_pos (show rst (idx6 p) zF = zF from rfl)] at need
  intro hm
  have hz : zF ∈ rs := List.mem_map.2 ⟨var (idx6 p), hm, phase6_self p⟩
  have hpos : 0 < dcount (idx6 p) rs :=
    List.countP_pos_iff.2 ⟨zF, hz, by rfl⟩
  omega

def rowPair6 (i j : Fin 6) (k : Fin 4) (b : Bool) : Fin 7 → Bool :=
  fun l =>
    if l = idx6 i then (if k = 1 then true else if k = 2 then false else b)
    else if l = idx6 j then (if k = 1 ∨ k = 2 then b else false)
    else (((List.finRange 6).filter fun z => z != i && z != j).take
      (if k = 1 then 3 else 4)).any fun z => idx6 z == l

theorem rowPair6_other {i j l : Fin 6} (hi : l ≠ i) (hj : l ≠ j) (k : Fin 4) :
    rowPair6 i j k false (idx6 l) = rowPair6 i j k true (idx6 l) := by
  have hi' : idx6 l ≠ idx6 i := fun h => hi (idx6_inj h)
  have hj' : idx6 l ≠ idx6 j := fun h => hj (idx6_inj h)
  simp only [rowPair6, if_neg hi', if_neg hj']

set_option maxRecDepth 8000 in
theorem rowPair6_evidence : ∀ (i j : Fin 6) (k : Fin 4), i ≠ j →
    gF k (var (idx6 i)) (var (idx6 j)) (rowPair6 i j k false) =
      gF k (var (idx6 i)) (var (idx6 j)) (rowPair6 i j k true) ∧
    fullTarget (rowPair6 i j k false) ≠ fullTarget (rowPair6 i j k true) := by
  decide +kernel

theorem full_not_var : ∀ i : Fin 6, fullTarget (singleInput (idx6 i)) ≠
    var (idx6 i) (singleInput (idx6 i)) := by decide

theorem runSixImpossible (s : ℕ) (r : List BF) (hs : s ≤ 11)
    (sources : ∀ w ∈ r, source6 w)
    (run : TR gF (strictC gF zF (fun _ => True) (fun _ => True)) [fullTarget] s r) : False := by
  cases s with
  | zero =>
    have hp := (TR.inv run).1 rfl
    obtain ⟨i, he⟩ := sources fullTarget (hp.mem_iff.2 (by simp))
    exact full_not_var i (congrFun he (singleInput (idx6 i)))
  | succ t =>
    obtain ⟨k, u, a, b, rest, gate, perm, tail⟩ := (TR.inv run).2 t rfl
    obtain ⟨i, rfl⟩ := sources a (perm.mem_iff.2 (by simp))
    obtain ⟨j, rfl⟩ := sources b (perm.mem_iff.2 (by simp))
    have hij : i ≠ j := by
      intro e
      subst j
      exact gate.2.2.2.1 rfl
    have original := TR.perm perm run
    have hi := atMostOneUse i (var (idx6 j) :: rest) (t+1) hs (by
      intro w hw
      exact sources w (perm.mem_iff.2 (by simp [hw]))) original
    have rotated := TR.perm (List.Perm.swap (var (idx6 j)) (var (idx6 i)) rest) original
    have hj := atMostOneUse j (var (idx6 i) :: rest) (t+1) hs (by
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact ⟨i, rfl⟩
      · exact sources w (perm.mem_iff.2 (by simp [hw]))) rotated
    have evidence := rowPair6_evidence i j k hij
    refine evidence.2 (TRF_det tail (rowPair6 i j k false) (rowPair6 i j k true) ?_ fullTarget (by simp))
    intro w hw
    rcases List.mem_append.1 hw with head | restMem
    · rw [List.eq_of_mem_replicate head]
      exact evidence.1
    · obtain ⟨l, eq⟩ := sources w (perm.mem_iff.2 (by simp [restMem]))
      have mem : var (idx6 l) ∈ rest := eq ▸ restMem
      have hli : l ≠ i := fun e => hi (List.mem_cons_of_mem _ (e ▸ mem))
      have hlj : l ≠ j := fun e => hj (List.mem_cons_of_mem _ (e ▸ mem))
      rw [eq]
      exact rowPair6_other hli hlj k

theorem fullTarget_nonzero : fullTarget ≠ zF := by
  intro h
  have hcut := congrFun h (fun _ => true)
  exact (by decide : fullTarget (fun _ => true) ≠ false) hcut

theorem binaryFloor (C : Circuit) (legal : FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x) :
    12 ≤ countBinary C.gates := by
  by_contra! small
  let W : List BF := List.ofFn fun i : Fin 6 => var (idx6 i)
  have evalFull : (wiresF C.gates W).getD C.output zF = fullTarget := by
    funext x
    let y : Fin 6 → Bool := fun i => x (idx6 i)
    change ((wiresF C.gates W).getD C.output zF) x = target y
    have he := computes y
    rw [← he, ← getD_map_x, ← wires_eq]
    simp only [Circuit.eval, Circuit.wires, W, List.map_ofFn] <;> rfl
  have h := trans_binary C.gates W source6 legal (by
    intro w hw
    change w ∈ List.ofFn (fun i : Fin 6 => var (idx6 i)) at hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hw
    exact Or.inr ⟨i, ori_zp rfl⟩) C.output
  rw [evalFull, ori_zp (by decide : fullTarget (fun _ => false) = false)] at h
  have hu := h.resolve_left fullTarget_nonzero
  obtain ⟨s, hs, inputs, hi, run⟩ := normalize gF zF (fun _ => True) (fun _ => True)
    (fun _ _ _ _ _ => trivial) gF_zero_left gF_zero_right gF_self
    (countBinary C.gates) source6 fullTarget (fun _ _ => trivial) fullTarget_nonzero hu
  exact runSixImpossible s inputs (by omega) (fun w hw => (hi w hw).1) run

theorem notFloor (C : Circuit) (legal : FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x)
    (hasNot : ∃ g ∈ C.gates, g.op = .not) : 13 ≤ C.size := by
  have low := binaryFloor C legal computes
  have extra := countBinary_lt C.gates hasNot
  change 13 ≤ C.gates.length
  omega

end PEqualNP.Outside.L_meta_12186

open PEqualNP.Outside.L_meta_12186 in
theorem PEqualNP.Outside.L_meta_12186 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3900735488 * 2 ^ 32 + 2147483648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3900735488 * 2 ^ 32 + 2147483648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  replaceWithLower notFloor
