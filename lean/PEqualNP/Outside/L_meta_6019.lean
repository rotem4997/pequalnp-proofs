import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6019

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (4735 : ℕ).testBit (4 * u.val + v.val)) 8 := by
  refine ⟨⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [8, 6]⟩, ⟨GateOp.and, [1, 9]⟩,
    ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [0, 10]⟩,
    ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [13, 14]⟩], 15⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def stepC (pool : List ℕ) : List ℕ :=
  65535 :: 0 :: (pool ++ pool.flatMap (fun a => pool.flatMap (fun b => [a &&& b, a ||| b])))

def Inv (pool : List ℕ) (ws : Fin 16 → List Bool) : Prop :=
  ∀ i : ℕ, ∃ m ∈ pool, ∀ p : Fin 16, m.testBit p = (ws p).getD i false

theorem getD_snoc (l : List Bool) (x : Bool) (i : ℕ) :
    (l ++ [x]).getD i false = if i = l.length then x else l.getD i false := by
  rcases lt_trichotomy i l.length with h | h | h
  · rw [ite_eq_right (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right (by omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

theorem testBit_65535 : ∀ p : Fin 16, (65535 : ℕ).testBit p = true := by decide

theorem gate_vec (pool : List ℕ) (ws : Fin 16 → List Bool) (h : Inv pool ws) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hlen : g.inputs.length ≤ 2) :
    ∃ c ∈ stepC pool, ∀ p : Fin 16,
      c.testBit p = g.op.eval (g.inputs.map fun i => (ws p).getD i false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · exact ⟨65535, by simp [stepC], fun p => by simp [GateOp.eval, testBit_65535 p]⟩
    · exact ⟨0, by simp [stepC], fun p => by simp [GateOp.eval]⟩
  | [a], _ =>
    obtain ⟨ma, hma, ha⟩ := h a
    refine ⟨ma, by simp [stepC, hma], fun p => ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval, ha p]
  | [a, b], _ =>
    obtain ⟨ma, hma, ha⟩ := h a
    obtain ⟨mb, hmb, hb⟩ := h b
    rcases hop with rfl | rfl
    · refine ⟨ma &&& mb, ?_, fun p => ?_⟩
      · simp only [stepC, List.mem_cons, List.mem_append, List.mem_flatMap]
        exact Or.inr (Or.inr (Or.inr ⟨ma, hma, mb, hmb, by simp⟩))
      · simp [GateOp.eval, ha p, hb p]
    · refine ⟨ma ||| mb, ?_, fun p => ?_⟩
      · simp only [stepC, List.mem_cons, List.mem_append, List.mem_flatMap]
        exact Or.inr (Or.inr (Or.inr ⟨ma, hma, mb, hmb, by simp⟩))
      · simp [GateOp.eval, ha p, hb p]
  | _ :: _ :: _ :: _, hl => simp at hl

theorem inv_step (pool pool' : List ℕ) (ws : Fin 16 → List Bool) (L : ℕ)
    (hL : ∀ p, (ws p).length = L) (hI : Inv pool ws) (b : Fin 16 → Bool) (c : ℕ)
    (hcv : ∀ p : Fin 16, c.testBit p = b p) (hsub : ∀ m ∈ pool, m ∈ pool') (hcp : c ∈ pool') :
    Inv pool' (fun p => ws p ++ [b p]) := by
  intro i
  obtain ⟨m, hm, hmb⟩ := hI i
  by_cases hi : i = L
  · subst hi
    exact ⟨c, hcp, fun p => by rw [getD_snoc, ite_eq_left (hL p).symm, hcv p]⟩
  · exact ⟨m, hsub m hm, fun p => by rw [getD_snoc, ite_eq_right (by rw [hL p]; exact hi), hmb p]⟩

def pool0 : List ℕ := [15, 240, 3840, 61440, 4369, 8738, 17476, 34952, 0]

def X (p : Fin 16) : List Bool :=
  oneEach (⟨p.val / 4, by omega⟩ : Fin 4) (⟨p.val % 4, by omega⟩ : Fin 4)

theorem X_len (p : Fin 16) : (X p).length = 8 := by simp [X, oneEach]

theorem inv0 : Inv pool0 X := by
  intro i
  by_cases hi : i < 8
  · have key : ∀ j : Fin 8, ∀ p : Fin 16, (pool0.getD j 0).testBit p = (X p).getD j false := by
      decide
    exact ⟨pool0.getD i 0, by interval_cases i <;> simp [pool0], fun p => key ⟨i, hi⟩ p⟩
  · refine ⟨0, by simp [pool0], fun p => ?_⟩
    rw [Nat.zero_testBit, List.getD_eq_default _ _ (by rw [X_len]; omega)]

def Live : ℕ → Finset ℕ → Prop
  | 0, S => S = {4735}
  | k+1, S => ∃ (a b c : ℕ) (D : Finset ℕ), a < b ∧ c ∉ S ∧ S = insert a (insert b D) ∧
    (c = a &&& b ∨ c = a ||| b) ∧ Live k (insert c D)

theorem live_card {k S} (h : Live k S) : S.card ≤ k+1 := by
  induction k generalizing S with
  | zero => change S = {4735} at h; simp [h]
  | succ k ih =>
    obtain ⟨a,b,c,D,_,hc,rfl,_,ht⟩ := h
    have hd : c ∉ D := fun h => hc (by simp [h])
    have h1 := ih ht
    rw [Finset.card_insert_of_notMem hd] at h1
    have h2 := Finset.card_insert_le a (insert b D)
    have h3 := Finset.card_insert_le b D
    omega

theorem lift_gate {k : ℕ} {P : List ℕ} (hz : 0 ∈ P) (hu : 65535 ∈ P)
    {c : ℕ} (hc : c ∈ stepC P) {S : Finset ℕ} (ht : Live k S)
    (hs : ∀ m ∈ S, m ∈ P ++ [c]) :
    ∃ j ≤ k+1, ∃ Q : Finset ℕ, (∀ m ∈ Q, m ∈ P) ∧ Live j Q := by
  by_cases hold : ∀ m ∈ S, m ∈ P
  · exact ⟨k, by omega, S, hold, ht⟩
  have hn : c ∉ P := by
    intro h
    apply hold
    intro m hm
    rcases List.mem_append.mp (hs m hm) with hh | hh
    · exact hh
    · simpa [List.mem_singleton.mp hh] using h
  have hcs : c ∈ S := by
    by_contra hh
    apply hold
    intro m hm
    have := hs m hm
    simpa [show m ≠ c from fun e => hh (e ▸ hm)] using this
  simp only [stepC, List.mem_cons, List.mem_append, List.mem_flatMap] at hc
  rcases hc with rfl | rfl | h | ⟨a, ha, b, hb, hab⟩
  · exact False.elim (hn hu)
  · exact False.elim (hn hz)
  · exact False.elim (hn h)
  simp only [List.not_mem_nil, or_false] at hab
  let D := S.erase c
  have hd : ∀ m ∈ D, m ∈ P := by
    intro m hm
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hm
    simpa [hne] using hs m hmem
  have he : insert c D = S := Finset.insert_erase hcs
  have go (x y : ℕ) (hx : x ∈ P) (hy : y ∈ P) (hlt : x < y)
      (hop : c = x &&& y ∨ c = x ||| y) :
      ∃ j ≤ k+1, ∃ Q : Finset ℕ, (∀ m ∈ Q, m ∈ P) ∧ Live j Q := by
    have sub : ∀ m ∈ insert x (insert y D), m ∈ P := by
      intro m hm
      simp only [Finset.mem_insert] at hm
      rcases hm with rfl | rfl | hm
      · exact hx
      · exact hy
      · exact hd _ hm
    exact ⟨k+1, le_rfl, _, sub, x, y, c, D, hlt, fun h => hn (sub _ h), rfl, hop, he.symm ▸ ht⟩
  rcases lt_trichotomy a b with hl | rfl | hg
  · exact go a b ha hb hl hab
  · have e : c = a := by simpa using hab
    exact False.elim (hn (e ▸ ha))
  · exact go b a hb ha hg (by simpa [Nat.and_comm b a, Nat.or_comm b a] using hab)

theorem extractLive : ∀ (gs : List Gate) (P : List ℕ) (ws : Fin 16 → List Bool) (L o : ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∀ p, (ws p).length = L) → Inv P ws → (∀ m ∈ P, m < 65536) → 0 ∈ P → 65535 ∈ P →
    (∀ p : Fin 16, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (ws p)).getD o false = (4735 : ℕ).testBit p) →
    ∃ j ≤ gs.length, ∃ S : Finset ℕ, (∀ m ∈ S, m ∈ P) ∧ Live j S
  | [], P, ws, L, o, _, _, hi, hbd, _, _, ho => by
    obtain ⟨m,hm,hv⟩ := hi o
    have hmod : m % 65536 = 4735 := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [show (65536 : ℕ) = 2^16 from rfl, Nat.testBit_mod_two_pow]
      by_cases h : i < 16
      · simpa [h] using (hv ⟨i,h⟩).trans (ho ⟨i,h⟩)
      · simp only [h, decide_false, Bool.false_and]
        exact (Nat.testBit_eq_false_of_lt (show 4735 < 2^i by
          calc 4735 < 2^16 := by decide
               _ ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega))).symm
    exact ⟨0, le_rfl, {4735}, by
      intro n hn
      simp only [Finset.mem_singleton] at hn
      subst n
      rw [Nat.mod_eq_of_lt (hbd _ hm)] at hmod
      exact hmod ▸ hm, rfl⟩
  | g :: gs, P, ws, L, o, hg, hl, hi, hbd, hz, hu, ho => by
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    obtain ⟨c,hc,hcv⟩ := gate_vec P ws hi g hop hlen
    have hcbd : c < 65536 := by
      simp only [stepC, List.mem_cons, List.mem_append, List.mem_flatMap] at hc
      rcases hc with rfl | rfl | h | ⟨a,ha,b,hb,h⟩
      · decide
      · decide
      · exact hbd _ h
      · simp only [List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact lt_of_le_of_lt Nat.and_le_left (hbd _ ha)
        · exact Nat.or_lt_two_pow (n := 16) (hbd _ ha) (hbd _ hb)
    obtain ⟨k,hk,S,hs,ht⟩ := extractLive gs (P ++ [c]) _ (L+1) o
      (fun g hg' => hg g (by simp [hg'])) (fun p => by simp [hl p])
      (inv_step P (P ++ [c]) ws L hl hi _ c hcv (fun m hm => by simp [hm]) (by simp))
      (by simpa only [List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] using And.intro hbd hcbd)
      (by simp [hz]) (by simp [hu]) (fun p => ho p)
    obtain ⟨j,hj,Q,hQ,hL⟩ := lift_gate hz hu hc ht hs
    exact ⟨j, by simp; omega, Q, hQ, hL⟩
theorem preserve {k S} (h : Live k S) (p q : ℕ)
    (hp : (4735 : ℕ).testBit p = true)
    (hs : ∀ x ∈ S, x.testBit p = true → x.testBit q = true) : (4735 : ℕ).testBit q = true := by
  induction k generalizing S with
  | zero =>
    change S = {4735} at h
    exact hs _ (by simp [h]) hp
  | succ k ih =>
    obtain ⟨a,b,c,D,_,_,rfl,hop,ht⟩ := h
    apply ih ht
    intro x hx hxp
    rcases Finset.mem_insert.mp hx with rfl | hd
    · have ha := hs a (by simp)
      have hb := hs b (by simp)
      rcases hop with rfl | rfl
      · simp only [Nat.testBit_and, Bool.and_eq_true] at hxp ⊢
        exact ⟨ha hxp.1, hb hxp.2⟩
      · simp only [Nat.testBit_or, Bool.or_eq_true] at hxp ⊢
        exact hxp.imp ha hb
    · exact hs _ (by simp [hd]) hxp

def bad (p : ℕ) : List ℕ → ℕ
  | [] => 60800
  | x :: xs => if x.testBit p then x &&& bad p xs else bad p xs

theorem bad_spec {p q : ℕ} (l : List ℕ) (h : (bad p l).testBit q = true) :
    (60800 : ℕ).testBit q = true ∧ ∀ x ∈ l, x.testBit p = true → x.testBit q = true := by
  induction l with
  | nil => exact ⟨h, by simp⟩
  | cons x xs ih =>
    simp only [bad] at h
    split at h
    · simp only [Nat.testBit_and, Bool.and_eq_true] at h
      obtain ⟨hn,ha⟩ := ih h.2
      exact ⟨hn, by simpa using And.intro (fun _ => h.1) ha⟩
    · obtain ⟨hn,ha⟩ := ih h
      exact ⟨hn, by simp_all⟩

def positives : List ℕ := [0,1,2,3,4,5,6,9,12]

def screen (l : List ℕ) : Bool := positives.all fun p => bad p l == 0

theorem passes {k : ℕ} {l : List ℕ} (h : Live k l.toFinset) : screen l = true := by
  apply List.all_eq_true.mpr
  intro p hp
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro q
  rw [Nat.zero_testBit]
  cases he : (bad p l).testBit q with
  | false => rfl
  | true =>
    obtain ⟨hn,hm⟩ := bad_spec l he
    have hpos : ∀ n ∈ positives, (4735 : ℕ).testBit n = true := by decide
    have ht := preserve h p q (hpos _ hp) (by simpa using hm)
    have hh : (4735 &&& 60800 : ℕ).testBit q = true := by rw [Nat.testBit_and, ht, hn]; rfl
    change (0 : ℕ).testBit q = true at hh
    simp at hh

def trim (l : List ℕ) (a b : ℕ) (u v : Bool) : List ℕ :=
  l.filter fun x => (x != a || u) && (x != b || v)

def flags : List Bool := [false,true]

def run : ℕ → List ℕ → Bool
  | 0, l => l.contains 4735
  | k+1, l => l.length ≤ k+2 && screen l && (l.contains 4735 ||
    l.any fun a => l.any fun b => a < b && [a &&& b, a ||| b].any fun c =>
      !l.contains c && flags.any fun u => flags.any fun v =>
        let t := c :: trim l a b u v
        t.length ≤ k+1 && run k t)

theorem trim_set {l : List ℕ} {a b : ℕ} {D : Finset ℕ}
    (h : l.toFinset = insert a (insert b D)) :
    (trim l a b (decide (a ∈ D)) (decide (b ∈ D))).toFinset = D := by
  ext x
  have hx : x ∈ l ↔ x = a ∨ x = b ∨ x ∈ D := by
    rw [← List.mem_toFinset, h]
    simp
  by_cases ha : x = a <;> by_cases hb : x = b <;>
    simp_all [trim]

theorem run_of {k j : ℕ} (hj : j ≤ k) (l : List ℕ) (hn : l.Nodup) (h : Live j l.toFinset) :
    run k l = true := by
  have hlen := live_card h
  rw [List.toFinset_card_of_nodup hn] at hlen
  cases k with
  | zero =>
    have : j = 0 := by omega
    subst j
    change l.toFinset = {4735} at h
    change l.contains 4735 = true
    simpa using (show 4735 ∈ l.toFinset by rw [h]; simp)
  | succ k =>
    simp only [run, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
    refine ⟨⟨by omega, passes h⟩, ?_⟩
    cases j with
    | zero =>
      change l.toFinset = {4735} at h
      left
      simpa using (show 4735 ∈ l.toFinset by rw [h]; simp)
    | succ j =>
      obtain ⟨a,b,c,D,hab,hc,hl,hop,ht⟩ := h
      right
      simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
      have ha : a ∈ l := by rw [← List.mem_toFinset,hl]; simp
      have hb : b ∈ l := by rw [← List.mem_toFinset,hl]; simp
      let u := decide (a ∈ D)
      let v := decide (b ∈ D)
      let t := c :: trim l a b u v
      have he : t.toFinset = insert c D := by simp [t,u,v,trim_set hl]
      have hn' : t.Nodup := by
        apply List.nodup_cons.mpr
        refine ⟨fun hh => hc (by exact List.mem_toFinset.mpr (List.mem_filter.mp hh).1), ?_⟩
        exact hn.filter _
      have ht' : Live j t.toFinset := he.symm ▸ ht
      have hl' := live_card ht'
      rw [List.toFinset_card_of_nodup hn'] at hl'
      refine ⟨a,ha,b,hb,hab,c,by simpa using hop,by simpa using hc,u,?_,v,?_,?_,?_⟩
      · cases u <;> simp [flags]
      · cases v <;> simp [flags]
      · change t.length ≤ k+1
        omega
      · exact run_of (by omega : j ≤ k) t hn' ht'
termination_by k
def initial : List ℕ := 65535 :: pool0

theorem failed : ∀ l ∈ initial.sublists, run 7 l = false := by decide +kernel

theorem lower : ¬ RepSizeAtMost (fun u v : Fin 4 => (4735 : ℕ).testBit (4 * u.val + v.val)) 7 := by
  rintro ⟨C,hC,hs,hr⟩
  obtain ⟨j,hj,S,hsub,hLive⟩ := extractLive C.gates initial X 8 C.output hC X_len
    (fun i => by obtain ⟨m,hm,hv⟩ := inv0 i; exact ⟨m,List.mem_cons_of_mem _ hm,hv⟩)
    (by decide) (by decide) (by decide) (fun p => by
      have h := hr ⟨p.val / 4, by omega⟩ ⟨p.val % 4, by omega⟩
      exact h.trans (congrArg (Nat.testBit 4735) (Nat.div_add_mod p.val 4)))
  let l := initial.filter fun x => decide (x ∈ S)
  have he : l.toFinset = S := by
    ext x
    simp [l, and_iff_right_of_imp (hsub x)]
  have hn : l.Nodup := (show initial.Nodup by decide).filter _
  have hh := run_of (by change C.gates.length ≤ 7 at hs; omega : j ≤ 7) l hn (he.symm ▸ hLive)
  rw [failed l (List.mem_sublists.mpr List.filter_sublist)] at hh
  contradiction

end PEqualNP.Outside.L_meta_6019
theorem PEqualNP.Outside.L_meta_6019 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4735 : ℕ).testBit (4 * u.val + v.val)) 8 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4735 : ℕ).testBit (4 * u.val + v.val)) 7 := by
  exact ⟨PEqualNP.Outside.L_meta_6019.upper, PEqualNP.Outside.L_meta_6019.lower⟩
