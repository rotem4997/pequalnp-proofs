import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6058

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- Wire profiles on the sixteen promised inputs, adapted from L-meta-5471.
def stepC (pool : List ℕ) : List ℕ :=
  65535 :: 0 :: (pool ++ pool.flatMap (fun a => pool.flatMap (fun b => [a &&& b, a ||| b])))

def Inv (pool : List ℕ) (ws : Fin 16 → List Bool) : Prop :=
  ∀ i : ℕ, ∃ m ∈ pool, ∀ p : Fin 16, m.testBit p = (ws p).getD i false

theorem getD_snoc (l : List Bool) (x : Bool) (i : ℕ) :
    (l ++ [x]).getD i false = if i = l.length then x else l.getD i false := by
  rcases lt_trichotomy i l.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega), List.getD_eq_default _ _ (by simp; omega),
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
    exact ⟨c, hcp, fun p => by rw [getD_snoc, if_pos (hL p).symm, hcv p]⟩
  · exact ⟨m, hsub m hm, fun p => by rw [getD_snoc, if_neg (by rw [hL p]; exact hi), hmb p]⟩

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

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (5071 : ℕ).testBit (4*u.val+v.val)) 8 := by
  refine ⟨⟨[⟨.or,[6,7]⟩,⟨.and,[1,8]⟩,⟨.or,[4,5]⟩,⟨.and,[2,10]⟩,⟨.and,[3,4]⟩,⟨.or,[0,9]⟩,⟨.or,[11,12]⟩,⟨.or,[13,14]⟩],15⟩,?_,by decide,by decide⟩
  intro g hg
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

abbrev good (S : Finset Nat) := ∀ p q : Fin 16,(5071 : Nat).testBit p=true → (5071 : Nat).testBit q=false →
  ∃ m∈S,m.testBit p=true ∧ m.testBit q=false
def base : Finset Nat := {15,240,3840,4369,8738,17476,34952,61440}
-- Each member lists truth tables of wires still able to separate all positive rows from all negative rows.
def family : List (Finset Nat) := [{15,192,3840,4369,8738,61440},{15,192,3840,4369,61986},{15,240,3840,4369,8738,17476,34952,61440},{15,240,3840,4369,8738,17476,63624},{15,240,3840,4369,8738,34952,62532},{15,240,3840,4369,8738,52428,61440},{15,240,3840,4369,8738,64716},{15,240,3840,4369,17476,34952,61986},{15,240,3840,4369,52428,61986},{15,240,4369,8738,17476,36744,61440},{15,240,4369,8738,20292,34952,61440},{15,240,4369,8738,20292,63624},{15,240,4369,8738,36744,62532},{15,240,4369,8738,53196,61440},{15,3840,4369,8946,17476,34952,61440},{15,3840,4369,8946,52428,61440},{15,3840,4593,8738,17476,34952,61440},{15,3840,4593,8738,17476,63624},{15,3840,4593,8738,34952,62532},{15,3840,4593,8738,52428,61440},{15,3840,4593,8738,64716},{15,4369,8946,17476,36744,61440},{15,4369,8946,20292,34952,61440},{15,4369,8946,53196,61440},{15,4593,8738,17476,36744,61440},{15,4593,8738,20292,34952,61440},{15,4593,8738,20292,63624},{15,4593,8738,36744,62532},{15,4593,8738,53196,61440},{207,3840,4369,8738,61440},{207,3840,4369,61986}]
def merge (S : Finset Nat) (a b c : Nat) := insert c ((S.erase a).erase b)
theorem initial : base∈family := by decide
theorem noSingle : ∀ S∈family,1<S.card := by decide
theorem baseCard : base.card=8 := by decide
def inputs : Finset Nat := insert 65535 pool0.toFinset
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
theorem necessary : ∀ a∈base,¬good (inputs.erase a) := by decide +kernel
def pick (w : List Nat) (codes : List Nat) (a b c : Nat) : Nat :=
  codes.getD (2*(w.idxOf a*w.length + w.idxOf b) + (if c=a &&& b then 0 else 1)) 0
abbrev test (S : Finset Nat) (a b c z : Nat) : Prop :=
  let V := merge S a b c
  if z<256 then
    let p := z/16
    let q := z % 16
    (5071 : Nat).testBit p=true ∧ (5071 : Nat).testBit q=false ∧ ∀ m∈V,¬(m.testBit p=true ∧ m.testBit q=false)
  else family[z-256]?=some V
theorem test_ok {S : Finset Nat} {a b c z : Nat} (h : test S a b c z) (ok : good (merge S a b c)) :
    merge S a b c∈family := by
  unfold test at h
  dsimp only at h
  split at h
  · rename_i lt
    obtain ⟨pos,neg,no⟩ := h
    obtain ⟨m,hm,x,y⟩ := ok ⟨z/16,by omega⟩ ⟨z % 16,by omega⟩ pos neg
    exact (no m hm ⟨x,y⟩).elim
  · exact List.mem_of_getElem? h
def code0 : Nat → Nat → Nat → Nat := pick [15,192,3840,4369,8738,61440] [0,0,4,285,4,42,21,4,4,21,4,29,4,285,0,0,100,106,100,100,100,101,100,109,4,42,100,106,0,0,149,132,132,149,132,157,21,4,100,100,149,132,0,0,138,205,138,196,4,21,100,101,132,149,138,205,0,0,154,257,4,29,100,109,132,157,138,196,154,257,0,0]
theorem checked0 : let S : Finset Nat := {15,192,3840,4369,8738,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code0 a b c) := by decide +kernel
theorem closed0 : let S : Finset Nat := {15,192,3840,4369,8738,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked0 a ha b hb ne c hc hn) ok
def code1 : Nat → Nat → Nat → Nat := pick [15,192,3840,4369,61986] [0,0,4,286,4,42,21,4,4,21,4,286,0,0,100,106,100,100,100,101,4,42,100,106,0,0,149,132,132,149,21,4,100,100,149,132,0,0,138,196,4,21,100,101,132,149,138,196,0,0]
theorem checked1 : let S : Finset Nat := {15,192,3840,4369,61986}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code1 a b c) := by decide +kernel
theorem closed1 : let S : Finset Nat := {15,192,3840,4369,61986}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked1 a ha b hb ne c hc hn) ok
def code2 : Nat → Nat → Nat → Nat := pick [15,240,3840,4369,8738,17476,34952,61440] [0,0,4,4,4,42,21,4,4,21,4,42,4,59,4,29,4,4,0,0,106,106,106,272,106,270,123,100,106,116,106,110,4,42,106,106,0,0,149,132,132,149,100,266,116,265,132,157,21,4,106,272,149,132,0,0,138,205,100,100,116,116,138,196,4,21,106,270,132,149,138,205,0,0,100,101,116,117,154,263,4,42,123,100,100,266,100,100,100,101,0,0,100,261,100,260,4,59,106,116,116,265,116,116,116,117,100,261,0,0,116,259,4,29,106,110,132,157,138,196,154,263,100,260,116,259,0,0]
theorem checked2 : let S : Finset Nat := {15,240,3840,4369,8738,17476,34952,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code2 a b c) := by decide +kernel
theorem closed2 : let S : Finset Nat := {15,240,3840,4369,8738,17476,34952,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked2 a ha b hb ne c hc hn) ok
def code3 : Nat → Nat → Nat → Nat := pick [15,240,3840,4369,8738,17476,63624] [0,0,4,4,4,42,21,4,4,21,4,42,4,29,4,4,0,0,106,106,106,273,106,125,123,100,106,110,4,42,106,106,0,0,149,132,132,149,100,267,116,157,21,4,106,273,149,132,0,0,138,205,100,100,116,116,4,21,106,125,132,149,138,205,0,0,100,101,116,117,4,42,123,100,100,267,100,100,100,101,0,0,100,262,4,29,106,110,116,157,116,116,116,117,100,262,0,0]
theorem checked3 : let S : Finset Nat := {15,240,3840,4369,8738,17476,63624}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code3 a b c) := by decide +kernel
theorem closed3 : let S : Finset Nat := {15,240,3840,4369,8738,17476,63624}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked3 a ha b hb ne c hc hn) ok
def code4 : Nat → Nat → Nat → Nat := pick [15,240,3840,4369,8738,34952,62532] [0,0,4,4,4,42,21,4,4,21,4,47,4,29,4,4,0,0,106,106,106,274,106,109,106,111,123,100,4,42,106,106,0,0,149,132,132,149,116,268,100,157,21,4,106,274,149,132,0,0,138,205,116,116,100,100,4,21,106,109,132,149,138,205,0,0,116,117,100,101,4,47,106,111,116,268,116,116,116,117,0,0,100,262,4,29,123,100,100,157,100,100,100,101,100,262,0,0]
theorem checked4 : let S : Finset Nat := {15,240,3840,4369,8738,34952,62532}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code4 a b c) := by decide +kernel
theorem closed4 : let S : Finset Nat := {15,240,3840,4369,8738,34952,62532}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked4 a ha b hb ne c hc hn) ok
def code5 : Nat → Nat → Nat → Nat := pick [15,240,3840,4369,8738,52428,61440] [0,0,4,4,4,42,21,4,4,21,4,42,4,29,4,4,0,0,106,106,106,275,106,271,256,100,106,110,4,42,106,106,0,0,149,132,132,149,100,269,132,157,21,4,106,275,149,132,0,0,138,205,100,100,138,196,4,21,106,271,132,149,138,205,0,0,100,101,154,264,4,42,256,100,100,269,100,100,100,101,0,0,100,262,4,29,106,110,132,157,138,196,154,264,100,262,0,0]
theorem checked5 : let S : Finset Nat := {15,240,3840,4369,8738,52428,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code5 a b c) := by decide +kernel
theorem closed5 : let S : Finset Nat := {15,240,3840,4369,8738,52428,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked5 a ha b hb ne c hc hn) ok
def code6 : Nat → Nat → Nat → Nat := pick [15,240,3840,4369,8738,64716] [0,0,4,4,4,42,21,4,4,21,4,29,4,4,0,0,106,106,106,276,106,109,196,100,4,42,106,106,0,0,149,132,132,149,100,157,21,4,106,276,149,132,0,0,138,205,100,100,4,21,106,109,132,149,138,205,0,0,100,101,4,29,196,100,100,157,100,100,100,101,0,0]
theorem checked6 : let S : Finset Nat := {15,240,3840,4369,8738,64716}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code6 a b c) := by decide +kernel
theorem closed6 : let S : Finset Nat := {15,240,3840,4369,8738,64716}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked6 a ha b hb ne c hc hn) ok
def code7 : Nat → Nat → Nat → Nat := pick [15,240,3840,4369,17476,34952,61986] [0,0,4,4,4,42,21,4,4,30,4,31,4,21,4,4,0,0,106,106,106,197,123,100,106,116,106,110,4,42,106,106,0,0,149,132,100,158,116,159,132,149,21,4,106,197,149,132,0,0,100,100,116,116,138,196,4,30,123,100,100,158,100,100,0,0,100,264,100,101,4,31,106,116,116,159,116,116,100,264,0,0,116,117,4,21,106,110,132,149,138,196,100,101,116,117,0,0]
theorem checked7 : let S : Finset Nat := {15,240,3840,4369,17476,34952,61986}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code7 a b c) := by decide +kernel
theorem closed7 : let S : Finset Nat := {15,240,3840,4369,17476,34952,61986}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked7 a ha b hb ne c hc hn) ok
def code8 : Nat → Nat → Nat → Nat := pick [15,240,3840,4369,52428,61986] [0,0,4,4,4,42,21,4,4,30,4,21,4,4,0,0,106,106,106,197,257,100,106,110,4,42,106,106,0,0,149,132,100,158,132,149,21,4,106,197,149,132,0,0,100,100,138,196,4,30,257,100,100,158,100,100,0,0,100,101,4,21,106,110,132,149,138,196,100,101,0,0]
theorem checked8 : let S : Finset Nat := {15,240,3840,4369,52428,61986}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code8 a b c) := by decide +kernel
theorem closed8 : let S : Finset Nat := {15,240,3840,4369,52428,61986}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked8 a ha b hb ne c hc hn) ok
def code9 : Nat → Nat → Nat → Nat := pick [15,240,4369,8738,17476,36744,61440] [0,0,4,4,21,4,4,21,4,42,4,42,4,29,4,4,0,0,106,280,106,277,122,100,106,106,106,110,21,4,106,280,0,0,138,205,100,100,116,116,138,143,4,21,106,277,138,205,0,0,100,101,116,117,154,159,4,42,122,100,100,100,100,101,0,0,100,269,100,268,4,42,106,106,116,116,116,117,100,269,0,0,116,157,4,29,106,110,138,143,154,159,100,268,116,157,0,0]
theorem checked9 : let S : Finset Nat := {15,240,4369,8738,17476,36744,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code9 a b c) := by decide +kernel
theorem closed9 : let S : Finset Nat := {15,240,4369,8738,17476,36744,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked9 a ha b hb ne c hc hn) ok
def code10 : Nat → Nat → Nat → Nat := pick [15,240,4369,8738,20292,34952,61440] [0,0,4,4,21,4,4,21,4,42,4,43,4,29,4,4,0,0,106,281,106,278,123,100,106,107,106,110,21,4,106,281,0,0,138,205,100,100,116,116,138,142,4,21,106,278,138,205,0,0,100,101,116,117,154,158,4,42,123,100,100,100,100,101,0,0,100,269,100,157,4,43,106,107,116,116,116,117,100,269,0,0,116,267,4,29,106,110,138,142,154,158,100,157,116,267,0,0]
theorem checked10 : let S : Finset Nat := {15,240,4369,8738,20292,34952,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code10 a b c) := by decide +kernel
theorem closed10 : let S : Finset Nat := {15,240,4369,8738,20292,34952,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked10 a ha b hb ne c hc hn) ok
def code11 : Nat → Nat → Nat → Nat := pick [15,240,4369,8738,20292,63624] [0,0,4,4,21,4,4,21,4,42,4,29,4,4,0,0,106,282,106,125,123,100,106,107,21,4,106,282,0,0,138,205,100,100,116,116,4,21,106,125,138,205,0,0,100,101,116,117,4,42,123,100,100,100,100,101,0,0,100,157,4,29,106,107,116,116,116,117,100,157,0,0]
theorem checked11 : let S : Finset Nat := {15,240,4369,8738,20292,63624}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code11 a b c) := by decide +kernel
theorem closed11 : let S : Finset Nat := {15,240,4369,8738,20292,63624}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked11 a ha b hb ne c hc hn) ok
def code12 : Nat → Nat → Nat → Nat := pick [15,240,4369,8738,36744,62532] [0,0,4,4,21,4,4,21,4,42,4,29,4,4,0,0,106,283,106,109,106,106,122,100,21,4,106,283,0,0,138,205,116,116,100,100,4,21,106,109,138,205,0,0,116,117,100,101,4,42,106,106,116,116,116,117,0,0,100,157,4,29,122,100,100,100,100,101,100,157,0,0]
theorem checked12 : let S : Finset Nat := {15,240,4369,8738,36744,62532}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code12 a b c) := by decide +kernel
theorem closed12 : let S : Finset Nat := {15,240,4369,8738,36744,62532}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked12 a ha b hb ne c hc hn) ok
def code13 : Nat → Nat → Nat → Nat := pick [15,240,4369,8738,53196,61440] [0,0,4,4,21,4,4,21,4,42,4,29,4,4,0,0,106,284,106,279,132,100,106,110,21,4,106,284,0,0,138,205,100,100,138,142,4,21,106,279,138,205,0,0,100,101,154,158,4,42,132,100,100,100,100,101,0,0,100,157,4,29,106,110,138,142,154,158,100,157,0,0]
theorem checked13 : let S : Finset Nat := {15,240,4369,8738,53196,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code13 a b c) := by decide +kernel
theorem closed13 : let S : Finset Nat := {15,240,4369,8738,53196,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked13 a ha b hb ne c hc hn) ok
def code14 : Nat → Nat → Nat → Nat := pick [15,3840,4369,8946,17476,34952,61440] [0,0,4,42,20,4,4,4,4,42,4,59,4,29,4,42,0,0,148,132,106,106,100,278,116,277,132,157,20,4,148,132,0,0,106,205,100,100,116,116,138,196,4,4,106,106,106,205,0,0,123,100,106,116,106,110,4,42,100,278,100,100,123,100,0,0,100,271,100,109,4,59,116,277,116,116,106,116,100,271,0,0,116,125,4,29,132,157,138,196,106,110,100,109,116,125,0,0]
theorem checked14 : let S : Finset Nat := {15,3840,4369,8946,17476,34952,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code14 a b c) := by decide +kernel
theorem closed14 : let S : Finset Nat := {15,3840,4369,8946,17476,34952,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked14 a ha b hb ne c hc hn) ok
def code15 : Nat → Nat → Nat → Nat := pick [15,3840,4369,8946,52428,61440] [0,0,4,42,20,4,4,4,4,42,4,29,4,42,0,0,148,132,106,106,100,279,132,157,20,4,148,132,0,0,106,205,100,100,138,196,4,4,106,106,106,205,0,0,154,100,106,110,4,42,100,279,100,100,154,100,0,0,100,109,4,29,132,157,138,196,106,110,100,109,0,0]
theorem checked15 : let S : Finset Nat := {15,3840,4369,8946,52428,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code15 a b c) := by decide +kernel
theorem closed15 : let S : Finset Nat := {15,3840,4369,8946,52428,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked15 a ha b hb ne c hc hn) ok
def code16 : Nat → Nat → Nat → Nat := pick [15,3840,4593,8738,17476,34952,61440] [0,0,4,42,21,4,4,5,4,42,4,59,4,29,4,42,0,0,106,106,132,133,100,281,116,280,132,157,21,4,106,106,0,0,106,205,123,100,106,116,106,110,4,5,132,133,106,205,0,0,100,101,116,117,154,197,4,42,100,281,123,100,100,101,0,0,100,275,100,274,4,59,116,280,106,116,116,117,100,275,0,0,116,273,4,29,132,157,106,110,154,197,100,274,116,273,0,0]
theorem checked16 : let S : Finset Nat := {15,3840,4593,8738,17476,34952,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code16 a b c) := by decide +kernel
theorem closed16 : let S : Finset Nat := {15,3840,4593,8738,17476,34952,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked16 a ha b hb ne c hc hn) ok
def code17 : Nat → Nat → Nat → Nat := pick [15,3840,4593,8738,17476,63624] [0,0,4,42,21,4,4,5,4,42,4,29,4,42,0,0,106,106,132,133,100,282,116,157,21,4,106,106,0,0,106,125,123,100,106,110,4,5,132,133,106,125,0,0,100,101,116,117,4,42,100,282,123,100,100,101,0,0,100,276,4,29,116,157,106,110,116,117,100,276,0,0]
theorem checked17 : let S : Finset Nat := {15,3840,4593,8738,17476,63624}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code17 a b c) := by decide +kernel
theorem closed17 : let S : Finset Nat := {15,3840,4593,8738,17476,63624}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked17 a ha b hb ne c hc hn) ok
def code18 : Nat → Nat → Nat → Nat := pick [15,3840,4593,8738,34952,62532] [0,0,4,42,21,4,4,5,4,47,4,29,4,42,0,0,106,106,132,133,116,283,100,157,21,4,106,106,0,0,106,109,106,111,123,100,4,5,132,133,106,109,0,0,116,117,100,101,4,47,116,283,106,111,116,117,0,0,100,276,4,29,100,157,123,100,100,101,100,276,0,0]
theorem checked18 : let S : Finset Nat := {15,3840,4593,8738,34952,62532}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code18 a b c) := by decide +kernel
theorem closed18 : let S : Finset Nat := {15,3840,4593,8738,34952,62532}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked18 a ha b hb ne c hc hn) ok
def code19 : Nat → Nat → Nat → Nat := pick [15,3840,4593,8738,52428,61440] [0,0,4,42,21,4,4,5,4,42,4,29,4,42,0,0,106,106,132,133,100,284,132,157,21,4,106,106,0,0,106,205,138,100,106,110,4,5,132,133,106,205,0,0,100,101,154,197,4,42,100,284,138,100,100,101,0,0,100,276,4,29,132,157,106,110,154,197,100,276,0,0]
theorem checked19 : let S : Finset Nat := {15,3840,4593,8738,52428,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code19 a b c) := by decide +kernel
theorem closed19 : let S : Finset Nat := {15,3840,4593,8738,52428,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked19 a ha b hb ne c hc hn) ok
def code20 : Nat → Nat → Nat → Nat := pick [15,3840,4593,8738,64716] [0,0,4,42,21,4,4,5,4,29,4,42,0,0,106,106,132,133,100,157,21,4,106,106,0,0,106,109,138,100,4,5,132,133,106,109,0,0,100,101,4,29,100,157,138,100,100,101,0,0]
theorem checked20 : let S : Finset Nat := {15,3840,4593,8738,64716}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code20 a b c) := by decide +kernel
theorem closed20 : let S : Finset Nat := {15,3840,4593,8738,64716}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked20 a ha b hb ne c hc hn) ok
def code21 : Nat → Nat → Nat → Nat := pick [15,4369,8946,17476,36744,61440] [0,0,20,4,4,4,4,42,4,42,4,29,20,4,0,0,106,205,100,100,116,116,138,143,4,4,106,205,0,0,122,100,106,106,106,110,4,42,100,100,122,100,0,0,100,279,100,109,4,42,116,116,106,106,100,279,0,0,116,125,4,29,138,143,106,110,100,109,116,125,0,0]
theorem checked21 : let S : Finset Nat := {15,4369,8946,17476,36744,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code21 a b c) := by decide +kernel
theorem closed21 : let S : Finset Nat := {15,4369,8946,17476,36744,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked21 a ha b hb ne c hc hn) ok
def code22 : Nat → Nat → Nat → Nat := pick [15,4369,8946,20292,34952,61440] [0,0,20,4,4,4,4,42,4,43,4,29,20,4,0,0,106,205,100,100,116,116,138,142,4,4,106,205,0,0,123,100,106,107,106,110,4,42,100,100,123,100,0,0,100,279,100,109,4,43,116,116,106,107,100,279,0,0,116,125,4,29,138,142,106,110,100,109,116,125,0,0]
theorem checked22 : let S : Finset Nat := {15,4369,8946,20292,34952,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code22 a b c) := by decide +kernel
theorem closed22 : let S : Finset Nat := {15,4369,8946,20292,34952,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked22 a ha b hb ne c hc hn) ok
def code23 : Nat → Nat → Nat → Nat := pick [15,4369,8946,53196,61440] [0,0,20,4,4,4,4,42,4,29,20,4,0,0,106,205,100,100,138,142,4,4,106,205,0,0,132,100,106,110,4,42,100,100,132,100,0,0,100,109,4,29,138,142,106,110,100,109,0,0]
theorem checked23 : let S : Finset Nat := {15,4369,8946,53196,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code23 a b c) := by decide +kernel
theorem closed23 : let S : Finset Nat := {15,4369,8946,53196,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked23 a ha b hb ne c hc hn) ok
def code24 : Nat → Nat → Nat → Nat := pick [15,4593,8738,17476,36744,61440] [0,0,21,4,4,5,4,42,4,42,4,29,21,4,0,0,106,205,122,100,106,106,106,110,4,5,106,205,0,0,100,101,116,117,154,159,4,42,122,100,100,101,0,0,100,284,100,283,4,42,106,106,116,117,100,284,0,0,116,157,4,29,106,110,154,159,100,283,116,157,0,0]
theorem checked24 : let S : Finset Nat := {15,4593,8738,17476,36744,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code24 a b c) := by decide +kernel
theorem closed24 : let S : Finset Nat := {15,4593,8738,17476,36744,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked24 a ha b hb ne c hc hn) ok
def code25 : Nat → Nat → Nat → Nat := pick [15,4593,8738,20292,34952,61440] [0,0,21,4,4,5,4,42,4,43,4,29,21,4,0,0,106,205,123,100,106,107,106,110,4,5,106,205,0,0,100,101,116,117,154,158,4,42,123,100,100,101,0,0,100,284,100,157,4,43,106,107,116,117,100,284,0,0,116,282,4,29,106,110,154,158,100,157,116,282,0,0]
theorem checked25 : let S : Finset Nat := {15,4593,8738,20292,34952,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code25 a b c) := by decide +kernel
theorem closed25 : let S : Finset Nat := {15,4593,8738,20292,34952,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked25 a ha b hb ne c hc hn) ok
def code26 : Nat → Nat → Nat → Nat := pick [15,4593,8738,20292,63624] [0,0,21,4,4,5,4,42,4,29,21,4,0,0,106,125,123,100,106,107,4,5,106,125,0,0,100,101,116,117,4,42,123,100,100,101,0,0,100,157,4,29,106,107,116,117,100,157,0,0]
theorem checked26 : let S : Finset Nat := {15,4593,8738,20292,63624}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code26 a b c) := by decide +kernel
theorem closed26 : let S : Finset Nat := {15,4593,8738,20292,63624}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked26 a ha b hb ne c hc hn) ok
def code27 : Nat → Nat → Nat → Nat := pick [15,4593,8738,36744,62532] [0,0,21,4,4,5,4,42,4,29,21,4,0,0,106,109,106,106,122,100,4,5,106,109,0,0,116,117,100,101,4,42,106,106,116,117,0,0,100,157,4,29,122,100,100,101,100,157,0,0]
theorem checked27 : let S : Finset Nat := {15,4593,8738,36744,62532}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code27 a b c) := by decide +kernel
theorem closed27 : let S : Finset Nat := {15,4593,8738,36744,62532}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked27 a ha b hb ne c hc hn) ok
def code28 : Nat → Nat → Nat → Nat := pick [15,4593,8738,53196,61440] [0,0,21,4,4,5,4,42,4,29,21,4,0,0,106,205,149,100,106,110,4,5,106,205,0,0,100,101,154,158,4,42,149,100,100,101,0,0,100,157,4,29,106,110,154,158,100,157,0,0]
theorem checked28 : let S : Finset Nat := {15,4593,8738,53196,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code28 a b c) := by decide +kernel
theorem closed28 : let S : Finset Nat := {15,4593,8738,53196,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked28 a ha b hb ne c hc hn) ok
def code29 : Nat → Nat → Nat → Nat := pick [207,3840,4369,8738,61440] [0,0,4,42,21,4,4,21,4,29,4,42,0,0,149,132,132,149,132,157,21,4,149,132,0,0,138,205,138,196,4,21,132,149,138,205,0,0,154,286,4,29,132,157,138,196,154,286,0,0]
theorem checked29 : let S : Finset Nat := {207,3840,4369,8738,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code29 a b c) := by decide +kernel
theorem closed29 : let S : Finset Nat := {207,3840,4369,8738,61440}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked29 a ha b hb ne c hc hn) ok
def code30 : Nat → Nat → Nat → Nat := pick [207,3840,4369,61986] [0,0,4,42,21,4,4,21,4,42,0,0,149,132,132,149,21,4,149,132,0,0,138,196,4,21,132,149,138,196,0,0]
theorem checked30 : let S : Finset Nat := {207,3840,4369,61986}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → test S a b c (code30 a b c) := by decide +kernel
theorem closed30 : let S : Finset Nat := {207,3840,4369,61986}; ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  intro S a ha b hb ne c hc hn ok
  exact test_ok (checked30 a ha b hb ne c hc hn) ok
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
theorem closed (S : Finset Nat) (hs : S∈family) : ∀ a∈S,∀ b∈S,a≠b → ∀ c∈[a &&& b,a ||| b],c∉S → good (merge S a b c) → merge S a b c∈family := by
  simp only [family,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact closed0
  · exact closed1
  · exact closed2
  · exact closed3
  · exact closed4
  · exact closed5
  · exact closed6
  · exact closed7
  · exact closed8
  · exact closed9
  · exact closed10
  · exact closed11
  · exact closed12
  · exact closed13
  · exact closed14
  · exact closed15
  · exact closed16
  · exact closed17
  · exact closed18
  · exact closed19
  · exact closed20
  · exact closed21
  · exact closed22
  · exact closed23
  · exact closed24
  · exact closed25
  · exact closed26
  · exact closed27
  · exact closed28
  · exact closed29
  · exact closed30

def cert (P : Finset Nat) (k : Nat) := ∃ S⊆P, good S ∧ S.card≤k+1 ∧ (S.card=k+1 → S∉family)
theorem liftGood {S W : Finset Nat} (h : S⊆W) (ok : good S) : good W := by
  intro p q hp hq
  obtain ⟨v,hv,one,zero⟩ := ok p q hp hq
  exact ⟨v,h hv,one,zero⟩
theorem unchanged {P Q : Finset Nat} {k : Nat} (sub : Q⊆P) (h : cert Q k) : cert P (k+1) := by
  obtain ⟨S,hS,ok,sz,_⟩ := h
  exact ⟨S,hS.trans sub,ok,by omega,by omega⟩
-- Expanding one used gate backwards adds at most one wire. Equality forces two fresh operands.
theorem back {P : Finset Nat} {k c a b : Nat} (ha : a∈P) (hb : b∈P)
    (op : c=a &&& b ∨ c=a ||| b) (h : cert (insert c P) k) : cert P (k+1) := by
  by_cases old : c∈P
  · rw [Finset.insert_eq_of_mem old] at h
    exact unchanged (fun _ m => m) h
  obtain ⟨S,sub,ok,sz,escape⟩ := h
  by_cases used : c∈S
  · let R := S.erase c
    let V := insert a (insert b R)
    have rsub : R⊆P := by
      intro z hz
      exact (Finset.mem_insert.mp (sub (Finset.mem_of_mem_erase hz))).resolve_left (Finset.ne_of_mem_erase hz)
    have vsub : V⊆P := Finset.insert_subset ha (Finset.insert_subset hb rsub)
    have goodV : good V := by
      intro p q hp hq
      obtain ⟨v,hv,x,y⟩ := ok p q hp hq
      by_cases e : v=c
      · subst v
        have A : a∈V := Finset.mem_insert_self _ _
        have B : b∈V := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        rcases op with rfl|rfl
        · simp only [Nat.testBit_and,Bool.and_eq_true] at x y
          cases e : a.testBit q with
          | false => exact ⟨a,A,x.1,e⟩
          | true => exact ⟨b,B,x.2,by simpa [e] using y⟩
        · simp only [Nat.testBit_or,Bool.or_eq_false_iff] at x y
          rcases (show a.testBit p=true ∨ b.testBit p=true by simpa only [Bool.or_eq_true] using x) with l|r
          · exact ⟨a,A,l,y.1⟩
          · exact ⟨b,B,r,y.2⟩
      · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨e,hv⟩)),x,y⟩
    have rc : R.card+1=S.card := Finset.card_erase_add_one used
    have v1 := Finset.card_insert_le a (insert b R)
    have v2 := Finset.card_insert_le b R
    refine ⟨V,vsub,goodV,by dsimp [V];omega,?_⟩
    intro tight blocked
    have t : (insert a (insert b R)).card=k+2 := tight
    have ab : a≠b := by rintro rfl;simp only [Finset.insert_idem] at t;omega
    have an : a∉R := by
      intro inR
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem inR)] at t
      omega
    have bn : b∉R := by
      intro inR
      rw [Finset.insert_eq_of_mem inR] at t
      have := Finset.card_insert_le a R
      omega
    have ea : V.erase a=insert b R := Finset.erase_insert (by simp [ab,an])
    have eb : (insert b R).erase b=R := Finset.erase_insert bn
    have recov : merge V a b c=S := by rw [merge,ea,eb];exact Finset.insert_erase used
    have fam := closed V blocked a (Finset.mem_insert_self ..) b
      (Finset.mem_insert_of_mem (Finset.mem_insert_self ..)) ab c (by simpa using op)
      (fun hm => old (vsub hm)) (recov ▸ ok)
    exact escape (by omega) (recov ▸ fam)
  · have hsub : S⊆P := by
      intro z hz
      exact (Finset.mem_insert.mp (sub hz)).resolve_left (fun e => used (e ▸ hz))
    exact ⟨S,hsub,ok,by omega,by omega⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
theorem work (gs : List Gate) (pool : List Nat) (ws : Fin 16 → List Bool) (L o : Nat)
    (mono : ∀ g∈gs,g.op∈({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2)
    (len : ∀ p,(ws p).length=L) (inv : Inv pool ws)
    (hout : ∀ p : Fin 16,(gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (ws p)).getD o false=(5071 : Nat).testBit p) : cert (insert 65535 (insert 0 pool.toFinset)) gs.length := by
  induction gs generalizing pool ws L with
  | nil =>
    obtain ⟨m,hm,val⟩ := inv o
    refine ⟨{m},Finset.singleton_subset_iff.mpr (by simp [hm]),?_,by simp,?_⟩
    · intro p q hp hq
      exact ⟨m,by simp,(val p).trans ((hout p).trans hp),(val q).trans ((hout q).trans hq)⟩
    · intro _ bad
      have := noSingle _ bad
      simpa using this
  | cons g gs ih =>
    obtain ⟨ops,arity⟩ := mono g (by simp)
    obtain ⟨c,hc,hval⟩ := gate_vec pool ws inv g ops arity
    have nxt := ih (pool ++ [c]) (fun p => ws p ++ [g.op.eval (g.inputs.map fun i => (ws p).getD i false)]) (L+1)
      (fun u hu => mono u (by simp [hu])) (fun p => by simp [len p])
      (inv_step pool (pool ++ [c]) ws L len inv _ c hval (fun u hu => by simp [hu]) (by simp))
      (fun p => hout p)
    let P := insert 65535 (insert 0 pool.toFinset)
    have eq : insert 65535 (insert 0 (pool++[c]).toFinset)=insert c P := by ext z;simp [P];tauto
    rw [eq] at nxt
    change cert P (gs.length+1)
    simp only [stepC,List.mem_cons,List.mem_append,List.mem_flatMap,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|old|⟨a,ha,b,hb,op⟩
    · exact unchanged (by simp [P]) nxt
    · exact unchanged (by simp [P]) nxt
    · exact unchanged (Finset.insert_subset (by simp [P,old]) (Finset.Subset.refl _)) nxt
    · exact back (by simp [P,ha]) (by simp [P,hb]) op nxt
theorem lower : ¬RepSizeAtMost (fun u v : Fin 4 => (5071 : Nat).testBit (4*u.val+v.val)) 7 := by
  rintro ⟨C,mono,sz,rep⟩
  obtain ⟨S,sub,ok,num,esc⟩ := work C.gates pool0 X 8 C.output mono X_len inv0 (fun p => by
    have h := rep ⟨p.val / 4,by omega⟩ ⟨p.val % 4,by omega⟩
    exact h.trans (congrArg (Nat.testBit 5071) (Nat.div_add_mod p.val 4)))
  have sub' : S⊆inputs := by simpa [inputs,pool0] using sub
  have bsub : base⊆S := by
    intro a ha
    by_contra miss
    exact necessary a ha (liftGood (fun x hx => Finset.mem_erase.mpr ⟨fun e => miss (e ▸ hx),sub' hx⟩) ok)
  have count := Finset.card_le_card bsub
  have eqsize := baseCard
  change C.gates.length≤7 at sz
  have eq : base=S := Finset.eq_of_subset_of_card_le bsub (by omega)
  exact esc (by omega) (eq ▸ initial)

end PEqualNP.Outside.L_meta_6058

theorem PEqualNP.Outside.L_meta_6058 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (5071 : ℕ).testBit (4 * u.val + v.val)) 8 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (5071 : ℕ).testBit (4 * u.val + v.val)) 7 := by
  exact ⟨PEqualNP.Outside.L_meta_6058.upper, PEqualNP.Outside.L_meta_6058.lower⟩
