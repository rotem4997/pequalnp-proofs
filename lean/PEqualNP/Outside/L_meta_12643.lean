import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12643_aux

-- Generated proof. The three libraries below are copied from merged files of this repository (Apache-2.0):
--   namespace S = search `s0`/`s1` and theorem `final`: PEqualNP/Outside/L_meta_5453.lean
--   namespace K = K4 needs 7 gates, `excludeTwo`: PEqualNP/Outside/L_meta_5446.lean
--   namespace E = `relabel_size`, `one_gate_at`, `gate_elim_at`: PEqualNP/Outside/L_meta_5481.lean

namespace S

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



def rho (n d i : ℕ) : ℕ := if i < n + d then i else i - 1

def fx (n d L j i : ℕ) : ℕ := if i < n + j then rho n d i else n + L

def ng (n : ℕ) (gs : List Gate) (d : ℕ) : List Gate :=
  List.ofFn fun k : Fin (gs.length - 1) =>
    let j := if k.val < d then k.val else k.val + 1
    let h := gs.getD j ⟨GateOp.or, []⟩
    ⟨h.op, h.inputs.map (fx n d gs.length j)⟩

theorem ng_len (n : ℕ) (gs : List Gate) (d : ℕ) : (ng n gs d).length = gs.length - 1 := by
  simp [ng]

theorem sem (n : ℕ) (gs : List Gate) (d : ℕ) (hd : d < gs.length)
    (hno : ∀ (j : ℕ) (hj : j < gs.length), d < j → n + d ∉ gs[j].inputs)
    (x : List Bool) (hx : x.length = n) :
    ∀ w, w < n + gs.length → w ≠ n + d →
      (run (ng n gs d) x).getD (rho n d w) false = (run gs x).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hwd
    by_cases h9 : w < n
    · rw [rho, if_pos (by omega), run_input _ _ _ (by omega), run_input _ _ _ (by omega)]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < gs.length := by omega
      have old := run_gate gs x j hj
      rw [hx] at old
      rw [old]
      obtain ⟨k, hkj, hkL, hr⟩ : ∃ k, (if k < d then k else k + 1) = j ∧
          k < gs.length - 1 ∧ rho n d (n + j) = n + k := by
        by_cases h : j < d
        · exact ⟨j, by rw [if_pos h], by omega, by unfold rho; split_ifs <;> omega⟩
        · exact ⟨j - 1, by rw [if_neg (by omega)]; omega, by omega, by
            unfold rho; split_ifs <;> omega⟩
      have new := run_gate (ng n gs d) x k (by rw [ng_len]; omega)
      rw [hx] at new
      have e : (ng n gs d)[k]'(by rw [ng_len]; omega) =
          ⟨gs[j].op, gs[j].inputs.map (fx n d gs.length j)⟩ := by
        have hgd : gs.getD j ⟨GateOp.or, []⟩ = gs[j] := List.getD_eq_getElem _ _ hj
        simp only [ng, List.getElem_ofFn, hkj, hgd]
      rw [hr, new, e, List.map_map]
      refine congrArg _ (List.map_congr_left fun i hi => ?_)
      simp only [Function.comp]
      by_cases hij : i < n + j
      · have hne : i ≠ n + d := by
          rintro rfl
          exact hno j hj (by omega) hi
        have hlt : rho n d i < n + k := by
          by_cases hkd : k < d
          · rw [if_pos hkd] at hkj
            unfold rho; split_ifs <;> omega
          · rw [if_neg hkd] at hkj
            unfold rho; split_ifs <;> omega
        have hfx : fx n d gs.length j i = rho n d i := if_pos hij
        rw [hfx, if_pos hlt, if_pos hij]
        exact ih i hij (by omega) hne
      · have hfx : fx n d gs.length j i = n + gs.length := if_neg hij
        rw [hfx, if_neg hij, if_neg (by omega)]

theorem del (n : ℕ) (C : Circuit) (hC : FanInTwo C) (d : ℕ) (hd : d < C.gates.length)
    (hno : ∀ (j : ℕ) (hj : j < C.gates.length), d < j → n + d ∉ C.gates[j].inputs)
    (ho : C.output ≠ n + d) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 1 = C.size ∧ circuitFun n D = circuitFun n C := by
  let o := if C.output < n + C.gates.length then rho n d C.output else n + C.gates.length
  refine ⟨⟨ng n C.gates d, o⟩, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hh
    have hj : (if k.val < d then k.val else k.val + 1) < C.gates.length := by
      have := k.isLt
      split_ifs <;> omega
    dsimp only
    rw [List.getD_eq_getElem _ _ hj]
    have := hC _ (List.getElem_mem hj)
    exact ⟨this.1, by simpa using this.2⟩
  · change (ng n C.gates d).length + 1 = C.gates.length
    rw [ng_len]; omega
  · funext x
    change (run (ng n C.gates d) (List.ofFn x)).getD o false =
      (run C.gates (List.ofFn x)).getD C.output false
    by_cases h : C.output < n + C.gates.length
    · simp only [o, if_pos h]
      exact sem n _ d hd hno _ (by simp) _ h ho
    · simp only [o, if_neg h]
      rw [List.getD_eq_default _ _ (by rw [run_length, ng_len, List.length_ofFn]; omega),
        List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)]





def rds (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

theorem eval_congr (g : Gate) (u v : ℕ → Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (huv : ∀ i ∈ rds g, u i = v i) : g.op.eval (g.inputs.map u) = g.op.eval (g.inputs.map v) := by
  rcases hop with h | h | h
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [h]
    cases hi : g.inputs with
    | nil => rfl
    | cons a t =>
      have := huv a (by simp [hi])
      simp [GateOp.eval, this]

theorem getD_sn (l : List Bool) (b : Bool) (t : ℕ) :
    (l ++ [b]).getD t false = if t = l.length then b else l.getD t false := by
  rcases lt_trichotomy t l.length with h | h | h
  · rw [if_neg (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem indep (v : ℕ) (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hno : ∀ g ∈ gs, v ∉ rds g) (x y : List Bool) (hl : x.length = y.length)
    (hxy : ∀ i, i ≠ v → x.getD i false = y.getD i false) :
    ∀ i, i ≠ v → (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simpa [run] using hxy
  | append_singleton gs g ih =>
    have ih' := ih (fun g' h => hop g' (by simp [h])) (fun g' h => hno g' (by simp [h]))
    intro i hi
    have e : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) =
        g.op.eval (g.inputs.map fun i => (run gs y).getD i false) :=
      eval_congr g _ _ (hop g (by simp)) fun k hk =>
        ih' k fun hc => hno g (by simp) (hc ▸ hk)
    rw [run_snoc, run_snoc, getD_sn, getD_sn, run_length, run_length, hl, e]
    split_ifs
    · rfl
    · exact ih' i hi


def fn (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 ||
    x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def X0 (u t : Fin 9) : Fin 9 → Bool := fun i => decide (i = u) || decide (i = t)

def X1 (u t v : Fin 9) : Fin 9 → Bool := fun i => decide (i = u) || decide (i = t) || decide (i = v)

def picks : List ℕ → List (ℕ × List ℕ)
  | [] => []
  | a :: l => (a, l) :: (picks l).map fun q => (q.1, a :: q.2)

theorem picks_mem (V : ℕ → ℕ) : ∀ (U : List ℕ) (i : ℕ), i ∈ U → (V i, (U.erase i).map V) ∈ picks (U.map V)
  | [], i, h => by simp at h
  | a :: l, i, h => by
    by_cases e : i = a
    · subst e; simp [picks]
    · have hi : i ∈ l := by simpa [e] using h
      have := picks_mem V l i hi
      rw [List.erase_cons_tail (by simpa using fun h' : a = i => e h'.symm)]
      simp only [picks, List.map_cons, List.mem_cons, List.mem_map]
      exact Or.inr ⟨_, this, rfl⟩

def detc (F t : ℕ) : List ℕ → ℕ → Bool
  | [], m => (t &&& m == 0) || (t &&& m == m)
  | a :: l, m => detc F t l (m &&& a) && detc F t l (m &&& (F ^^^ a))

def s0 (F t : ℕ) : ℕ → List ℕ → Bool
  | 0, us => us == [t]
  | r + 1, us => detc F t us F && (picks us).any fun q => (picks q.2).any fun p =>
      s0 F t r ((q.1 &&& p.1) :: p.2) || s0 F t r ((q.1 ||| p.1) :: p.2)

def s1 (F t : ℕ) : ℕ → List ℕ → List ℕ → Bool
  | 0, _, _ => false
  | r + 1, W, us => ((0 :: W).any fun w => detc F t (w :: us) F) && (picks us).any fun q =>
      ((picks q.2).any fun p =>
        s1 F t r ((q.1 &&& p.1) :: W) ((q.1 &&& p.1) :: p.2) ||
        s1 F t r ((q.1 ||| p.1) :: W) ((q.1 ||| p.1) :: p.2)) ||
      ((0 :: W).any fun w => s0 F t r ((q.1 &&& w) :: q.2) || s0 F t r ((q.1 ||| w) :: q.2)) ||
      s0 F t r ((F ^^^ q.1) :: q.2)

def Det (N t : ℕ) (us : List ℕ) : Prop :=
  ∀ p < N, ∀ q < N, (∀ a ∈ us, a.testBit p = a.testBit q) → t.testBit p = t.testBit q

theorem full_bit (N p : ℕ) (hp : p < N) : (2 ^ N - 1).testBit p = true := by
  rw [Nat.testBit_two_pow_sub_one]; simpa using hp

theorem eqN {N a b : ℕ} (ha : a < 2 ^ N) (hb : b < 2 ^ N)
    (h : ∀ p < N, a.testBit p = b.testBit p) : a = b := by
  refine Nat.eq_of_testBit_eq fun p => ?_
  by_cases hp : p < N
  · exact h p hp
  · have e : 2 ^ N ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem detc_of (N t : ℕ) : ∀ (us : List ℕ) (m : ℕ), m < 2 ^ N →
    (∀ p q, m.testBit p = true → m.testBit q = true → (∀ a ∈ us, a.testBit p = a.testBit q) →
      t.testBit p = t.testBit q) → detc (2 ^ N - 1) t us m = true
  | [], m, hm, h => by
    simp only [detc, Bool.or_eq_true, beq_iff_eq]
    by_cases hx : ∃ p, m.testBit p = true ∧ t.testBit p = true
    · obtain ⟨p, hp, htp⟩ := hx
      right
      refine Nat.eq_of_testBit_eq fun q => ?_
      rw [Nat.testBit_and]
      cases hq : m.testBit q with
      | false => simp
      | true => rw [← h p q hp hq (by simp), htp]; rfl
    · left
      refine Nat.eq_of_testBit_eq fun q => ?_
      rw [Nat.testBit_and, Nat.zero_testBit]
      cases hq : m.testBit q with
      | false => simp
      | true =>
        cases hq' : t.testBit q with
        | false => rfl
        | true => exact absurd ⟨q, hq, hq'⟩ hx
  | a :: l, m, hm, h => by
    simp only [detc, Bool.and_eq_true]
    constructor
    · refine detc_of N t l _ (lt_of_le_of_lt Nat.and_le_left hm) fun p q hp hq hl => ?_
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hq
      refine h p q hp.1 hq.1 fun b hb => ?_
      rcases List.mem_cons.1 hb with rfl | hb
      · rw [hp.2, hq.2]
      · exact hl b hb
    · refine detc_of N t l _ (lt_of_le_of_lt Nat.and_le_left hm) fun p q hp hq hl => ?_
      rw [Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true] at hp hq
      have lt : ∀ p, m.testBit p = true → p < N := by
        intro p hp
        by_contra hge
        have e : 2 ^ N ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) (by omega)
        rw [Nat.testBit_lt_two_pow (by omega)] at hp; cases hp
      refine h p q hp.1 hq.1 fun b hb => ?_
      rcases List.mem_cons.1 hb with rfl | hb
      · have e1 := hp.2
        have e2 := hq.2
        rw [full_bit N p (lt p hp.1)] at e1
        rw [full_bit N q (lt q hq.1)] at e2
        revert e1 e2
        cases b.testBit p <;> cases b.testBit q <;> simp
      · exact hl b hb

theorem detc_full {N t : ℕ} {us : List ℕ} (h : Det N t us) :
    detc (2 ^ N - 1) t us (2 ^ N - 1) = true := by
  have hN : 0 < 2 ^ N := Nat.two_pow_pos N
  refine detc_of N t us _ (by omega) fun p q hp hq hl => ?_
  rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq] at hp hq
  exact h p hp q hq hl

def Wl (n : ℕ) (V : ℕ → ℕ) : ℕ → List ℕ
  | 0 => (List.range n).map V
  | k + 1 => V (n + k) :: Wl n V k

theorem Wl_mem (n : ℕ) (V : ℕ → ℕ) : ∀ k i, i < n + k → V i ∈ Wl n V k
  | 0, i, h => by
    simp only [Wl, List.mem_map, List.mem_range]
    exact ⟨i, by omega, rfl⟩
  | k + 1, i, h => by
    by_cases e : i = n + k
    · subst e; simp [Wl]
    · exact List.mem_cons_of_mem _ (Wl_mem n V k i (by omega))

theorem search (N n m o t : ℕ) (V : ℕ → ℕ) (R : ℕ → List ℕ) (ho : V o = t)
    (Hu : ∀ k < m, n + k = o ∨ ∃ j, k + 1 ≤ j ∧ j < m ∧ n + k ∈ R j)
    (hG : ∀ j < m, (∃ i i', R j = [i, i'] ∧
        (V (n + j) = (if i < n + j then V i else 0) &&& (if i' < n + j then V i' else 0) ∨
         V (n + j) = (if i < n + j then V i else 0) ||| (if i' < n + j then V i' else 0))) ∨
      (∃ i, R j = [i] ∧ (V (n + j) = (if i < n + j then V i else 0) ∨
         V (n + j) = (2 ^ N - 1) ^^^ (if i < n + j then V i else 0))) ∨ R j = []) :
    ∀ r k (U : List ℕ), k + r = m → U.Nodup →
      (∀ i ∈ U, i < n + k ∧ (i = o ∨ ∃ j, k ≤ j ∧ j < m ∧ i ∈ R j)) →
      U.length ≤ r + 1 ∧
      (U.length = r + 1 → s0 (2 ^ N - 1) t r (U.map V) = true ∧ Det N t (U.map V)) ∧
      (U.length = r → U ≠ [] → s1 (2 ^ N - 1) t r (Wl n V k) (U.map V) = true ∧
        ∃ w ∈ 0 :: Wl n V k, Det N t (w :: U.map V)) := by
  intro r
  induction r with
  | zero =>
    intro k U hk hnd hU
    have all : ∀ i ∈ U, i = o := by
      intro i hi
      rcases (hU i hi).2 with h | ⟨j, h1, h2, _⟩
      · exact h
      · omega
    have hlen : U.length ≤ 1 := by
      rcases U with _ | ⟨a, _ | ⟨b, l⟩⟩
      · simp
      · simp
      · exfalso
        have e1 := all a (by simp)
        have e2 := all b (by simp)
        rw [e1, e2] at hnd
        simp at hnd
    refine ⟨by omega, fun h1 => ?_, fun h0 hne => absurd (List.length_eq_zero_iff.1 h0) hne⟩
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 h1
    have e := all a (by simp)
    subst e
    refine ⟨by simp [s0, ho], fun p _ q _ h => ?_⟩
    have := h (V a) (by simp)
    rw [ho] at this; exact this
  | succ r ih =>
    intro k U hk hnd hU
    have hkm : k < m := by omega
    set v := V (n + k) with hv
    -- one step with the list of unread wires U'
    have step : ∀ U' : List ℕ, U'.Nodup → (∀ i ∈ U', i ∈ U ∧ i ∉ R k) →
        ((U'.length + 1 ≤ r + 1) ∧
        (U'.length + 1 = r + 1 → s0 (2 ^ N - 1) t r (v :: U'.map V) = true ∧ Det N t (v :: U'.map V)) ∧
        (U'.length + 1 = r → s1 (2 ^ N - 1) t r (v :: Wl n V k) (v :: U'.map V) = true ∧
          ∃ w ∈ 0 :: v :: Wl n V k, Det N t (w :: v :: U'.map V))) := by
      intro U' hnd' hU'
      have := ih (k + 1) ((n + k) :: U') (by omega) (by
        rw [List.nodup_cons]
        refine ⟨fun h => ?_, hnd'⟩
        have := (hU _ (hU' _ h).1).1
        omega) (by
        intro i hi
        rcases List.mem_cons.1 hi with rfl | hi
        · exact ⟨by omega, Hu k hkm⟩
        · obtain ⟨h1, h2⟩ := hU' i hi
          obtain ⟨h3, h4⟩ := hU i h1
          refine ⟨by omega, ?_⟩
          rcases h4 with h4 | ⟨j, h4, h5, h6⟩
          · exact Or.inl h4
          · right
            refine ⟨j, ?_, h5, h6⟩
            rcases Nat.lt_or_ge k j with h | h
            · omega
            · have : j = k := by omega
              rw [this] at h6; exact absurd h6 h2)
      obtain ⟨q1, q2, q3⟩ := this
      refine ⟨by simpa using q1, fun h => ?_, fun h => ?_⟩
      · exact q2 (by simpa using h)
      · exact q3 (by simpa using h) (by simp)
    have hlenE : ∀ i ∈ U, (U.erase i).length + 1 = U.length := by
      intro i hi
      rw [List.length_erase_of_mem hi]
      have := List.length_pos_of_mem hi
      omega
    have c0 : (∀ x ∈ U, x ∉ R k) → U.length ≤ r := by
      intro h
      have := (step U hnd fun i hi => ⟨hi, h i hi⟩).1
      omega
    have c1 : ∀ i ∈ U, (∀ x ∈ U, x ∈ R k → x = i) →
        ((∃ w ∈ 0 :: Wl n V k, v = V i &&& w ∨ v = V i ||| w) ∨ v = (2 ^ N - 1) ^^^ V i) →
        U.length ≤ r + 1 ∧ (U.length = r + 1 →
          s1 (2 ^ N - 1) t (r + 1) (Wl n V k) (U.map V) = true ∧
          ∃ w ∈ 0 :: Wl n V k, Det N t (w :: U.map V)) := by
      intro i hi h1 hval
      obtain ⟨q1, q2, _⟩ := step (U.erase i) (hnd.erase i) (by
        intro x hx
        obtain ⟨hxi, hxU⟩ := (hnd.mem_erase_iff).1 hx
        exact ⟨hxU, fun hR => hxi (h1 x hxU hR)⟩)
      have hl := hlenE i hi
      refine ⟨by omega, fun hlen => ?_⟩
      obtain ⟨s, d⟩ := q2 (by omega)
      have hmem := picks_mem V U i hi
      have hat : ∀ w, (v = V i &&& w ∨ v = V i ||| w) → Det N t (w :: U.map V) := by
        intro w hw p hp q hq hall
        refine d p hp q hq fun a ha => ?_
        have hw1 := hall w (by simp)
        have hi1 := hall (V i) (List.mem_cons_of_mem _ (List.mem_map_of_mem hi))
        rcases List.mem_cons.1 ha with rfl | ha
        · rcases hw with e | e <;> rw [e]
          · rw [Nat.testBit_and, Nat.testBit_and, hw1, hi1]
          · rw [Nat.testBit_or, Nat.testBit_or, hw1, hi1]
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
          exact hall _ (List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_of_mem_erase hx)))
      have hdet : ∃ w ∈ 0 :: Wl n V k, Det N t (w :: U.map V) := by
        rcases hval with ⟨w, hw, e⟩ | e
        · exact ⟨w, hw, hat w e⟩
        · refine ⟨0, by simp, fun p hp q hq hall => d p hp q hq fun a ha => ?_⟩
          have hi1 := hall (V i) (List.mem_cons_of_mem _ (List.mem_map_of_mem hi))
          rcases List.mem_cons.1 ha with rfl | ha
          · rw [e, Nat.testBit_xor, Nat.testBit_xor, hi1, full_bit N p hp, full_bit N q hq]
          · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
            exact hall _ (List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_of_mem_erase hx)))
      refine ⟨?_, hdet⟩
      simp only [s1, Bool.and_eq_true, List.any_eq_true]
      obtain ⟨w0, hw0, hd0⟩ := hdet
      refine ⟨⟨w0, hw0, detc_full hd0⟩, _, hmem, ?_⟩
      simp only [Bool.or_eq_true, List.any_eq_true]
      rcases hval with ⟨w, hw, e | e⟩ | e
      · exact Or.inl (Or.inr ⟨w, hw, Or.inl (by rw [← e]; exact s)⟩)
      · exact Or.inl (Or.inr ⟨w, hw, Or.inr (by rw [← e]; exact s)⟩)
      · exact Or.inr (by rw [← e]; exact s)
    have c2 : ∀ i ∈ U, ∀ i' ∈ U, i ≠ i' → (∀ x ∈ R k, x = i ∨ x = i') →
        (v = V i &&& V i' ∨ v = V i ||| V i') →
        U.length ≤ r + 2 ∧
        (U.length = r + 2 → s0 (2 ^ N - 1) t (r + 1) (U.map V) = true ∧ Det N t (U.map V)) ∧
        (U.length = r + 1 → s1 (2 ^ N - 1) t (r + 1) (Wl n V k) (U.map V) = true ∧
          ∃ w ∈ 0 :: Wl n V k, Det N t (w :: U.map V)) := by
      intro i hi i' hi' hne hR hval
      have hi2 : i' ∈ U.erase i := (hnd.mem_erase_iff).2 ⟨hne.symm, hi'⟩
      have hl := hlenE i hi
      have hl2 : ((U.erase i).erase i').length + 1 = (U.erase i).length := by
        rw [List.length_erase_of_mem hi2]
        have := List.length_pos_of_mem hi2
        omega
      obtain ⟨q1, q2, q3⟩ := step ((U.erase i).erase i') ((hnd.erase i).erase i') (by
        intro x hx
        obtain ⟨h1, h2⟩ := ((hnd.erase i).mem_erase_iff).1 hx
        obtain ⟨h3, h4⟩ := (hnd.mem_erase_iff).1 h2
        exact ⟨h4, fun hR' => (hR x hR').elim h3 h1⟩)
      have m1 := picks_mem V U i hi
      have m2 := picks_mem V (U.erase i) i' hi2
      have sub : ∀ a ∈ ((U.erase i).erase i').map V, a ∈ U.map V := by
        intro a ha
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
        exact List.mem_map_of_mem (List.mem_of_mem_erase (List.mem_of_mem_erase hx))
      have vagree : ∀ p q : ℕ, (∀ a ∈ U.map V, a.testBit p = a.testBit q) →
          v.testBit p = v.testBit q := by
        intro p q hall
        have e1 := hall (V i) (List.mem_map_of_mem hi)
        have e2 := hall (V i') (List.mem_map_of_mem hi')
        rcases hval with e | e <;> rw [e]
        · rw [Nat.testBit_and, Nat.testBit_and, e1, e2]
        · rw [Nat.testBit_or, Nat.testBit_or, e1, e2]
      refine ⟨by omega, fun hlen => ?_, fun hlen => ?_⟩
      · obtain ⟨s, d⟩ := q2 (by omega)
        have hd : Det N t (U.map V) := by
          intro p hp q hq hall
          refine d p hp q hq fun a ha => ?_
          rcases List.mem_cons.1 ha with rfl | ha
          · exact vagree p q hall
          · exact hall a (sub a ha)
        refine ⟨?_, hd⟩
        simp only [s0, Bool.and_eq_true, List.any_eq_true, Bool.or_eq_true]
        refine ⟨detc_full hd, _, m1, _, m2, ?_⟩
        rcases hval with e | e
        · left; rw [← e]; exact s
        · right; rw [← e]; exact s
      · obtain ⟨s, w, hw, d⟩ := q3 (by omega)
        have hdet : ∃ w ∈ 0 :: Wl n V k, Det N t (w :: U.map V) := by
          have mk : ∀ w', (∀ p q : ℕ, (∀ a ∈ U.map V, a.testBit p = a.testBit q) →
              (w'.testBit p = w'.testBit q) → w.testBit p = w.testBit q) → Det N t (w' :: U.map V) := by
            intro w' hw' p hp q hq hall
            have hall' : ∀ a ∈ U.map V, a.testBit p = a.testBit q := fun a ha =>
              hall a (List.mem_cons_of_mem _ ha)
            refine d p hp q hq fun a ha => ?_
            rcases List.mem_cons.1 ha with rfl | ha
            · exact hw' p q hall' (hall w' (by simp))
            rcases List.mem_cons.1 ha with rfl | ha
            · exact vagree p q hall'
            · exact hall' a (sub a ha)
          rcases List.mem_cons.1 hw with rfl | hw
          · exact ⟨0, by simp, mk 0 fun _ _ _ h => h⟩
          rcases List.mem_cons.1 hw with rfl | hw
          · exact ⟨0, by simp, mk 0 fun p q h _ => vagree p q h⟩
          · exact ⟨w, List.mem_cons_of_mem _ hw, mk w fun _ _ _ h => h⟩
        refine ⟨?_, hdet⟩
        obtain ⟨w0, hw0, hd0⟩ := hdet
        simp only [s1, Bool.and_eq_true, List.any_eq_true]
        refine ⟨⟨w0, hw0, detc_full hd0⟩, _, m1, ?_⟩
        simp only [Bool.or_eq_true, List.any_eq_true]
        refine Or.inl (Or.inl ⟨_, m2, ?_⟩)
        rcases hval with e | e
        · left; rw [← e]; exact s
        · right; rw [← e]; exact s
    -- from the three counts
    have w_mem : ∀ i, (if i < n + k then V i else 0) ∈ 0 :: Wl n V k := by
      intro i
      split_ifs with h
      · exact List.mem_cons_of_mem _ (Wl_mem n V k i h)
      · simp
    have f0 : (∀ x ∈ U, x ∉ R k) → U.length ≤ r + 1 + 1 ∧
        (U.length = r + 1 + 1 → s0 (2 ^ N - 1) t (r + 1) (U.map V) = true ∧ Det N t (U.map V)) ∧
        (U.length = r + 1 → U ≠ [] → s1 (2 ^ N - 1) t (r + 1) (Wl n V k) (U.map V) = true ∧
          ∃ w ∈ 0 :: Wl n V k, Det N t (w :: U.map V)) := by
      intro h
      have := c0 h
      exact ⟨by omega, fun h => by omega, fun h => by omega⟩
    have f1 : ∀ i ∈ U, (∀ x ∈ U, x ∈ R k → x = i) →
        ((∃ w ∈ 0 :: Wl n V k, v = V i &&& w ∨ v = V i ||| w) ∨ v = (2 ^ N - 1) ^^^ V i) →
        U.length ≤ r + 1 + 1 ∧
        (U.length = r + 1 + 1 → s0 (2 ^ N - 1) t (r + 1) (U.map V) = true ∧ Det N t (U.map V)) ∧
        (U.length = r + 1 → U ≠ [] → s1 (2 ^ N - 1) t (r + 1) (Wl n V k) (U.map V) = true ∧
          ∃ w ∈ 0 :: Wl n V k, Det N t (w :: U.map V)) := by
      intro i hi h1 hval
      obtain ⟨q1, q2⟩ := c1 i hi h1 hval
      exact ⟨by omega, fun h => by omega, fun h _ => q2 h⟩
    rcases hG k hkm with ⟨i, i', hR, hval⟩ | ⟨i, hR, hval⟩ | hR
    · by_cases hi : i ∈ U
      · have hi' := (hU i hi).1
        rw [if_pos hi'] at hval
        by_cases h2 : i' ∈ U ∧ i ≠ i'
        · have hi2 := (hU i' h2.1).1
          rw [if_pos hi2] at hval
          obtain ⟨q1, q2, q3⟩ := c2 i hi i' h2.1 h2.2 (by rw [hR]; simp) hval
          exact ⟨q1, q2, fun h _ => q3 h⟩
        · refine f1 i hi ?_ (Or.inl ⟨_, w_mem i', hval⟩)
          intro x hx hxR
          rw [hR] at hxR
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hxR
          rcases hxR with rfl | rfl
          · rfl
          · by_contra hne
            exact h2 ⟨hx, fun h => hne h.symm⟩
      · by_cases hi' : i' ∈ U
        · have hlt := (hU i' hi').1
          rw [if_pos hlt] at hval
          refine f1 i' hi' ?_ (Or.inl ⟨_, w_mem i, ?_⟩)
          · intro x hx hxR
            rw [hR] at hxR
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hxR
            rcases hxR with rfl | rfl
            · exact absurd hx hi
            · rfl
          · rcases hval with e | e
            · left; rw [Nat.and_comm]; exact e
            · right; rw [Nat.or_comm]; exact e
        · refine f0 fun x hx hxR => ?_
          rw [hR] at hxR
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hxR
          rcases hxR with rfl | rfl
          · exact hi hx
          · exact hi' hx
    · by_cases hi : i ∈ U
      · rw [if_pos (hU i hi).1] at hval
        refine f1 i hi ?_ ?_
        · intro x _ hxR
          rw [hR] at hxR
          simpa using hxR
        · rcases hval with e | e
          · exact Or.inl ⟨0, by simp, Or.inr (by rw [Nat.or_zero]; exact e)⟩
          · exact Or.inr e
      · refine f0 fun x hx hxR => ?_
        rw [hR] at hxR
        have : x = i := by simpa using hxR
        exact hi (this ▸ hx)
    · exact f0 fun x _ hxR => by rw [hR] at hxR; simp at hxR

/-- `not` gates read one wire -/
def nrm (g : Gate) : Gate := ⟨g.op, rds g⟩

theorem nrm_run (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) (x : List Bool) :
    run (gs.map nrm) x = run gs x := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [List.map_append, List.map_singleton, run_snoc, run_snoc,
      ih fun g' h => hop g' (by simp [h])]
    congr 2
    rcases hop g (by simp) with h | h | h
    · simp [nrm, rds, h]
    · simp [nrm, rds, h]
    · rcases g with ⟨o, l⟩
      simp only at h
      subst h
      rcases l with _ | ⟨a, l⟩ <;> simp [nrm, rds, GateOp.eval]

def X (n p : ℕ) : List Bool := List.ofFn fun i : Fin n => p.testBit i

def tt (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ :=
  Nat.ofBits fun p : Fin (2 ^ n) => f fun i : Fin n => p.val.testBit i

def vars (n : ℕ) : List ℕ :=
  (List.range n).map fun i => Nat.ofBits fun p : Fin (2 ^ n) => p.val.testBit i

theorem final (n lb : ℕ) (f : (Fin n → Bool) → Bool)
    (hn0 : n ≠ 0) (hess : ∀ i : Fin n, ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!(x i))))
    (hs0 : lb ≤ n - 1 ∨ s0 (2 ^ (2 ^ n) - 1) (tt n f) (n - 1) (vars n) = false)
    (hs1 : lb ≤ n ∨ (lb = n + 1 ∧
      s1 (2 ^ (2 ^ n) - 1) (tt n f) n (vars n) (vars n) = false)) (t : ℕ)
    (h : HasCircuitSize n f t) : lb ≤ t := by
  classical
  obtain ⟨C0, hC0, hsz0, hf0⟩ := h
  -- a smallest circuit for f
  have hex : ∃ s, ∃ D : Circuit, FanInTwo D ∧ circuitFun n D = f ∧ D.size = s :=
    ⟨C0.size, C0, hC0, funext hf0, rfl⟩
  obtain ⟨D, hD, hDf, hDs⟩ := Nat.find_spec hex
  have hmin : ∀ E : Circuit, FanInTwo E → circuitFun n E = f → D.size ≤ E.size := by
    intro E hE hEf
    rw [hDs]
    exact Nat.find_min' hex ⟨E, hE, hEf, rfl⟩
  have hle : D.size ≤ t := (hmin C0 hC0 (funext hf0)).trans hsz0
  by_contra hlt
  have hopD : ∀ g ∈ D.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    intro g hg
    simpa using (hD g hg).1
  -- normalise
  set C : Circuit := ⟨D.gates.map nrm, D.output⟩ with hCd
  have hlen : C.gates.length = D.gates.length := by simp [hCd]
  have hrun : ∀ x, run C.gates x = run D.gates x := fun x => nrm_run D.gates hopD x
  have hCf : circuitFun n C = f := by
    rw [← hDf]
    funext x
    change (run C.gates (List.ofFn x)).getD D.output false = (run D.gates (List.ofFn x)).getD D.output false
    rw [hrun]
  have hgC : ∀ j (hj : j < C.gates.length), ∃ g ∈ D.gates, C.gates[j] = nrm g := by
    intro j hj
    have hj' : j < D.gates.length := by omega
    exact ⟨D.gates[j], List.getElem_mem hj', by simp [hCd]⟩
  have hopC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact hopD g' hg'
  have hrl : ∀ g ∈ D.gates, (rds g).length ≤ 2 := by
    intro g hg
    have := (hD g hg).2
    rcases hopD g hg with h | h | h <;> simp [rds, h] <;> omega
  have hFC : FanInTwo C := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact ⟨(hD g' hg').1, hrl g' hg'⟩
  let m := C.gates.length
  have hm : m = D.size := hlen
  -- every gate is read or is the output
  have Hu : ∀ k < m, n + k = C.output ∨ ∃ j, k + 1 ≤ j ∧ ∃ hj : j < C.gates.length,
      n + k ∈ C.gates[j].inputs := by
    intro k hk
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨E, hE1, hE2, hE3⟩ := del n C hFC k hk
      (fun j hj hkj hin => hcon.2 ⟨j, hkj, hj, hin⟩) (fun h => hcon.1 h.symm)
    have := hmin E hE1 (hE3.trans hCf)
    have e : C.size = m := rfl
    omega
  -- every input is read or is the output
  have Hi : ∀ i < n, i = C.output ∨ ∃ j, ∃ hj : j < C.gates.length, i ∈ C.gates[j].inputs := by
    intro i hi
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨x, hx⟩ := hess ⟨i, hi⟩
    apply hx
    rw [← hCf]
    refine indep i C.gates hopC ?_ (List.ofFn x) (List.ofFn _) (by simp) ?_ C.output
      (fun h => hcon.1 h.symm)
    · intro g hg hig
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      obtain ⟨g', _, e⟩ := hgC j hj
      refine hcon.2 ⟨j, hj, ?_⟩
      rcases hopC _ (List.getElem_mem hj) with h | h | h
      · simpa [rds, h] using hig
      · simpa [rds, h] using hig
      · simp only [rds, h] at hig
        exact List.mem_of_mem_take hig
    · intro q hq
      by_cases hqn : q < n
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hqn, dif_pos, Option.getD_some]
        rw [Function.update_of_ne]
        intro h
        exact hq (by simpa using congrArg Fin.val h)
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  let N := 2 ^ n
  let V : ℕ → ℕ := fun i => Nat.ofBits fun p : Fin N => (run C.gates (X n p)).getD i false
  have Vb : ∀ i p, p < N → (V i).testBit p = (run C.gates (X n p)).getD i false := by
    intro i p hp
    simp only [V]
    rw [Nat.testBit_ofBits_lt _ _ hp]
  have Vlt : ∀ i, V i < 2 ^ N := fun i => Nat.ofBits_lt_two_pow _
  have Xl : ∀ p, (X n p).length = n := fun p => by simp [X]
  have Xd : ∀ p i, i < n → (X n p).getD i false = p.testBit i := by
    intro p i hi
    simp [X, List.getD_eq_getElem?_getD, hi]
  have hVi : ∀ i < n, V i = Nat.ofBits fun p : Fin (2 ^ n) => p.val.testBit i := by
    intro i hi
    refine eqN (Vlt i) (Nat.ofBits_lt_two_pow _) fun p hp => ?_
    rw [Vb i p hp, Nat.testBit_ofBits_lt _ _ hp, run_input _ _ _ (by rw [Xl]; exact hi), Xd p i hi]
  have hvars : (List.range n).map V = vars n := by
    unfold vars
    exact List.map_congr_left fun i hi => hVi i (List.mem_range.1 hi)
  have hVo : V C.output = tt n f := by
    refine eqN (Vlt _) (Nat.ofBits_lt_two_pow _) fun p hp => ?_
    rw [Vb _ p hp, tt, Nat.testBit_ofBits_lt _ _ hp, ← hCf]
    rfl
  let R : ℕ → List ℕ := fun j => if hj : j < C.gates.length then C.gates[j].inputs else []
  have hG : ∀ j < m, (∃ i i', R j = [i, i'] ∧
        (V (n + j) = (if i < n + j then V i else 0) &&& (if i' < n + j then V i' else 0) ∨
         V (n + j) = (if i < n + j then V i else 0) ||| (if i' < n + j then V i' else 0))) ∨
      (∃ i, R j = [i] ∧ (V (n + j) = (if i < n + j then V i else 0) ∨
         V (n + j) = (2 ^ N - 1) ^^^ (if i < n + j then V i else 0))) ∨ R j = [] := by
    intro j hj
    have hRj : R j = C.gates[j].inputs := dif_pos hj
    have wb : ∀ i p, p < N → (if i < n + j then V i else 0).testBit p =
        if i < n + j then (run C.gates (X n p)).getD i false else false := by
      intro i p hp
      split_ifs
      · exact Vb i p hp
      · exact Nat.zero_testBit p
    have wlt : ∀ i, (if i < n + j then V i else 0) < 2 ^ N := by
      intro i
      split_ifs
      · exact Vlt i
      · exact Nat.two_pow_pos N
    have hv : ∀ p, p < N → (V (n + j)).testBit p = C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        if i < n + j then (run C.gates (X n p)).getD i false else false) := by
      intro p hp
      have := run_gate C.gates (X n p) j hj
      rw [Xl] at this
      rw [Vb _ p hp, this]
    have hl2 : C.gates[j].inputs.length ≤ 2 := (hFC _ (List.getElem_mem hj)).2
    rw [hRj]
    obtain ⟨g', hg', eg⟩ := hgC j hj
    rcases hin : C.gates[j].inputs with _ | ⟨i, _ | ⟨i', _ | ⟨i'', l⟩⟩⟩
    · exact Or.inr (Or.inr rfl)
    · right; left
      refine ⟨i, rfl, ?_⟩
      rw [hin] at hv
      rcases hopC _ (List.getElem_mem hj) with h | h | h <;> rw [h] at hv
      · left
        refine eqN (Vlt _) (wlt i) fun p hp => ?_
        rw [hv p hp, wb i p hp]; simp [GateOp.eval]
      · left
        refine eqN (Vlt _) (wlt i) fun p hp => ?_
        rw [hv p hp, wb i p hp]; simp [GateOp.eval]
      · right
        refine eqN (Vlt _) (Nat.xor_lt_two_pow (by have := Nat.two_pow_pos N; omega) (wlt i)) fun p hp => ?_
        rw [hv p hp, Nat.testBit_xor, full_bit N p hp, wb i p hp]; simp [GateOp.eval]
    · left
      refine ⟨i, i', rfl, ?_⟩
      rw [hin] at hv
      rcases hopC _ (List.getElem_mem hj) with h | h | h <;> rw [h] at hv
      · left
        refine eqN (Vlt _) (lt_of_le_of_lt Nat.and_le_left (wlt i)) fun p hp => ?_
        rw [hv p hp, Nat.testBit_and, wb i p hp, wb i' p hp]; simp [GateOp.eval]
      · right
        refine eqN (Vlt _) (Nat.or_lt_two_pow (wlt i) (wlt i')) fun p hp => ?_
        rw [hv p hp, Nat.testBit_or, wb i p hp, wb i' p hp]; simp [GateOp.eval]
      · exfalso
        rw [eg] at h hin
        change g'.op = _ at h
        change rds g' = _ at hin
        simp only [rds, h] at hin
        have := congrArg List.length hin
        simp at this
        omega
    · rw [hin] at hl2; simp at hl2
  have hS := search N n m C.output (tt n f) V R hVo
    (by
      intro k hk
      rcases Hu k hk with h | ⟨j, h1, h2, h3⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, h1, h2, by simp only [R, dif_pos h2]; exact h3⟩)
    hG m 0 (List.range n) (by omega) List.nodup_range (by
      intro i hi
      have hi' := List.mem_range.1 hi
      refine ⟨by omega, ?_⟩
      rcases Hi i hi' with h | ⟨j, h2, h3⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, by omega, h2, by simp only [R, dif_pos h2]; exact h3⟩)
  obtain ⟨q1, q2, q3⟩ := hS
  rw [List.length_range] at q1 q2 q3
  rw [hvars] at q2 q3
  have hmlb : m < lb := by omega
  rcases Nat.lt_or_ge m n with hmn | hmn
  · have e : m = n - 1 := by omega
    have := (q2 (by omega)).1
    rw [e] at this
    rcases hs0 with h | h
    · omega
    · rw [h] at this; cases this
  · rcases hs1 with h | ⟨h, h'⟩
    · omega
    · have e : m = n := by omega
      have := (q3 e.symm (by
        intro h0
        have := congrArg List.length h0
        simp at this
        exact hn0 this)).1
      rw [e] at this
      have hw : Wl n V 0 = vars n := hvars
      rw [hw, h'] at this; cases this

end S

namespace K

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool), P s (inv a :: kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section
variable {α : Type} {inv : α → α} {meet join : α → α → α} {y : α}

theorem Run.done : Run inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : Run inv meet join y s xs) :
    Run inv meet join y s zs := fun P d q u b => q p (h P d q u b)

theorem Run.one {s a r} (save : Bool)
    (h : Run inv meet join y s (inv a :: kept save a r)) :
    Run inv meet join y (s + 1) (a :: r) := fun P d q u b => u save (h P d q u b)

theorem Run.two {s a b r} (c ka kb : Bool)
    (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s + 1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

theorem Run.fold {P : ∀ t ws, Run inv meet join y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run inv meet join y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (save : Bool)
      (h : Run inv meet join y s (inv a :: kept save a r)),
      P _ _ h → P _ _ (Run.one save h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h))
    {t ws} (h : Run inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run inv meet join y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun k ⟨h', ih⟩ => ⟨Run.one k h', one k h' ih⟩)
    (fun c a b ⟨h', ih⟩ => ⟨Run.two c a b h', two c a b h' ih⟩)
  exact hex.elim fun _ hp => hp

end

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by
  cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by
  cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest save _ ih =>
    have e1 : (inv a :: kept save a rest).map e
        = inv' (e a) :: kept save (e a) (rest.map e) := by
      simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

theorem wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) :=
  List.foldl_append

theorem length_wiresFrom (gs : List Gate) : ∀ w : List Bool,
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wiresFrom]
  | cons g gs ih =>
    intro w
    rw [wiresFrom_cons, ih]
    simp
    omega

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, by
      rw [wiresFrom_cons, ht, List.append_assoc]⟩

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht⟩ := wiresFrom_prefix gs w
  rw [ht]
  exact List.getD_append _ _ _ _ h

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem split_at (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  have hlt : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hgp : gs[p] = g := (List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p, gs.drop (p + 1), ?_, by simp [hlt.le]⟩
  calc gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
    _ = gs.take p ++ gs[p] :: gs.drop (p + 1) := by rw [List.drop_eq_getElem_cons hlt]
    _ = gs.take p ++ g :: gs.drop (p + 1) := by rw [hgp]

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def SCleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ j ≠ k ∧ g.inputs = [j, k])

theorem SCleanGate.lt {m : ℕ} {g : Gate} (h : SCleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, _, hin⟩ <;> rw [hin] <;> simp_all

def SCleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → SCleanGate (n + p) g

def statVal (w : List Bool) : Sum Bool ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Sum Bool ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Sum Bool ℕ, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Sum Bool ℕ, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def simpNot (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, if c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, if c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] =>
      if j = k then (none, Sum.inr j) else (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, if c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, if c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] =>
      if j = k then (none, Sum.inr j) else (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ)) : Option Gate × Sum Bool ℕ :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ))
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, SCleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpAnd] at hg
    · cases a <;> simp [simpAnd] at hg
    · cases a <;> cases b <;> simp only [simpAnd, Option.mem_def] at hg
      all_goals try contradiction
      rename_i j k
      by_cases hjk : j = k
      · simp [hjk] at hg
      · simp only [hjk, ite_false, Option.some.injEq] at hg
        subst hg
        exact Or.inr ⟨Or.inl rfl, j, k, hv (Sum.inr j) (by simp), hv (Sum.inr k) (by simp), hjk, rfl⟩
    · simp [simpAnd] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpOr] at hg
    · cases a <;> simp [simpOr] at hg
    · cases a <;> cases b <;> simp only [simpOr, Option.mem_def] at hg
      all_goals try contradiction
      rename_i j k
      by_cases hjk : j = k
      · simp [hjk] at hg
      · simp only [hjk, ite_false, Option.some.injEq] at hg
        subst hg
        exact Or.inr ⟨Or.inr rfl, j, k, hv (Sum.inr j) (by simp), hv (Sum.inr k) (by simp), hjk, rfl⟩
    · simp [simpOr] at hg
  · rcases ins with _ | ⟨a, l⟩
    · simp [simpNot] at hg
    · cases a <;> simp only [simpNot, Option.mem_def] at hg
      · contradiction
      · rename_i j
        cases hg
        exact Or.inl ⟨rfl, j, hv (Sum.inr j) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Sum Bool ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b
      · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
      · rename_i c j; cases c <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j c; cases c <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j k
        by_cases hjk : j = k
        · subst hjk
          simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        · simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b
      · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
      · rename_i c j; cases c <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j c; cases c <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j k
        by_cases hjk : j = k
        · subst hjk
          simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        · simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def simpStep (n : ℕ) (acc : List (Sum Bool ℕ) × List Gate) (g : Gate) :
    List (Sum Bool ℕ) × List Gate :=
  let r := simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def simpPass (n : ℕ) (gs : List Gate) (acc : List (Sum Bool ℕ) × List Gate) :
    List (Sum Bool ℕ) × List Gate :=
  gs.foldl (simpStep n) acc

theorem simpPass_len (n : ℕ) (gs : List Gate) : ∀ acc : List (Sum Bool ℕ) × List Gate,
    (simpPass n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [simpPass]
  | cons g gs ih =>
    intro acc
    have h1 := ih (simpStep n acc g)
    have h2 : (simpStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [simpStep, List.length_append]
      cases (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 <;> simp
    have h3 : simpPass n (g :: gs) acc = simpPass n gs (simpStep n acc g) := rfl
    rw [h3, List.length_cons]
    omega

def SimpInv (n : ℕ) (x : List Bool) (w : List Bool) (acc : List (Sum Bool ℕ) × List Gate) : Prop :=
  acc.1.length = w.length ∧
  SCleanL n acc.2 ∧
  ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 x) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem simpPass_inv (n : ℕ) (x : List Bool) (hx : x.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List (Sum Bool ℕ) × List Gate),
      (∀ g ∈ gs,
        (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      SimpInv n x w acc →
      SimpInv n x (wiresFrom gs w) (simpPass n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (simpStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hcl, hi⟩ := h
    set w' := wiresFrom acc.2 x with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hx]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hvins : ∀ s ∈ ins, statValid (n + acc.2.length) s := by
      intro s hs
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
      exact (hi a).1
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by rw [lw']; exact hvins)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) x = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht⟩ := wiresFrom_prefix r.1.toList w'
    have hcl' : SCleanL n (acc.2 ++ r.1.toList) := by
      intro p g' hpg'
      cases hr1 : r.1 with
      | none =>
        rw [hr1] at hpg'
        simp only [Option.toList_none, List.append_nil] at hpg'
        exact hcl p g' hpg'
      | some g0 =>
        rw [hr1] at hpg'
        simp only [Option.toList_some] at hpg'
        by_cases hp : p < acc.2.length
        · rw [List.getElem?_append_left hp] at hpg'
          exact hcl p g' hpg'
        · have hpe : p = acc.2.length := by
            have := (List.getElem?_eq_some_iff.1 hpg').1
            simp at this
            omega
          subst hpe
          rw [List.getElem?_append_right le_rfl] at hpg'
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hpg'
          subst hpg'
          exact simplify_clean g.op (n + acc.2.length) ins hvins g0 (by simp [← hr, hr1])
    refine ⟨by simp [simpStep, hl], hcl', ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) x) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_len _ _ _ _ rfl, hl, getD_snoc_len _ _ _ _ rfl]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem exists_sclean {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ gs o, gs.length ≤ s ∧ SCleanL n gs ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  have hok : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    refine ⟨?_, hlen⟩
    rcases hop with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  set init : List (Sum Bool ℕ) := List.ofFn fun i : Fin n => Sum.inr i.val
  set acc := simpPass n C.gates (init, [])
  have hinit : ∀ x : Fin n → Bool, SimpInv n (List.ofFn x) (List.ofFn x) (init, []) := by
    intro x
    refine ⟨by simp [init], by intro p g hg; simp at hg, ?_⟩
    intro i
    by_cases hi : i < n
    · simp [init, hi, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by simp [init]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hinv : ∀ x : Fin n → Bool,
      SimpInv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc := fun x =>
    simpPass_inv n (List.ofFn x) (by simp) C.gates (List.ofFn x) (init, []) hok (hinit x)
  have hlen : acc.2.length ≤ s := by
    have := simpPass_len n C.gates (init, [])
    simp only [List.length_nil, zero_add] at this
    exact le_trans this hsz
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have h1 := ((hinv y).2.2 C.output).2
    have h2 := ((hinv y').2.2 C.output).2
    rw [hst] at h1 h2
    have e1 : wiresFrom C.gates (List.ofFn y) = C.wires (List.ofFn y) := rfl
    have e2 : wiresFrom C.gates (List.ofFn y') = C.wires (List.ofFn y') := rfl
    rw [← hev y, ← hev y']
    show (C.wires (List.ofFn y)).getD C.output false = (C.wires (List.ofFn y')).getD C.output false
    rw [← e1, ← e2, ← h1, ← h2]
    rfl
  | inr o =>
    obtain ⟨y, _, _⟩ := hnc
    have ho : o < n + acc.2.length := by
      have hv := ((hinv y).2.2 C.output).1
      rw [hst] at hv
      exact hv
    refine ⟨acc.2, o, hlen, (hinv y).2.1, ho, ?_⟩
    intro x
    have hv := ((hinv x).2.2 C.output).2
    rw [hst] at hv
    have e1 : wiresFrom C.gates (List.ofFn x) = C.wires (List.ofFn x) := rfl
    rw [← hev x]
    show (wiresFrom acc.2 (List.ofFn x)).getD o false = (C.wires (List.ofFn x)).getD C.output false
    rw [← e1, ← hv]
    rfl

def redir (m a : ℕ) : ℕ := if m < a then a - 1 else a

theorem redir_lt {m b a : ℕ} (hm : m ≤ b) (ha : a < b + 1) (hne : a ≠ m) : redir m a < b := by
  unfold redir
  split <;> omega

theorem redir_inj {m a b : ℕ} (ha : a ≠ m) (hb : b ≠ m) (heq : redir m a = redir m b) :
    a = b := by
  unfold redir at heq
  split at heq <;> split at heq <;> omega

theorem getD_drop_wire (w₁ u : List Bool) (b : Bool) (a : ℕ) (hne : a ≠ w₁.length) :
    (w₁ ++ u).getD (redir w₁.length a) false = (w₁ ++ [b] ++ u).getD a false := by
  unfold redir
  by_cases hlt : w₁.length < a
  · simp only [hlt, ite_true]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    have hlen : (w₁ ++ [b]).length = w₁.length + 1 := by simp
    rw [List.getElem?_append_right (by omega), hlen]
    congr 2
    omega
  · simp only [hlt, ite_false]
    have ha : a < w₁.length := by omega
    rw [List.getD_append _ _ _ _ ha]
    rw [List.append_assoc, List.getD_append _ _ _ _ ha]

theorem wiresFrom_drop_dead (w₁ : List Bool) (b : Bool) (post : List Gate) :
    ∀ u : List Bool,
      (∀ g ∈ post, w₁.length ∉ g.inputs) →
      ∃ u',
        wiresFrom (post.map fun g => ⟨g.op, g.inputs.map (redir w₁.length)⟩) (w₁ ++ u) = w₁ ++ u' ∧
        wiresFrom post (w₁ ++ [b] ++ u) = w₁ ++ [b] ++ u' := by
  induction post with
  | nil => intro u _; exact ⟨u, rfl, rfl⟩
  | cons g gs ih =>
    intro u hdead
    have hg : w₁.length ∉ g.inputs := hdead g List.mem_cons_self
    have hmap : (g.inputs.map (redir w₁.length)).map (fun i => (w₁ ++ u).getD i false)
        = g.inputs.map (fun i => (w₁ ++ [b] ++ u).getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      exact getD_drop_wire w₁ u b a (fun e => hg (e ▸ ha))
    set c := g.op.eval (g.inputs.map fun i => (w₁ ++ [b] ++ u).getD i false)
    obtain ⟨u', h1, h2⟩ := ih (u ++ [c]) (fun g' hg' => hdead g' (List.mem_cons_of_mem _ hg'))
    refine ⟨u', ?_, ?_⟩
    · simp only [List.map_cons, wiresFrom_cons, hmap]
      rw [List.append_assoc]
      exact h1
    · rw [wiresFrom_cons, List.append_assoc, List.append_assoc]
      rw [← List.append_assoc w₁ [b] (u ++ [c])]
      exact h2

theorem erase_dead (n : ℕ) (gs : List Gate) (o p : ℕ) (hcl : SCleanL n gs)
    (ho : o < n + gs.length) (hp : p < gs.length) (hne : n + p ≠ o)
    (hdead : ∀ (q : ℕ) (g : Gate), gs[q]? = some g → n + p ∉ g.inputs) :
    ∃ gs' o', gs'.length + 1 = gs.length ∧ SCleanL n gs' ∧ o' < n + gs'.length ∧
      ∀ x, val gs' n o' x = val gs n o x := by
  let gs' := gs.take p ++ (gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (redir (n + p))⟩
  let o' := redir (n + p) o
  have hlen' : gs'.length + 1 = gs.length := by
    simp [gs']
    omega
  have ho' : o' < n + gs'.length := redir_lt (by omega) (by omega) (Ne.symm hne)
  have hcl' : SCleanL n gs' := by
    intro q g hqg
    by_cases hqp : q < p
    · have h1 : gs'[q]? = gs[q]? := by
        simp only [gs']
        rw [List.getElem?_append_left (by simp; omega)]
        exact List.getElem?_take_of_lt hqp
      rw [h1] at hqg
      exact hcl q g hqg
    · have hlt' : q < gs'.length := (List.getElem?_eq_some_iff.1 hqg).1
      have hq1 : q + 1 < gs.length := by omega
      have h1 : gs'[q]? = ((gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (redir (n + p))⟩)[q - p]? := by
        simp only [gs']
        rw [List.getElem?_append_right (by simp; omega)]
        simp [Nat.min_eq_left (Nat.le_of_lt hp)]
      rw [h1, List.getElem?_map, List.getElem?_drop] at hqg
      have hidx : p + 1 + (q - p) = q + 1 := by omega
      rw [hidx] at hqg
      obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hqg
      have hcl0 := hcl (q + 1) g0 hg0
      have hd0 := hdead (q + 1) g0 hg0
      rcases hcl0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hjk, hin⟩
      · refine Or.inl ⟨hop, redir (n + p) j, ?_, by simp [hin]⟩
        exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
      · refine Or.inr ⟨hop, redir (n + p) j, redir (n + p) k, ?_, ?_, ?_, by simp [hin]⟩
        · exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
        · exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
        · intro heq
          exact hjk (redir_inj (fun e => hd0 (by rw [hin]; simp [e]))
            (fun e => hd0 (by rw [hin]; simp [e])) heq)
  refine ⟨gs', o', hlen', hcl', ho', ?_⟩
  intro x
  unfold val
  have hsplit : gs = gs.take p ++ gs[p] :: gs.drop (p + 1) := by
    calc gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
      _ = gs.take p ++ gs[p] :: gs.drop (p + 1) := by rw [List.drop_eq_getElem_cons hp]
  set w₁ := wiresFrom (gs.take p) (List.ofFn x)
  have lw₁ : w₁.length = n + p := by
    rw [length_wiresFrom]
    simp [Nat.min_eq_left (Nat.le_of_lt hp)]
  have hdead_post : ∀ g ∈ gs.drop (p + 1), w₁.length ∉ g.inputs := by
    intro g hg
    obtain ⟨k, hk, hgk⟩ := List.getElem_of_mem hg
    rw [List.getElem_drop] at hgk
    rw [lw₁]
    have hlt_k : p + 1 + k < gs.length := by simp at hk; omega
    exact hdead (p + 1 + k) g (by rw [List.getElem?_eq_getElem hlt_k, hgk])
  set b := gs[p].op.eval (gs[p].inputs.map fun i => w₁.getD i false)
  obtain ⟨u', hu1, hu2⟩ := wiresFrom_drop_dead w₁ b (gs.drop (p + 1)) [] hdead_post
  have heq1 : wiresFrom gs' (List.ofFn x) = w₁ ++ u' := by
    simp only [gs', wiresFrom_append]
    rw [← lw₁]
    simpa [w₁] using hu1
  have heq2 : wiresFrom gs (List.ofFn x) = w₁ ++ [b] ++ u' := by
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append, wiresFrom_cons]
    simpa [w₁, b] using hu2
  rw [heq1, heq2]
  show (w₁ ++ u').getD (redir (n + p) o) false = (w₁ ++ [b] ++ u').getD o false
  rw [← lw₁]
  exact getD_drop_wire w₁ u' b o (by rw [lw₁]; exact Ne.symm hne)

def Live (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live gs o (p + 1) a)) := by
  have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases hnd p hplt with h | ⟨q, g', hg', hin⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin⟩
        have := (hcl q g' hg').lt _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∀ d p, p + d = gs.length →
      Run (invF (n := n)) meetF joinF (val gs n o) d ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1
          omega
    exact Run.perm (hperm.map (val gs n)) Run.done
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    have IH := ih (p + 1) (by omega)
    have hstep := live_succ n gs o hcl hnd p g hg
    have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
      (mem_liveList _ _ _ _ _).2 ⟨(hcl p g hg).lt a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg := val_gate n gs p g hg (hcl p g hg).lt
    have hnd0 := nodup_liveList gs n o p
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hjk, hinp⟩
    · have hjm := hin j (by simp [hinp])
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hjm
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
          rw [mem_kept]
          rintro (⟨_, h⟩ | h)
          · exact hnew j hjm h.symm
          · exact hnew _ (List.mem_of_mem_erase h) rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff]
          simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
              · exact Or.inr (Or.inr ⟨haj, h1⟩)
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hjm, fun _ => h1⟩
            · exact Or.inr ⟨h2, fun h => absurd h h1⟩
      have hval : val gs n (n + p) = invF (val gs n j) := by
        funext x
        rw [hvg x, hop, hinp]
        simp [GateOp.eval, invF]
      have IH' := Run.perm (hp2.map (val gs n)) IH
      rw [List.map_cons, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.one _ IH')
    · have hjm := hin j (by simp [hinp])
      have hkm := hin k (by simp [hinp])
      have hke : k ∈ (liveList gs n o p).erase j :=
        (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
      have hp1 : (liveList gs n o p).Perm
          (j :: k :: ((liveList gs n o p).erase j).erase k) :=
        (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
      have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
          a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
        intro a
        rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j
            (kept (decide (Live gs o (p + 1) k)) k
              (((liveList gs n o p).erase j).erase k))) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
          · rw [mem_kept, mem_kept]
            rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
            · exact hnew j hjm h.symm
            · exact hnew k hkm h.symm
            · exact hnew _ ((hmr _).1 h).2.2 rfl
          · rw [hmr]; simp
          · rw [mem_kept, hmr]
            rintro (⟨_, h⟩ | h)
            · exact hjk h
            · exact h.2.1 rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
          simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
              · by_cases hak : a = k
                · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hjm, fun _ => h1⟩
            · exact Or.inr ⟨hkm, fun _ => h1⟩
            · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
      have IH' := Run.perm (hp2.map (val gs n)) IH
      have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
          then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
        funext x
        rw [hvg x, hinp]
        rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval, meetF, joinF]
      rw [List.map_cons, kept_map, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')

open Classical in
theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  have hex : ∃ m, ∃ gs o, gs.length = m ∧ SCleanL n gs ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
    obtain ⟨gs, o, hl, hcl, ho, hev⟩ := exists_sclean f hnc s h
    exact ⟨gs.length, gs, o, rfl, hcl, ho, hev⟩
  set m := Nat.find hex
  have hm_le : m ≤ s := by
    obtain ⟨gs, o, hl, hcl, ho, hev⟩ := exists_sclean f hnc s h
    exact le_trans (Nat.find_min' hex ⟨gs, o, rfl, hcl, ho, hev⟩) hl
  obtain ⟨gs, o, hlen, hcl, ho, hev⟩ := Nat.find_spec hex
  have hnd : ∀ p, p < gs.length → n + p = o ∨
      ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra! hbad
    obtain ⟨hne, hdead⟩ := hbad
    obtain ⟨gs', o', hlen', hcl', ho', hev'⟩ := erase_dead n gs o p hcl ho hp hne hdead
    have hlt : gs'.length < m := by omega
    exact Nat.find_min hex hlt ⟨gs', o', rfl, hcl', ho', fun x => (hev' x).trans (hev x)⟩
  refine ⟨gs.length, by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact run_live n gs o hcl ho hnd gs.length 0 (by omega)

abbrev fG : BFn 4 := fun x => decide (3 ≤ (List.ofFn x).count true)

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true, kept, List.mem_cons] at hmem
    · rcases hmem with rfl | hr
      · simp [ha, hm]
      · exact hw _ (by simp [hr])
    · rcases hmem with rfl | rfl | hr
      · simp [ha, hm]
      · exact ha
      · exact hw _ (by simp [hr])
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha, hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k + i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all

def lo (k : Nat) := 2 ^ k - 1
def mask (k : Nat) := lo (k + k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k + i) := by
      simp [mask, lo, Nat.testBit_two_pow_sub_one, show i < k + k by omega, show k + i < k + k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k + i) := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k + i) hm hh)
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 &&
      (let w := a ^^^ m
       f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
            (slack ≥ 2 && f (w :: a :: b :: r)))

theorem next_one {k a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((a ^^^ mask k) :: kept save a rest))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s + 2 - ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  have ht := hf _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s + 2 - ws.length := by omega
    simp [ht, hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  have ht := hf _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s + 2 - ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) →
      next (mask k) (s + 2 - zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag)

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else false) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, moved tag d i _ h] <;>
    split_ifs <;> simp

theorem move_run {k s ws} (h : NatRun (mask k) (goal k) s ws) (tag d : Nat)
    (hz : (tag &&& (tag <<< d)) = 0) (hm : moveBits tag d (mask k) = mask k)
    (hy : moveBits tag d (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (moveBits tag d)) := by
  rw [← hy]
  exact Run.map _ (fun a => (move_hom tag d hz a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (move_hom tag d hz a b).1) (fun a b => (move_hom tag d hz a b).2.1) h

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s + 1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and] <;>
        grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k + i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s + 1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k + i) ≤ (goal k).testBit i := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s + 1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s + 1
  · simp [covers, he, required_up h he]
  · simp [covers, he, required h]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat + c.toNat
  let y := (!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s + 1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s + 1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6, Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6, Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s + 1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s + 1
    · simp [hl, Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o + a) = true) :
    span f (a + b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)⟩

def fld (T w i : Nat) : Nat := (T >>> (w * i)) &&& (2 ^ w - 1)

def bsr (T w h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if fld T w ((lo + hi) / 2) ≤ h then bsr T w h f ((lo + hi) / 2) hi
       else bsr T w h f lo ((lo + hi) / 2))
    else lo

def hw (w : Nat) : Nat := (w % 11400714819323198549 + 317) ^ 3 % 11400714819323198549 + 1

def hz : List Nat → Nat
  | [] => 0
  | w :: t => hw w + hz t

def hk (zs : List Nat) : Nat := hz zs % 4294967291

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def scr (k s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck k s zs)

theorem scr_no {k s : Nat} (pool : List Nat) {zs : List Nat}
    (h : NatRun (mask k) (goal k) s zs) : scr k s pool zs = false := by
  unfold scr
  rw [Bool.and_eq_false_iff]
  right
  rw [List.any_eq_false]
  intro x _
  rw [scoreCheck_no h x]
  simp

def bar (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (ori : List Nat → List Nat) (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next (mask k) (s + 2 - ws.length) ws fun zs =>
        covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs)))

theorem bar_sound {k S N idx ori pool} {s i : Nat} (hb : bar k S N idx ori pool s i = true)
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [bar, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (zs : List Nat) :=
      covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs))
    have hF (zs) (hz : NatRun (mask k) (goal k) s zs) : F zs = true := by
      simp only [F, covers_ok hz, scr_no pool hz, Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p (hr hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem bar_all {k S N idx ori pool} {cap : Nat}
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, bar k S N idx ori pool s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := bar_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h


def rowsG : List ℕ := [3, 3, 3, 3, 5, 5, 5, 5, 6, 6, 6, 6, 9, 9, 9, 9, 10, 10, 10, 10, 12, 12, 12, 12, 7, 11, 13, 14, 7, 11, 13, 14, 7, 11, 13, 14, 7, 11, 13, 14, 7, 11, 13, 14, 7, 11, 13, 14]

def xsG : List ℕ := [0x77777700f0ff, 0xbbbbbb0f0f0f, 0xddddddf00ff0, 0xeeeeeefff000]

theorem rowsG_len : rowsG.length = 48 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 4) => (fun x : Fin 4 → Bool => x i)).map (fun a => encL a rowsG)
      = xsG := by decide +kernel

theorem enc_goalG : encL fG rowsG = goal 24 := by decide +kernel

theorem maskG : mask 24 = 2 ^ rowsG.length - 1 := by rw [rowsG_len]; simp [mask, lo]

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 24 zs &&& lo 24) ≠ lo 24 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 6, ¬ NatRun (mask 24) (goal 24) s xsG) :
    ∀ s ≤ 6, ∀ zs : List ℕ, zs.Sublist xsG → NatRun (mask 24) (goal 24) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 6, ¬ NatRun (mask 24) (goal 24) s xsG) :
    ¬ HasCircuitSize 4 fG 6 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run fG ⟨fun _ => false, fun _ => true, by decide⟩ 6 h
  have hr : NatRun (mask 24) (encL fG rowsG) s' (ws.map fun a => encL a rowsG) :=
    Run.map (fun a : BFn 4 => encL a rowsG)
      (fun a => by rw [maskG]; exact encL_inv a rowsG)
      (fun a b => encL_and a b rowsG) (fun a b => encL_or a b rowsG) hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 2 => 90
  | 3 => 227
  | 4 => 247
  | 5 => 21
  | 6 => 1
  | _ => 0

def HT : Nat → Nat
  | 2 => 0xfd8de339faafc7b6fa1b86e4f68e867af1027d83e80b4be9e7723cdbe596607ce4a7da5be41b243fe282f4a8e15b59b1e0c0d950daded0fad7b3f2c2d5cb1b30d2f54e59d25906d2cbb88e3acaaa8038c88da185c63ea3bdc4c1c870c27f8dd0c27ab72ac230884fc19bd999be08b70dbc5fe2acba4a39d8b8c5a942b8114fbfaf4d76edad8598b1a87160e9a85bceb09e50a81d9a076aeb94bae51192ac66cb9035518c903398a58c3ec37989bff89d83e32ebe7bf064ab7a4d02ef7a31f1b87891de127787a6d573a0ec3e70e38919709c3a59700e590566ba757565e6c62e6318f2af5cd760675b1fdb6159f4c5cd554b907f55157513525548c84c0a236649dc1d124996aa894790b60c46db25f146cce7e6455de5aa403708353f1032473ee365453ab004ea2398ea66197d94e418544055173c66c3149ecb29113d25e4111f14580fcdee440fb2dd0d0f4d1b330b043db108ee926506119701060288f70311bfed01400bcb
  | 3 => 0xff1cecfbfef50eb3fe2e6c97fdf39589fdee9651fd025d64fb66c30ffb363264f8eed471f6400fb7f44ca7b3f2e30b86f2534588ee10fd6deb8813deea11ad43e99e468ce9983df8e91e078be786f80be762c34ce6cd140fe6c6d141e6383025e59ac20ee57058e3e537e4b3e4459820e2f6ded1e1d0272cdfe77b06dec93bc1ddb325c5dd0fab3fdc9eb596dae063c4daded0fada88f099d9a5d7fad91b2830d2c99cddd25906d2d02ae943cdbd14bccae20094caaa8038ca52d912c962db92c5b4b023c575826ec1bb7bb4c15af4b8bfdc966cbf561627be08b70dbe08179abd8de625bd5525ddbb81307fb7f313cbb7d3abdbb7b8a001b6f105acb6b10821b40c85bfb370410eb302b26ab2e38af2b24ea708b05ecf2dadeb93b1ad8598b1abd23550abb44536ab0326c0a951e9d4a5eede8ea58d131fa4ec8d08a4ce9901a31d3654a03c37dfa0318d399ef174749e487d109d6020829c7918989c34114f9989b08696e5e9909680c4a3944c750693918fea938a2f2392dd72ca917c55ad9064404c8d5e35148c9a66ee8c5430f48c5423ee8b28495f8a634939886c3fde86d9b67285a75f4c859331398174761b8134fb6f80d8316a7f32ec9c7f19294d7dafffef7d2b283d7c4dff647bdb44877bb91b7a7ab1a71e792f622e77f443f97787a6d576f8a671740d89627389526c7326458b7262776570e389196e57017a6d420d976c5964d06bae03016b3bc00269d44484699c01ab693d3e3d69222d066897dcc565e6c62e65b547146546250563b06bd5605c122f5feb39155fbfcd7e5f92b4fc5ef3e9ad5dbc01825bb8dcbf5890121d586a9ad1585b2bb4559b6d4c55805c15550c1e77520f12f050df46a450914d0d5019d6be4edf49874cd2372048839dbf4790b60c4747c31546cce7e645dfba82449ce32844187cbf43fd6b88426987e1410e79d340a1b8613d48b18d3cbeb4293aed87063a7744d63a2ef07839a97aa5398d47ce386fdbb335b2788e358ad90e34f1ca00344e20f832222f8631e1596231cbbdf73163995a30f120fc3048645e2bc856d02b9fc71a2a5bab1c285e5e1f24afbc7024a689002419d03621d50f4320ac50071d266fe71cb15ab91c304da11b493b8a1a49bb1619919a0718d03fce16f5617016edb6ca16591cbf150b684d0fcdee440fb2dd0d0fb015740f295f7a0cfc3fd60b6e25ce0a9a034909434730091c214107df353206f4e8af06c074d606b325ff06a3955206241055057f88da03d6361a01da5025
  | 4 => 0xffb0a5d5ff449931ff1cecfbfe6032adfc44211dfbc078c2fb363264fab3b8f2f96b2e81f7928b19f5a36148f57933e4f5191107f378231ef21d1510ee10fd6dedf15330ebc80a30e8cd8e41e8296627e74d40e5e62d5237e622445be5ff0c41e59ac20ee4f06d35e330cac3e32d9f8ae0c0b238e09300c7deb3fd7ede9841e9dd5ed34cdc717bc5da368c7cd99b5506d5bd4f5dd4e6eaded3133136d2c99cddd191dcf8d02ae943cbc71cb8cb61231ecb585653c78d5d5dc6ca2fd5c634dcf9c5ae958fc509e06fc4fc5446c4e6a855c4695473c3dff119c2810163bfe20485bfdc966cbed1d7f6bdc1c301bd02207bbb59438cba507a91b8da13f6b580d153b363b7c8b302b26ab238bb3eb2158324b079790cb003a9f5ae5e7911ae23cb14adfaf123aa7347e0a83c0ce4a79e7cd8a389d378a2a18ff5a28bab97a1689d77a0318d399f5e11989e1a22f59da853db9d678d779d6020829c857b6f9c5bbd859c34114f9a8e72149a40dfa099ec90f99531912a944c750692ba859c90f7d1cf9034a4478fd232258e9778468e8e06f38e66c8b88ce28d378bad398a8b80c89489d093b0883c4c6887a0822d876fba6f868618ec868106b485b96c5f8344768b7f19294d7cce2c3a7c4dff647bcb21d27bb91b7a7ba32fb07b7ff7967b445f3c7aba0efb7a71588a7a2a48fd7a11680679cb8d737968849377f443f977db383c74f4f58f7488c65c746a050d73b90b0f73b4f3bb739b6fbc73174d3e73028b2672ca16f671fe0f3271870026702a558a7018d2336e57017a6cc601f46b8213516a30e7d969c3ade1699c01ab686f7aa7682cc8366712c84d602275f85feb39155cc2e0785ca8ec9a5c269bc75c11c202588c3cf95801ecb856c2d450569bae6154a58262545b97ec517b7229510af69f50da2ee150ac66e74ff6c01f4f4d41854baf7a044bad9e084b1241d84a69af6548f0ac4048ab49f548839dbf47f484d247804d6b45dfba8245df4a954553313844ea6c0843f1af1f43df646643a98de943a4b669437bdc78431353323f0a120c3d9245e63d1f682d38dc78d73895590337988a34369d94b03624dea035da24c435d76b0335b2788e33677b7b32efe6083248b57e32343f0531973ca8304187de2f9402fb2d4bc89b2c38ecdb2b22159d2ab27c7f29b09c7f290fe900285e5e1f28204f6728087dbe27523024225b8bed21d50f431f517f051cc2ddca1c79e1fa1a49bb1619e6633719e5508e194be66a18ba540418971bea1719b91e16f5617016591cbf14bf07170d5c23910b87a4bf09eaf06209a8bcc90969c6f60855ae8107e6a22706b325ff05e690c605aa15790504506e0429eca10246ed4901ede1e601da5025014b4fc10102fea6
  | 5 => 0xff449931ff1cecfbf5a36148e62d5237d3133136cb5856539c34114f9531912a9034a4477cce2c3a7ba32fb07b7ff796699c01ab6712c84d5801ecb850da2ee148839dbf3d1f682d35b2788e0d5c23910246ed49
  | 6 => 0xff1cecfb
  | _ => 0

def LT : Nat → Nat
  | 2 => 0x333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333
  | 3 => 0x44444444444444444444444444444444444434444344434444444434444444444444444344444444444444444444444444444444444444444444444434444434444444444344444444444444444444444343444444444444444444444444444444444444444444444334444444444444444
  | 4 => 0x5545554555555554555555554555555555555554545555555555555545555555545555555555555545555455455554555555555555555555454545555555554555555555555554555545555455555555555555555555554554555555555555555555545555555555555455554555455555544555555554555555455
  | 5 => 0x545555455555455545455
  | 6 => 0x4
  | _ => 0

def DT : Nat → Nat
  | 2 => 0xc12d18001664c000031c7880004b6260000b2bd300018debc00031bd5600063970c000ae9cf8001253930002c415e000506280000c31d180018dead00031972c0005682c4000c6b5500017ec970002ccb7e0005982bc000bf6690001425ac0002bc94e000508cc4000b305d800181eb10002cc84e00061968c000b29d080014253900020b12800056969c000b105c8001664a700030cb88000637cc4000b2c52800179eb10002bcb800005d968c000c7667800189eb90002c314c0005984c4000b30558001665a80002a971600047462c000c750b8001425b0000284a600005094c4000bf54b800189ead0002c971c0005882c4000969ca8001662a700030a33e0005eb25c000c6c548001520b100031d32e0003d6230000c72d200012d18d0002bcb4e0004b6064000c4f588000f568b0002531320005096b8000c4c5500018e323000284b74000638a8c000b3057000176c9700028303e0005196c4000a72d380018ea9700031c74600063b268000c68d100017cb9300028486200063ab48000c6f56000105793
  | 3 => 0x31d996c405982c5780bf565b1018ecca60031dfb25c05fb2c4f80f1425b1018ecca62035e3b25c063b305780b32d88e0186cc762030cb628c06dc764b80f3664a701665a706031e1968c04b724c580eb8dead017accb62031d92e1805992c4580c7565b901665af16031d9727c0637a8cb80d98ec9701b71d9a403963467c05992c5380c74e5b1018edb13a0315996e405a96c4500d58ec97018e5b320000637ab40637ac4200df8e5a3018ecc94e031b13e4c000bf64b80c3665b101c2ccb4e0314b624c000b305780a12e531018eccb5c031d992e4063b2b4f80d9660b101f284b7203ae37ac4058970588001865a301d31bd620315996b4059a12d800f3665c001d71b154031dc96dc06bb32d380f1665a7016684a62031d8627c063aec4f80b32dc8b018e4b126031cb5e4c072968c580c7665ba0002cc94e0284b62c0059b105880b305397017eccb7203d5096c4073b305880f32d3930176ccb62031d096c006296f588096c498b018ecb03e037e37ac4063ab2d880c742531018ecb13e02ccb623007bb305780bf2d893018accb62031d896bc063af25880b32d68b018ec4162031d990c4059af2d380c565eb101b71d52e02cc7622c063b2c5080e18e5a301a31cb46031d696c4063b339b00f35e5a701625b11603a5096c405796c4580f5660b1018e5b926038e3968c06ec72d880c7664b1015e5b14e031d996bc07ca12d800c765a1c01f284b620005096c005096c4080f942531018eccb76031d7969c063c4f5880014253101e6ccb4e030d9627c05996c0580c7658a0018ecc772031cb625005996c4580c756597018e5c746039638e8c000b105880b32988b018e5b12c03dd982e4063b12dc80bf665b1018ebcb72034e3b2c406396b4980b32d90801665b11a036d92e2c0638ec4980b305882018ecd52e031d98e8c075c4f5880c92d89201ee0b126031d996b0059727c580db7ec97018ecc662031d996e4000af2d380f92d899000313d6203963968c063b329c80c755897018e3b14603bd982c405082f5880f7658a600c4f93160335996e00639ac4880c75589f016663112033e3b32c050969d180c72d813018e5b126031d996f0063b32d580c72dead01eec4162031cb625406394c4980c56589f018e5a30a03963971005fb32cb80c7662b101d5eb116031d996b4077b32d380db8cb9301665c15e031d98ec4063b2f5680c7658a201ab1bd62031b93e4c076b32d880f7660b10186ccb72031d95e7c063b12d880e5865a3018ebcb6203e50627c000c754b80018e3a30182ccb62031bd62b4068c764b80f36539f0196cb13c03ae37ae4073c6f5880ab2d88b01665c94e030cb624c059627c580bf65897018ea4b62038d096c4061b32d180c7665b0
  | 4 => 0x1665b1162f1d996c4b80c7665b1f98ecca638e5b126431e1b32d880c766531b32d8a7178eccb629b1d97ac4be3b32d89fc76694b63cb1d9627fbe3b32d8e3a12deb101b71d92f8ecbd627f7e3b32d8e3b33a5b1cb8ecb13f665b9622f1d9a12d8edb32d88bb32d89316031d9727eccc96c45fbc7625b1c766acb638ecb13e7bee3b2c4fe3b32d89cc7665b9178eccb80c76dfb32d8f9c76589fc7665b94f8eccb92c71dbb32d8e3b32e0b1018d89f27665b1462c061b32d8e396c498bc7660bd63ef1d996c71cb624c96396c5393c7665b9738eccb62436e3b32dce396cd893c7665b9278ecb4627f1d9969d1f2b32d88bc78accb6203ae37ac71cb624c8fcb3425b1cd8eccb73665bd622fce3b3258e3b32d883c7665b1338e5b9624c05996e45edc72d893c72d893278eccb728f1d996c57d996c4589b5665b117f6ccb622fae3b2c4fe3b32d89df3665b117f31d096c7cd996c53f5c5665b1e58eccb72025b1262fe63b2c4fe3b2c4f80c72d8a3278eccb6220063ab2d8f0c7665b1c76589f2e031d9627f463b32d8e3b32deb9f38eccb4f8eccb622c062b32d8e3b2c4f9fc7665b1258eccb629f8e3b32d8f2c72d893b3425c1638eccb66c7ee3b32dcf2c7665a3c77eccb63665b2622f1d996c48e39b2d893c72deb127e71d996e75e3b32d8f8c7665b1c7668313e031cb724f1d996e5880c7664b1c76589f38031d996bf6e3b32d8e3b32d893c7665c763cb1d98ec71d9992d8f2c72d8a3fb8e5b1278ecc1625f1d996c4780f9425b1eb665b1178eccb621b1dcb32dcd996c458af7665c163e71cb624f363b32d8e3b32dcb6c72deb147b31d996c71dbb2c4fe3b32dcb8c7660b13f8eccb6ac4079b32d3fcb32d88bb32d88b01ab1d996c6ccb625c580b32d88bf78ecb13f931cb624f1d996c51d996c4f8b017eccb638ecd896c71d996c56e3b35e5b1c7665a72f8eccb96c7963b32d8f5c7665b9e78eccb638eccb94c7ce3af2d8e3b32e231c7666cb638eccb7ac6cd096c45e3b32d89bc7665b96f6684b629fe63b32dce5c7665b1c7665b9018eccb62ab1d996e4b80c7665b9f78eccb5fb71d9965c072c72d1fbc7660b1c76589f3b8ecd996c7ae396c49e3b32d889c7665b13d8ed5996c7ee3b32d8e3b32d885c7665b93f665c1622fce3b32d8fcc72d893b32e0b14f8e5b12603ae3b32d6e3b32d8b0c72d89727eeccb622c06396c49e3b32d8b1c7665a32f8ecb13e2f1d99d2dce4c7665b1f58eccb638ecd096e71d9629cfe396c4f93c772ccb638f1d996c71d996d98f2c3665b1018eccb5b8eccb70c71d996c4263b32da31db8ecb12e031d98ec71d996c98e3a12d893c7665c17203dd982c76e3ab2d8e3b2e589feb8e5bd63b71d9627f1d9627c9e3b32d887018ec4b62031d796c7de3b32dcf5c7665b1e98eccb638eccb622b1cb82c49e3b32d882c7425b147665b11620059627c5e3b32dbb1eb8ecbd63f31d996c31d9628cffcc7665b1f78e5b126031d996c31d996c40e3b32d880
  | 5 => 0x63b32d897018eccb638eccb627f1d9a12d8e3b32e0b1f78eccb62031d9627f1d996c45e3b32d8a7c7665b963b71d996c71d996c4980b32d88bc7665b147cb1d996c71d996f5880c7665b9f38eccb62031cb624fae3b32d8fcc7665b1
  | 6 => 0xc7665b1
  | _ => 0

def VT : Nat := 0xfffffffffffffffffffffff0ffffffffff0fffffffffff00fffffffff0fffffffffff0f0fffffffff00ffffffffff000ffffffff0fffffffffff0ff0ffffffff0f0ffffffff0fffffffffff0fff0fffffff0f0fffffffff00ffffffffff00ff0ffffff0fffffffffff0fff0fffffff0ff0ffffffff0f0fffffffff0f0f0fffffff00ffffffffff00f0ffeeeeeeffff00eeeeeefff0f0eeeeeefff00feeeeeefff000eeeeeeff0000eeeeeef0f000eeeeeef00000eeeeee0ff000eeeeee0f0000eeeeee00f000ddddddff0ff0ddddddf0fff0ddddddf00fffddddddf00ff0ddddddf00f00ddddddf000f0ddddddf00000dddddd000ff0dddddd000f00dddddd0000f0ccccccfffff0ccccccf0000fccccccf00000cccccc0ffff0bbbbbbff0f0fbbbbbb0fff0fbbbbbb0f0fffbbbbbb0f0f0fbbbbbb0f0f00bbbbbb0f000fbbbbbb0f0000bbbbbb000f0fbbbbbb000f00bbbbbb00000faaaaaaffff0faaaaaaf0ff0faaaaaa0f00f0aaaaaa0f0000999999ff0fff999999ff00ff99999900ff00999999000f00888888ffff00888888ff0ff0888888ff0f0f888888ff0f00888888ff0000888888f00f008888880f0f00888888000000777777f0f0ff7777770ff0ff77777700ffff77777700f0ff77777700f0f077777700f00f77777700f0007777770000ff7777770000f077777700000f666666fff0ff666666ff00ff66666600ff0066666600f000555555f0ffff555555f0ff0f5555550f00f05555550000f0444444fff0f0444444f0fff0444444f0f0ff444444f0f0f0444444f0f000444444f000f044444400f0f0444444000000333333f0000f3333330fffff3333330ffff033333300000f222222fff00f2222220fff0f2222220ff0ff2222220ff00f2222220ff0002222220f000f22222200f00f222222000000111111f00fff1111110f0fff11111100ffff111111000fff111111000ff0111111000f0f1111110000ff111111000000000000f000000000000f000000000000f000000000000f000000000000f000000000000f000000000000

def S (s j : Nat) : List Nat :=
  (List.range (fld (LT s) 4 j)).map (fun t => fld VT 48 (fld (DT s) 7 (5*j+t)))
def idx (s : Nat) (zs : List Nat) : Nat := bsr (HT s) 32 (hk zs) 12 0 (NN s)
def Z (s : Nat) := bar 24 S NN idx id [] s

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h2x0 : span (Z 2) 8 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h2x8 : span (Z 2) 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h2x16 : span (Z 2) 8 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h2x24 : span (Z 2) 8 24 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h2x32 : span (Z 2) 8 32 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h2x40 : span (Z 2) 8 40 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h2x48 : span (Z 2) 8 48 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h2x56 : span (Z 2) 8 56 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h2x64 : span (Z 2) 8 64 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h2x72 : span (Z 2) 8 72 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h2x80 : span (Z 2) 8 80 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h2x88 : span (Z 2) 2 88 = true := by decide +kernel
theorem z2 : span (Z 2) 90 0 = true := (@span_join (Z 2) 48 0 42 (@span_join (Z 2) 24 0 24 (@span_join (Z 2) 8 0 16 h2x0 (@span_join (Z 2) 8 8 8 h2x8 h2x16)) (@span_join (Z 2) 8 24 16 h2x24 (@span_join (Z 2) 8 32 8 h2x32 h2x40))) (@span_join (Z 2) 24 48 18 (@span_join (Z 2) 8 48 16 h2x48 (@span_join (Z 2) 8 56 8 h2x56 h2x64)) (@span_join (Z 2) 8 72 10 h2x72 (@span_join (Z 2) 8 80 2 h2x80 h2x88))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x0 : span (Z 3) 8 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x8 : span (Z 3) 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x16 : span (Z 3) 8 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x24 : span (Z 3) 8 24 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x32 : span (Z 3) 8 32 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x40 : span (Z 3) 8 40 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x48 : span (Z 3) 8 48 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x56 : span (Z 3) 8 56 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x64 : span (Z 3) 8 64 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x72 : span (Z 3) 8 72 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x80 : span (Z 3) 8 80 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x88 : span (Z 3) 8 88 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x96 : span (Z 3) 8 96 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x104 : span (Z 3) 8 104 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x112 : span (Z 3) 8 112 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x120 : span (Z 3) 8 120 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x128 : span (Z 3) 8 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x136 : span (Z 3) 8 136 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x144 : span (Z 3) 8 144 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x152 : span (Z 3) 8 152 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x160 : span (Z 3) 8 160 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x168 : span (Z 3) 8 168 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x176 : span (Z 3) 8 176 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x184 : span (Z 3) 8 184 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x192 : span (Z 3) 8 192 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x200 : span (Z 3) 8 200 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x208 : span (Z 3) 8 208 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x216 : span (Z 3) 8 216 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h3x224 : span (Z 3) 3 224 = true := by decide +kernel
theorem z3 : span (Z 3) 227 0 = true := (@span_join (Z 3) 112 0 115 (@span_join (Z 3) 56 0 56 (@span_join (Z 3) 24 0 32 (@span_join (Z 3) 8 0 16 h3x0 (@span_join (Z 3) 8 8 8 h3x8 h3x16)) (@span_join (Z 3) 16 24 16 (@span_join (Z 3) 8 24 8 h3x24 h3x32) (@span_join (Z 3) 8 40 8 h3x40 h3x48))) (@span_join (Z 3) 24 56 32 (@span_join (Z 3) 8 56 16 h3x56 (@span_join (Z 3) 8 64 8 h3x64 h3x72)) (@span_join (Z 3) 16 80 16 (@span_join (Z 3) 8 80 8 h3x80 h3x88) (@span_join (Z 3) 8 96 8 h3x96 h3x104)))) (@span_join (Z 3) 56 112 59 (@span_join (Z 3) 24 112 32 (@span_join (Z 3) 8 112 16 h3x112 (@span_join (Z 3) 8 120 8 h3x120 h3x128)) (@span_join (Z 3) 16 136 16 (@span_join (Z 3) 8 136 8 h3x136 h3x144) (@span_join (Z 3) 8 152 8 h3x152 h3x160))) (@span_join (Z 3) 32 168 27 (@span_join (Z 3) 16 168 16 (@span_join (Z 3) 8 168 8 h3x168 h3x176) (@span_join (Z 3) 8 184 8 h3x184 h3x192)) (@span_join (Z 3) 16 200 11 (@span_join (Z 3) 8 200 8 h3x200 h3x208) (@span_join (Z 3) 8 216 3 h3x216 h3x224)))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x0 : span (Z 4) 8 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x8 : span (Z 4) 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x16 : span (Z 4) 8 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x24 : span (Z 4) 8 24 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x32 : span (Z 4) 8 32 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x40 : span (Z 4) 8 40 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x48 : span (Z 4) 8 48 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x56 : span (Z 4) 8 56 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x64 : span (Z 4) 8 64 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x72 : span (Z 4) 8 72 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x80 : span (Z 4) 8 80 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x88 : span (Z 4) 8 88 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x96 : span (Z 4) 8 96 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x104 : span (Z 4) 8 104 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x112 : span (Z 4) 8 112 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x120 : span (Z 4) 8 120 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x128 : span (Z 4) 8 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x136 : span (Z 4) 8 136 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x144 : span (Z 4) 8 144 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x152 : span (Z 4) 8 152 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x160 : span (Z 4) 8 160 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x168 : span (Z 4) 8 168 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x176 : span (Z 4) 8 176 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x184 : span (Z 4) 8 184 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x192 : span (Z 4) 8 192 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x200 : span (Z 4) 8 200 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x208 : span (Z 4) 8 208 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x216 : span (Z 4) 8 216 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x224 : span (Z 4) 8 224 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x232 : span (Z 4) 8 232 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x240 : span (Z 4) 7 240 = true := by decide +kernel
theorem z4 : span (Z 4) 247 0 = true := (@span_join (Z 4) 120 0 127 (@span_join (Z 4) 56 0 64 (@span_join (Z 4) 24 0 32 (@span_join (Z 4) 8 0 16 h4x0 (@span_join (Z 4) 8 8 8 h4x8 h4x16)) (@span_join (Z 4) 16 24 16 (@span_join (Z 4) 8 24 8 h4x24 h4x32) (@span_join (Z 4) 8 40 8 h4x40 h4x48))) (@span_join (Z 4) 32 56 32 (@span_join (Z 4) 16 56 16 (@span_join (Z 4) 8 56 8 h4x56 h4x64) (@span_join (Z 4) 8 72 8 h4x72 h4x80)) (@span_join (Z 4) 16 88 16 (@span_join (Z 4) 8 88 8 h4x88 h4x96) (@span_join (Z 4) 8 104 8 h4x104 h4x112)))) (@span_join (Z 4) 64 120 63 (@span_join (Z 4) 32 120 32 (@span_join (Z 4) 16 120 16 (@span_join (Z 4) 8 120 8 h4x120 h4x128) (@span_join (Z 4) 8 136 8 h4x136 h4x144)) (@span_join (Z 4) 16 152 16 (@span_join (Z 4) 8 152 8 h4x152 h4x160) (@span_join (Z 4) 8 168 8 h4x168 h4x176))) (@span_join (Z 4) 32 184 31 (@span_join (Z 4) 16 184 16 (@span_join (Z 4) 8 184 8 h4x184 h4x192) (@span_join (Z 4) 8 200 8 h4x200 h4x208)) (@span_join (Z 4) 16 216 15 (@span_join (Z 4) 8 216 8 h4x216 h4x224) (@span_join (Z 4) 8 232 7 h4x232 h4x240)))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x0 : span (Z 5) 8 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x8 : span (Z 5) 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x16 : span (Z 5) 5 16 = true := by decide +kernel
theorem z5 : span (Z 5) 21 0 = true := (@span_join (Z 5) 8 0 13 h5x0 (@span_join (Z 5) 8 8 5 h5x8 h5x16))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x0 : span (Z 6) 1 0 = true := by decide +kernel
theorem z6 : span (Z 6) 1 0 = true := h6x0

theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · simp [NN]
  · simp [NN]
  · intro i hi
    exact span_ok z2 i (Nat.zero_le i) (by simpa [NN] using hi)
  · intro i hi
    exact span_ok z3 i (Nat.zero_le i) (by simpa [NN] using hi)
  · intro i hi
    exact span_ok z4 i (Nat.zero_le i) (by simpa [NN] using hi)
  · intro i hi
    exact span_ok z5 i (Nat.zero_le i) (by simpa [NN] using hi)
  · intro i hi
    exact span_ok z6 i (Nat.zero_le i) (by simpa [NN] using hi)

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : NatRun (mask 24) (goal 24) s xsG) : False := by
  have hl := run_len h
  have hlen : xsG.length = 4 := by decide +kernel
  rw [hlen] at hl
  have hlo : 3 ≤ s := by omega
  interval_cases s
  · exact bar_all (ori := id) (fun h => h) checked 3 (by decide) 226 (by decide)
      (Run.perm (by decide +kernel : xsG.Perm (S 3 226)) h)
  · exact bar_all (ori := id) (fun h => h) checked 4 (by decide) 244 (by decide)
      (Run.perm (by decide +kernel : xsG.Perm (S 4 244)) h)
  · exact bar_all (ori := id) (fun h => h) checked 5 (by decide) 19 (by decide)
      (Run.perm (by decide +kernel : xsG.Perm (S 5 19)) h)
  · exact bar_all (ori := id) (fun h => h) checked 6 (by decide) 0 (by decide)
      (Run.perm (by decide +kernel : xsG.Perm (S 6 0)) h)


theorem Run.swap_binary {α : Type} {i : α → α} {m j : α → α → α}
    {goal : α} {s : Nat} {xs : List α} (h : Run i m j goal s xs) : Run i j m goal s xs := by
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm hp ih
  | one save _ ih => exact Run.one save ih
  | two c ka kb _ ih =>
    cases c
    · exact Run.two true ka kb ih
    · exact Run.two false ka kb ih

def twoOfFour : BFn 4 := fun x =>
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 3) || (x 2 && x 3)

def flipFn (f : BFn 4) : BFn 4 := fun x => !(f (fun i => !(x i)))

theorem excludeTwo : ¬ HasCircuitSize 4 twoOfFour 6 := by
  intro h
  obtain ⟨s, hs, ws, sub, run⟩ := exists_run twoOfFour ⟨fun _ => false, fun _ => true, by decide⟩ 6 h
  have mapped : Run (invF (n := 4)) joinF meetF (flipFn twoOfFour) s (ws.map flipFn) := by
    apply Run.map flipFn (h := run)
    · intro a
      rfl
    · intro a b
      funext x
      simp [flipFn, meetF, joinF]
    · intro a b
      funext x
      simp [flipFn, meetF, joinF]
  have eq : flipFn twoOfFour = fG := by decide +kernel
  rw [eq] at mapped
  have rt : NatRun (mask 24) (encL fG rowsG) s ((ws.map flipFn).map fun a => encL a rowsG) :=
    Run.map (fun a : BFn 4 => encL a rowsG)
      (fun a => by rw [maskG]; exact encL_inv a rowsG)
      (fun a b => encL_and a b rowsG) (fun a b => encL_or a b rowsG) mapped.swap_binary
  rw [enc_goalG] at rt
  refine no_subG noRunFull s hs _ ?_ rt
  rw [← enc_inputsG]
  have mappedSub := sub.map flipFn
  have proj : (List.ofFn fun (i : Fin 4) => (fun x : Fin 4 → Bool => x i)).map flipFn =
      List.ofFn fun (i : Fin 4) => (fun x : Fin 4 → Bool => x i) := by decide +kernel
  rw [proj] at mappedSub
  exact mappedSub.map _

end K

namespace E
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool


def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs {n : ℕ} : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  omega

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim_one (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s', s' + 1 ≤ s ∧ HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length + 1 ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨acc.2.length, hlen, ⟨acc.2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Sum.inl false) ≠ Sum.inl c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Sum.inl false) = Sum.inl b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Sum.inl false)
      = Sum.inl b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      statVal (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y))
        ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) with
  | inl c => exact absurd hst (hout b c)
  | inr j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

theorem snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]

theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨s', hs, h'⟩ := gate_elim_one n _ b s hdep' hnc' hg
  refine ⟨s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

theorem gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

end E

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Fr : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4276682472 * 2 ^ 32 + 4276660392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def Frf : (Fin 6 → Bool) → Bool := fun x => Fr (Function.update x 4 false)
def Frff : (Fin 6 → Bool) → Bool := fun x => Frf (Function.update x 3 false)
def Prff : Fin 6 → Fin 4 := fun j => if j.val = 0 then 0 else if j.val = 1 then 1 else if j.val = 2 then 2 else if j.val = 5 then 3 else 0
def Grff : (Fin 4 → Bool) → Bool := fun y => Frff (y ∘ Prff)
set_option maxHeartbeats 0 in
theorem c0rff : S.s0 (2 ^ (2 ^ 4) - 1) (S.tt 4 Grff) (4 - 1) (S.vars 4) = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem c1rff : S.s1 (2 ^ (2 ^ 4) - 1) (S.tt 4 Grff) 4 (S.vars 4) (S.vars 4) = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem Lrff (s : ℕ) (h : HasCircuitSize 6 Frff s) : 5 ≤ s :=
  S.final 4 5 Grff (by decide) (by decide +kernel) (Or.inr c0rff) (Or.inr ⟨by decide, c1rff⟩) s (E.relabel_size Prff Frff s h)

def Frft : (Fin 6 → Bool) → Bool := fun x => Frf (Function.update x 3 true)
def Prft : Fin 6 → Fin 4 := fun j => if j.val = 0 then 0 else if j.val = 1 then 1 else if j.val = 2 then 2 else if j.val = 5 then 3 else 0
def Grft : (Fin 4 → Bool) → Bool := fun y => Frft (y ∘ Prft)
set_option maxHeartbeats 0 in
theorem c0rft : S.s0 (2 ^ (2 ^ 4) - 1) (S.tt 4 Grft) (4 - 1) (S.vars 4) = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem c1rft : S.s1 (2 ^ (2 ^ 4) - 1) (S.tt 4 Grft) 4 (S.vars 4) (S.vars 4) = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem Lrft (s : ℕ) (h : HasCircuitSize 6 Frft s) : 5 ≤ s :=
  S.final 4 5 Grft (by decide) (by decide +kernel) (Or.inr c0rft) (Or.inr ⟨by decide, c1rft⟩) s (E.relabel_size Prft Frft s h)

theorem Lrf (s : ℕ) (h : HasCircuitSize 6 Frf s) : 7 ≤ s := by
  have hdep : ∃ x : Fin 6 → Bool, Frf (Function.update x 3 (!x 3)) ≠ Frf x :=
    ⟨(fun j => (33 : ℕ).testBit j.val), by decide +kernel⟩
  have hnc : ∀ b : Bool, ∃ x y : Fin 6 → Bool, Frf (Function.update x 3 b) ≠ Frf (Function.update y 3 b) := by
    intro b
    cases b
    · exact ⟨(fun j => (0 : ℕ).testBit j.val), (fun j => (3 : ℕ).testBit j.val), by decide +kernel⟩
    · exact ⟨(fun j => (0 : ℕ).testBit j.val), (fun j => (3 : ℕ).testBit j.val), by decide +kernel⟩
  obtain ⟨b, s1, hs, h1⟩ := E.gate_elim_at 5 Frf 3 s hdep hnc h
  cases b with
  | false => have := Lrff s1 h1; omega
  | true => have := Lrft s1 h1; omega

def Frt : (Fin 6 → Bool) → Bool := fun x => Fr (Function.update x 4 true)
def Prt : Fin 6 → Fin 4 := fun j => if j.val = 0 then 0 else if j.val = 1 then 1 else if j.val = 2 then 2 else if j.val = 3 then 3 else 0
def Grt : (Fin 4 → Bool) → Bool := fun y => Frt (y ∘ Prt)
theorem Lrt (s : ℕ) (h : HasCircuitSize 6 Frt s) : 7 ≤ s := by
  have c : HasCircuitSize 4 Grt s := E.relabel_size Prt Frt s h
  have e : Grt = K.twoOfFour := by decide +kernel
  rw [e] at c
  by_contra! small
  obtain ⟨C, fan, sz, correct⟩ := c
  exact K.excludeTwo ⟨C, fan, by omega, correct⟩

theorem Lr (s : ℕ) (h : HasCircuitSize 6 Fr s) : 9 ≤ s := by
  have hdep : ∃ x : Fin 6 → Bool, Fr (Function.update x 4 (!x 4)) ≠ Fr x :=
    ⟨(fun j => (6 : ℕ).testBit j.val), by decide +kernel⟩
  have hnc : ∀ b : Bool, ∃ x y : Fin 6 → Bool, Fr (Function.update x 4 b) ≠ Fr (Function.update y 4 b) := by
    intro b
    cases b
    · exact ⟨(fun j => (0 : ℕ).testBit j.val), (fun j => (3 : ℕ).testBit j.val), by decide +kernel⟩
    · exact ⟨(fun j => (0 : ℕ).testBit j.val), (fun j => (3 : ℕ).testBit j.val), by decide +kernel⟩
  obtain ⟨b, s1, hs, h1⟩ := E.gate_elim_at 5 Fr 4 s hdep hnc h
  cases b with
  | false => have := Lrf s1 h1; omega
  | true => have := Lrt s1 h1; omega

end PEqualNP.Outside.L_meta_12643_aux

namespace PEqualNP.Outside.L_meta_12643_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- New here: the lower bound above (for every AND/OR/NOT circuit) meets this monotone circuit with 9 gates.
def witness : Circuit := ⟨[⟨.or, [4, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [9, 10]⟩, ⟨.and, [6, 11]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [12, 13]⟩], 14⟩

theorem witness_mono : Monotone2 witness := by
  simp [Monotone2, witness]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem witness_eval : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = Fr x := by
  decide +kernel

end PEqualNP.Outside.L_meta_12643_aux

theorem PEqualNP.Outside.L_meta_12643 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682472 * 2 ^ 32 + 4276660392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682472 * 2 ^ 32 + 4276660392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  have large := PEqualNP.Outside.L_meta_12643_aux.Lr s hs
  have hw : PEqualNP.Outside.L_meta_12643_aux.witness.size = 9 := rfl
  exact ⟨PEqualNP.Outside.L_meta_12643_aux.witness, PEqualNP.Outside.L_meta_12643_aux.witness_mono, by omega, PEqualNP.Outside.L_meta_12643_aux.witness_eval⟩
