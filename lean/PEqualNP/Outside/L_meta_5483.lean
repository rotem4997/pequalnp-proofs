import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5483

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

def prs2 : List ℕ → List (ℕ × ℕ × List ℕ)
  | [] => []
  | a :: l => ((picks l).map fun p => (a, p.1, p.2)) ++ (prs2 l).map fun q => (q.1, q.2.1, a :: q.2.2)

theorem prs2_mem (V : ℕ → ℕ) : ∀ (U : List ℕ) (i i' : ℕ), i ∈ U → i' ∈ U → i ≠ i' →
    (V i, V i', ((U.erase i).erase i').map V) ∈ prs2 (U.map V) ∨
    (V i', V i, ((U.erase i).erase i').map V) ∈ prs2 (U.map V)
  | [], i, i', h, _, _ => by simp at h
  | a :: l, i, i', hi, hi', hne => by
    by_cases e : i = a
    · subst e
      have h2 : i' ∈ l := by simpa [hne.symm] using hi'
      left
      rw [List.erase_cons_head]
      simp only [prs2, List.map_cons, List.mem_append, List.mem_map]
      exact Or.inl ⟨_, picks_mem V l i' h2, rfl⟩
    · by_cases e' : i' = a
      · subst e'
        have h2 : i ∈ l := by simpa [e] using hi
        right
        rw [List.erase_comm, List.erase_cons_head]
        simp only [prs2, List.map_cons, List.mem_append, List.mem_map]
        exact Or.inl ⟨_, picks_mem V l i h2, rfl⟩
      · have h1 : i ∈ l := by simpa [e] using hi
        have h2 : i' ∈ l := by simpa [e'] using hi'
        rw [List.erase_cons_tail (by simpa using fun h' : a = i => e h'.symm),
          List.erase_cons_tail (by simpa using fun h' : a = i' => e' h'.symm)]
        simp only [prs2, List.map_cons, List.mem_append, List.mem_map]
        rcases prs2_mem V l i i' h1 h2 hne with h | h
        · exact Or.inl (Or.inr ⟨_, h, rfl⟩)
        · exact Or.inr (Or.inr ⟨_, h, rfl⟩)

def detc (F t : ℕ) : List ℕ → ℕ → Bool
  | [], m => (t &&& m == 0) || (t &&& m == m)
  | a :: l, m => detc F t l (m &&& a) && detc F t l (m &&& (F ^^^ a))

def s0 (F t : ℕ) : ℕ → List ℕ → Bool
  | 0, us => us == [t]
  | r + 1, us => detc F t us F && (prs2 us).any fun q =>
      s0 F t r ((q.1 &&& q.2.1) :: q.2.2) || s0 F t r ((q.1 ||| q.2.1) :: q.2.2)

def detE (F t : ℕ) : ℕ → List ℕ → List ℕ → Bool
  | 0, _, us => detc F t us F
  | e + 1, W, us => (0 :: W).any fun w => detE F t e W (w :: us)

def sE (F t : ℕ) : ℕ → ℕ → List ℕ → List ℕ → Bool
  | r, 0, _, us => s0 F t r us
  | 0, _ + 1, _, _ => false
  | r + 1, e + 1, W, us => detE F t (e + 1) W us && (((prs2 us).any fun q =>
        sE F t r (e + 1) ((q.1 &&& q.2.1) :: W) ((q.1 &&& q.2.1) :: q.2.2) ||
        sE F t r (e + 1) ((q.1 ||| q.2.1) :: W) ((q.1 ||| q.2.1) :: q.2.2)) ||
      (picks us).any fun q => ((0 :: W).any fun w => sE F t r e ((q.1 &&& w) :: W) ((q.1 &&& w) :: q.2) ||
        sE F t r e ((q.1 ||| w) :: W) ((q.1 ||| w) :: q.2)) ||
      sE F t r e ((F ^^^ q.1) :: W) ((F ^^^ q.1) :: q.2)) ||
    (match e with
      | 0 => false
      | d + 1 => detE F t (d + 2) W us && ((0 :: W).any fun w => ((0 :: W).any fun w' =>
          sE F t r d ((w &&& w') :: W) ((w &&& w') :: us) ||
          sE F t r d ((w ||| w') :: W) ((w ||| w') :: us)) ||
          sE F t r d ((F ^^^ w) :: W) ((F ^^^ w) :: us)))

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

def DE (N t e : ℕ) (W us : List ℕ) : Prop :=
  ∃ ws : List ℕ, ws.length = e ∧ (∀ w ∈ ws, w ∈ 0 :: W) ∧ Det N t (ws ++ us)

theorem detE_of {N t : ℕ} (W : List ℕ) : ∀ (ws us : List ℕ), (∀ w ∈ ws, w ∈ 0 :: W) →
    Det N t (ws ++ us) → detE (2 ^ N - 1) t ws.length W us = true
  | [], us, _, h => detc_full h
  | w :: ws, us, hw, h => by
    simp only [List.length_cons, detE, List.any_eq_true]
    refine ⟨w, hw w (by simp), detE_of W ws (w :: us) (fun x hx => hw x (by simp [hx])) ?_⟩
    intro p hp q hq hall
    refine h p hp q hq fun a ha => hall a ?_
    simp only [List.cons_append, List.mem_cons, List.mem_append] at ha ⊢
    tauto

theorem DE_det {N t e : ℕ} {W us : List ℕ} (h : DE N t e W us) :
    detE (2 ^ N - 1) t e W us = true := by
  obtain ⟨ws, rfl, h1, h2⟩ := h
  exact detE_of W ws us h1 h2

/-- replace the new value by extra old wires `xs` -/
theorem DE_step {N t e : ℕ} {W us us' xs : List ℕ} {v : ℕ} (h : DE N t e (v :: W) (v :: us'))
    (hx : ∀ x ∈ xs, x ∈ 0 :: W) (hsub : ∀ a ∈ us', a ∈ us)
    (hv : ∀ p < N, ∀ q < N, (∀ a ∈ xs, a.testBit p = a.testBit q) →
      (∀ a ∈ us, a.testBit p = a.testBit q) → v.testBit p = v.testBit q) :
    DE N t (xs.length + e) W us := by
  classical
  obtain ⟨ws, rfl, h1, h2⟩ := h
  refine ⟨xs ++ ws.map (fun w => if w = v then 0 else w), by simp, ?_, ?_⟩
  · intro w hw
    rcases List.mem_append.1 hw with hw | hw
    · exact hx w hw
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hw
      split_ifs with e1
      · simp
      · have := h1 y hy
        simp only [List.mem_cons] at this ⊢
        tauto
  · intro p hp q hq hall
    have hxs : ∀ a ∈ xs, a.testBit p = a.testBit q := fun a ha => hall a (by simp [ha])
    have hus : ∀ a ∈ us, a.testBit p = a.testBit q := fun a ha => hall a (by simp [ha])
    have hvv := hv p hp q hq hxs hus
    refine h2 p hp q hq fun a ha => ?_
    rcases List.mem_append.1 ha with ha | ha
    · by_cases e1 : a = v
      · rw [e1]; exact hvv
      · have := hall a (List.mem_append_left _ (List.mem_append_right _
          (List.mem_map.2 ⟨a, ha, if_neg e1⟩)))
        exact this
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact hvv
      · exact hus a (hsub a ha)

theorem search (N n m o t : ℕ) (V : ℕ → ℕ) (R : ℕ → List ℕ) (ho : V o = t)
    (Hu : ∀ k < m, n + k = o ∨ ∃ j, k + 1 ≤ j ∧ j < m ∧ n + k ∈ R j)
    (hG : ∀ j < m, (∃ i i', R j = [i, i'] ∧
        (V (n + j) = (if i < n + j then V i else 0) &&& (if i' < n + j then V i' else 0) ∨
         V (n + j) = (if i < n + j then V i else 0) ||| (if i' < n + j then V i' else 0))) ∨
      (∃ i, R j = [i] ∧ (V (n + j) = (if i < n + j then V i else 0) ∨
         V (n + j) = (2 ^ N - 1) ^^^ (if i < n + j then V i else 0))) ∨
      (R j = [] ∧ (V (n + j) = 0 ∨ V (n + j) = 2 ^ N - 1))) :
    ∀ r k (U : List ℕ), k + r = m → U.Nodup → U ≠ [] →
      (∀ i ∈ U, i < n + k ∧ (i = o ∨ ∃ j, k ≤ j ∧ j < m ∧ i ∈ R j)) →
      U.length ≤ r + 1 ∧ ∀ e, U.length + e = r + 1 →
        sE (2 ^ N - 1) t r e (Wl n V k) (U.map V) = true ∧ DE N t e (Wl n V k) (U.map V) := by
  intro r
  induction r with
  | zero =>
    intro k U hk hnd hne hU
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
    have hpos := List.length_pos_iff.2 hne
    refine ⟨by omega, fun e he => ?_⟩
    have e0 : e = 0 := by omega
    subst e0
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 (show U.length = 1 by omega)
    have ea := all a (by simp)
    subst ea
    refine ⟨by simp [sE, s0, ho], [], rfl, by simp, fun p _ q _ h => ?_⟩
    have := h (V a) (by simp)
    rw [ho] at this; exact this
  | succ r ih =>
    intro k U hk hnd hne hU
    have hkm : k < m := by omega
    set v := V (n + k) with hv
    have step : ∀ U' : List ℕ, U'.Nodup → (∀ i ∈ U', i ∈ U ∧ i ∉ R k) →
        U'.length ≤ r ∧ ∀ e, U'.length + 1 + e = r + 1 →
          sE (2 ^ N - 1) t r e (v :: Wl n V k) (v :: U'.map V) = true ∧
          DE N t e (v :: Wl n V k) (v :: U'.map V) := by
      intro U' hnd' hU'
      obtain ⟨q1, q2⟩ := ih (k + 1) ((n + k) :: U') (by omega) (by
        rw [List.nodup_cons]
        refine ⟨fun h => ?_, hnd'⟩
        have := (hU _ (hU' _ h).1).1
        omega) (by simp) (by
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
      rw [List.length_cons] at q1 q2
      exact ⟨by omega, fun e he => q2 e he⟩
    have hlenE : ∀ i ∈ U, (U.erase i).length + 1 = U.length := by
      intro i hi
      rw [List.length_erase_of_mem hi]
      have := List.length_pos_of_mem hi
      omega
    have w_mem : ∀ i, (if i < n + k then V i else 0) ∈ 0 :: Wl n V k := by
      intro i
      split_ifs with h
      · exact List.mem_cons_of_mem _ (Wl_mem n V k i h)
      · simp
    -- no unread wire is read
    have f0 : (∀ x ∈ U, x ∉ R k) →
        ((∃ w ∈ 0 :: Wl n V k, ∃ w' ∈ 0 :: Wl n V k, v = w &&& w' ∨ v = w ||| w') ∨
          ∃ w ∈ 0 :: Wl n V k, v = (2 ^ N - 1) ^^^ w) →
        U.length ≤ r + 1 + 1 ∧ ∀ e, U.length + e = r + 1 + 1 →
          sE (2 ^ N - 1) t (r + 1) e (Wl n V k) (U.map V) = true ∧ DE N t e (Wl n V k) (U.map V) := by
      intro h hval
      obtain ⟨q1, q2⟩ := step U hnd fun i hi => ⟨hi, h i hi⟩
      refine ⟨by omega, fun e he => ?_⟩
      obtain ⟨d, rfl⟩ : ∃ d, e = d + 2 := ⟨e - 2, by omega⟩
      obtain ⟨s, D⟩ := q2 d (by omega)
      have hDE : DE N t (d + 2) (Wl n V k) (U.map V) := by
        rcases hval with ⟨w, hw, w', hw', e1⟩ | ⟨w, hw, e1⟩
        · have := DE_step (xs := [w, w']) (us := U.map V) D (by
            intro x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · exact hw
            · have : x = w' := by simpa using hx
              rw [this]; exact hw') (fun a ha => ha) (by
            intro p _ q _ hx _
            have a1 := hx w (by simp)
            have a2 := hx w' (by simp)
            rcases e1 with e1 | e1 <;> rw [e1]
            · rw [Nat.testBit_and, Nat.testBit_and, a1, a2]
            · rw [Nat.testBit_or, Nat.testBit_or, a1, a2])
          rw [show [w, w'].length + d = d + 2 by simp; omega] at this
          exact this
        · have := DE_step (xs := [w, 0]) (us := U.map V) D (by
            intro x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · exact hw
            · simp at hx; simp [hx]) (fun a ha => ha) (by
            intro p hp q hq hx _
            have a1 := hx w (by simp)
            rw [e1, Nat.testBit_xor, Nat.testBit_xor, a1, full_bit N p hp, full_bit N q hq])
          rw [show [w, 0].length + d = d + 2 by simp; omega] at this
          exact this
      refine ⟨?_, hDE⟩
      simp only [sE, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true]
      right
      refine ⟨DE_det hDE, ?_⟩
      rcases hval with ⟨w, hw, w', hw', e1⟩ | ⟨w, hw, e1⟩
      · refine ⟨w, hw, Or.inl ⟨w', hw', ?_⟩⟩
        rcases e1 with e1 | e1
        · left; rw [← e1]; exact s
        · right; rw [← e1]; exact s
      · exact ⟨w, hw, Or.inr (by rw [← e1]; exact s)⟩
    have f1 : ∀ i ∈ U, (∀ x ∈ U, x ∈ R k → x = i) →
        ((∃ w ∈ 0 :: Wl n V k, v = V i &&& w ∨ v = V i ||| w) ∨ v = (2 ^ N - 1) ^^^ V i) →
        U.length ≤ r + 1 + 1 ∧ ∀ e, U.length + e = r + 1 + 1 →
          sE (2 ^ N - 1) t (r + 1) e (Wl n V k) (U.map V) = true ∧ DE N t e (Wl n V k) (U.map V) := by
      intro i hi h1 hval
      obtain ⟨q1, q2⟩ := step (U.erase i) (hnd.erase i) (by
        intro x hx
        obtain ⟨hxi, hxU⟩ := (hnd.mem_erase_iff).1 hx
        exact ⟨hxU, fun hR => hxi (h1 x hxU hR)⟩)
      have hl := hlenE i hi
      refine ⟨by omega, fun e he => ?_⟩
      obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
      obtain ⟨s, D⟩ := q2 d (by omega)
      have hmem := picks_mem V U i hi
      have sub : ∀ a ∈ (U.erase i).map V, a ∈ U.map V := by
        intro a ha
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
        exact List.mem_map_of_mem (List.mem_of_mem_erase hx)
      have hDE : DE N t (d + 1) (Wl n V k) (U.map V) := by
        rcases hval with ⟨w, hw, e1⟩ | e1
        · have := DE_step (xs := [w]) (us := U.map V) D (by simpa using hw) sub (by
            intro p _ q _ hx hu
            have a1 := hx w (by simp)
            have a2 := hu (V i) (List.mem_map_of_mem hi)
            rcases e1 with e1 | e1 <;> rw [e1]
            · rw [Nat.testBit_and, Nat.testBit_and, a1, a2]
            · rw [Nat.testBit_or, Nat.testBit_or, a1, a2])
          rw [show [w].length + d = d + 1 by simp; omega] at this
          exact this
        · have := DE_step (xs := [0]) (us := U.map V) D (by simp) sub (by
            intro p hp q hq _ hu
            have a2 := hu (V i) (List.mem_map_of_mem hi)
            rw [e1, Nat.testBit_xor, Nat.testBit_xor, a2, full_bit N p hp, full_bit N q hq])
          rw [show [0].length + d = d + 1 by simp; omega] at this
          exact this
      refine ⟨?_, hDE⟩
      simp only [sE, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true]
      left
      refine ⟨DE_det hDE, Or.inr ⟨_, hmem, ?_⟩⟩
      rcases hval with ⟨w, hw, e1 | e1⟩ | e1
      · exact Or.inl ⟨w, hw, Or.inl (by rw [← e1]; exact s)⟩
      · exact Or.inl ⟨w, hw, Or.inr (by rw [← e1]; exact s)⟩
      · exact Or.inr (by rw [← e1]; exact s)
    have f2 : ∀ i ∈ U, ∀ i' ∈ U, i ≠ i' → (∀ x ∈ R k, x = i ∨ x = i') →
        (v = V i &&& V i' ∨ v = V i ||| V i') →
        U.length ≤ r + 1 + 1 ∧ ∀ e, U.length + e = r + 1 + 1 →
          sE (2 ^ N - 1) t (r + 1) e (Wl n V k) (U.map V) = true ∧ DE N t e (Wl n V k) (U.map V) := by
      intro i hi i' hi' hne' hR hval
      have hi2 : i' ∈ U.erase i := (hnd.mem_erase_iff).2 ⟨hne'.symm, hi'⟩
      have hl := hlenE i hi
      have hl2 : ((U.erase i).erase i').length + 1 = (U.erase i).length := by
        rw [List.length_erase_of_mem hi2]
        have := List.length_pos_of_mem hi2
        omega
      obtain ⟨q1, q2⟩ := step ((U.erase i).erase i') ((hnd.erase i).erase i') (by
        intro x hx
        obtain ⟨h1, h2⟩ := ((hnd.erase i).mem_erase_iff).1 hx
        obtain ⟨h3, h4⟩ := (hnd.mem_erase_iff).1 h2
        exact ⟨h4, fun hR' => (hR x hR').elim h3 h1⟩)
      have m1 := prs2_mem V U i i' hi hi' hne'
      have sub : ∀ a ∈ ((U.erase i).erase i').map V, a ∈ U.map V := by
        intro a ha
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
        exact List.mem_map_of_mem (List.mem_of_mem_erase (List.mem_of_mem_erase hx))
      refine ⟨by omega, fun e he => ?_⟩
      obtain ⟨s, D⟩ := q2 e (by omega)
      have hDE : DE N t e (Wl n V k) (U.map V) := by
        have := DE_step (xs := []) (us := U.map V) D (by simp) sub (by
          intro p _ q _ _ hu
          have a1 := hu (V i) (List.mem_map_of_mem hi)
          have a2 := hu (V i') (List.mem_map_of_mem hi')
          rcases hval with e1 | e1 <;> rw [e1]
          · rw [Nat.testBit_and, Nat.testBit_and, a1, a2]
          · rw [Nat.testBit_or, Nat.testBit_or, a1, a2])
        simpa using this
      refine ⟨?_, hDE⟩
      rcases e with _ | e
      · simp only [sE] at s ⊢
        simp only [s0, Bool.and_eq_true, List.any_eq_true, Bool.or_eq_true]
        rcases m1 with m1 | m1 <;> refine ⟨DE_det hDE, _, m1, ?_⟩
        · rcases hval with e1 | e1
          · left; rw [← e1]; exact s
          · right; rw [← e1]; exact s
        · rcases hval with e1 | e1
          · left; rw [Nat.and_comm, ← e1]; exact s
          · right; rw [Nat.or_comm, ← e1]; exact s
      · simp only [sE, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true]
        left
        rcases m1 with m1 | m1 <;> refine ⟨DE_det hDE, Or.inl ⟨_, m1, ?_⟩⟩
        · rcases hval with e1 | e1
          · left; rw [← e1]; exact s
          · right; rw [← e1]; exact s
        · rcases hval with e1 | e1
          · left; rw [Nat.and_comm, ← e1]; exact s
          · right; rw [Nat.or_comm, ← e1]; exact s
    rcases hG k hkm with ⟨i, i', hR, hval⟩ | ⟨i, hR, hval⟩ | ⟨hR, hval⟩
    · by_cases hi : i ∈ U
      · have hi' := (hU i hi).1
        by_cases h2 : i' ∈ U ∧ i ≠ i'
        · have hi2 := (hU i' h2.1).1
          rw [if_pos hi', if_pos hi2] at hval
          exact f2 i hi i' h2.1 h2.2 (by rw [hR]; simp) hval
        · rw [if_pos hi'] at hval
          refine f1 i hi ?_ (Or.inl ⟨_, w_mem i', hval⟩)
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
        · refine f0 (fun x hx hxR => ?_) (Or.inl ⟨_, w_mem i, _, w_mem i', hval⟩)
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
      · refine f0 (fun x hx hxR => ?_) ?_
        · rw [hR] at hxR
          have : x = i := by simpa using hxR
          exact hi (this ▸ hx)
        · rcases hval with e | e
          · exact Or.inl ⟨_, w_mem i, 0, by simp, Or.inr (by rw [Nat.or_zero]; exact e)⟩
          · exact Or.inr ⟨_, w_mem i, e⟩
    · refine f0 (fun x _ hxR => by rw [hR] at hxR; simp at hxR) ?_
      rcases hval with e | e
      · exact Or.inl ⟨0, by simp, 0, by simp, Or.inl (by rw [Nat.and_zero]; exact e)⟩
      · exact Or.inr ⟨0, by simp, by rw [Nat.xor_zero]; exact e⟩

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
    (hs : ∀ e, n - 1 + e < lb →
      sE (2 ^ (2 ^ n) - 1) (tt n f) (n - 1 + e) e (vars n) (vars n) = false) (t : ℕ)
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
         V (n + j) = (2 ^ N - 1) ^^^ (if i < n + j then V i else 0))) ∨ (R j = [] ∧ (V (n + j) = 0 ∨ V (n + j) = 2 ^ N - 1)) := by
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
    · right; right
      refine ⟨rfl, ?_⟩
      rw [hin] at hv
      have h0 : (0 : ℕ) < 2 ^ N := Nat.two_pow_pos N
      rcases hopC _ (List.getElem_mem hj) with h | h | h <;> rw [h] at hv
      · right
        refine eqN (Vlt _) (by omega) fun p hp => ?_
        rw [hv p hp, full_bit N p hp]; simp [GateOp.eval]
      · left
        refine eqN (Vlt _) h0 fun p hp => ?_
        rw [hv p hp, Nat.zero_testBit]; simp [GateOp.eval]
      · right
        refine eqN (Vlt _) (by omega) fun p hp => ?_
        rw [hv p hp, full_bit N p hp]; simp [GateOp.eval]
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
      intro h0
      have := congrArg List.length h0
      simp at this
      exact hn0 this) (by
      intro i hi
      have hi' := List.mem_range.1 hi
      refine ⟨by omega, ?_⟩
      rcases Hi i hi' with h | ⟨j, h2, h3⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, by omega, h2, by simp only [R, dif_pos h2]; exact h3⟩)
  obtain ⟨q1, q2⟩ := hS
  rw [List.length_range] at q1 q2
  rw [hvars] at q2
  have hmlb : m < lb := by omega
  obtain ⟨e, he⟩ : ∃ e, m = n - 1 + e := ⟨m - (n - 1), by omega⟩
  have h1 := (q2 e (by omega)).1
  have h2 := hs e (by omega)
  have hw : Wl n V 0 = vars n := hvars
  rw [hw, he, h2] at h1
  cases h1

end PEqualNP.Outside.L_meta_5483

open PEqualNP.Outside.L_meta_5483 in
theorem PEqualNP.Outside.L_meta_5483 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5)) t → 7 ≤ t := by
  intro t h
  refine final 6 7 _ (by decide) (by decide) (fun e he => ?_) t h
  have he' : e < 2 := by omega
  clear he
  interval_cases e <;> decide +kernel
