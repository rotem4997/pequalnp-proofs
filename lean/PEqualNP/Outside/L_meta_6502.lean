import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6502

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


theorem cnt (n m o : ℕ) (R : ℕ → List ℕ) (hR : ∀ k, (R k).length ≤ 2)
    (Hu : ∀ k < m, n + k = o ∨ ∃ j, k + 1 ≤ j ∧ j < m ∧ n + k ∈ R j) :
    ∀ r k (U : List ℕ), k + r = m → U.Nodup →
      (∀ i ∈ U, i < n + k ∧ (i = o ∨ ∃ j, k ≤ j ∧ j < m ∧ i ∈ R j)) → U.length ≤ r + 1 := by
  classical
  intro r
  induction r with
  | zero =>
    intro k U hk hnd hU
    have all : ∀ i ∈ U, i = o := by
      intro i hi
      rcases (hU i hi).2 with h | ⟨j, h1, h2, _⟩
      · exact h
      · omega
    rcases U with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp
    · simp
    · exfalso
      have e1 := all a (by simp)
      have e2 := all b (by simp)
      rw [e1, e2] at hnd
      simp at hnd
  | succ r ih =>
    intro k U hk hnd hU
    have hkm : k < m := by omega
    have h1 : (U.filter (· ∈ R k)).length ≤ 2 := by
      have hs : (U.filter (· ∈ R k)).Subperm (R k) :=
        List.subperm_of_subset (hnd.filter _) fun x hx => by simpa using (List.mem_filter.1 hx).2
      exact hs.length_le.trans (hR k)
    have h2 := List.length_eq_length_filter_add (l := U) (fun x => decide (x ∈ R k))
    have h3 := ih (k + 1) ((n + k) :: U.filter (fun x => !decide (x ∈ R k))) (by omega) (by
      rw [List.nodup_cons]
      refine ⟨fun h => ?_, hnd.filter _⟩
      have := (hU _ (List.mem_of_mem_filter h)).1
      omega) (by
      intro i hi
      rcases List.mem_cons.1 hi with rfl | hi
      · exact ⟨by omega, Hu k hkm⟩
      · obtain ⟨h4, h5⟩ := List.mem_filter.1 hi
        obtain ⟨h6, h7⟩ := hU i h4
        refine ⟨by omega, ?_⟩
        rcases h7 with h7 | ⟨j, h7, h8, h9⟩
        · exact Or.inl h7
        · right
          refine ⟨j, ?_, h8, h9⟩
          rcases Nat.lt_or_ge k j with h | h
          · omega
          · have : j = k := by omega
            rw [this] at h9
            simp [h9] at h5)
    rw [List.length_cons] at h3
    omega

theorem cntp {α : Type} (p : α → Bool) : ∀ l : List α, l.countP p = (Finset.univ.filter fun i : Fin l.length => p (l.get i) = true).card
  | [] => by simp
  | a :: l => by
    have ih := cntp p l
    have e : (Finset.univ.filter fun i : Fin (a :: l).length => p ((a :: l).get i) = true).card =
        (if p a = true then 1 else 0) + (Finset.univ.filter fun i : Fin l.length => p (l.get i) = true).card := by
      have := Fin.card_filter_univ_succ (n := l.length) (fun i : Fin (l.length + 1) => p ((a :: l).get i) = true)
      rw [show (Finset.univ.filter fun i : Fin (a :: l).length => p ((a :: l).get i) = true).card = (Finset.univ.filter fun i : Fin (l.length + 1) => p ((a :: l).get i) = true).card from rfl, this]
      by_cases h : p a = true
      · simp [h, Function.comp_def, add_comm]
      · simp [h, Function.comp_def]
    rw [e, ← ih, List.countP_cons, add_comm]





theorem fcount (eff : Gate → List ℕ) (v : ℕ) : ∀ gs : List Gate, (gs.filter fun g => (eff g).contains v).length ≤ (gs.flatMap eff).count v
  | [] => by simp
  | g :: gs => by
    have ih := fcount eff v gs
    rw [List.flatMap_cons, List.count_append, List.filter_cons]
    split_ifs with h
    · have : 0 < (eff g).count v := List.count_pos_iff.2 (by simpa using h)
      simp only [List.length_cons]
      omega
    · omega

theorem flen (eff : Gate → List ℕ) : ∀ gs : List Gate, (∀ g ∈ gs, (eff g).length ≤ bif g.op.eval [false] then 1 else 2) →
    (gs.flatMap eff).length + (gs.filter fun g => g.op.eval [false]).length ≤ 2 * gs.length
  | [], _ => by simp
  | g :: gs, h => by
    have ih := flen eff gs fun g' h' => h g' (List.mem_cons_of_mem _ h')
    have h1 := h g List.mem_cons_self
    rw [List.flatMap_cons, List.length_append, List.filter_cons, List.length_cons]
    cases hb : g.op.eval [false] with
    | true =>
      rw [hb] at h1
      simp only [if_true, List.length_cons, cond_true] at h1 ⊢
      omega
    | false =>
      rw [hb] at h1
      simp only [cond_false] at h1
      rw [if_neg (by simp)]
      omega

theorem csum (l : List ℕ) (S : Finset ℕ) : ∑ w ∈ S, l.count w ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.count_cons, Finset.sum_add_distrib, List.length_cons]
    have : ∑ w ∈ S, (if (a == w) = true then 1 else 0) ≤ 1 := by
      simp only [beq_iff_eq, Finset.sum_ite_eq]
      split_ifs <;> omega
    omega

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6502

theorem PEqualNP.Outside.L_meta_6502 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.IsMinimalCircuit x1 x2 →     (∀ (x4 : Fin x1), ∃ (x5 : Fin x1 → Bool) (x6 : Fin x1 → Bool), (∀ (x7 : Fin x1), x7 ≠ x4 → x5 x7 = x6 x7) ∧ PEqualNP.MetaComplexity.circuitFun x1 x2 x5 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x6) →       have x5 : PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => List.take (bif x5.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x5.inputs;       have x6 : List ℕ := x2.output :: List.flatMap x5 x2.gates;       have x7 : Fin x1 → ℕ := fun (x7 : Fin x1) => (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (x5 x8).contains ↑x7) x2.gates).length;       ∑ x8 : Fin x1, Max.max (1 : ℕ) (x7 x8) + ∑ x8 ∈ Finset.range x2.size, (List.count (x1 + x8) x6 - (1 : ℕ)) + (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.op.eval [Bool.false]) x2.gates).length ≤ x2.size + (1 : ℕ) := by
  intro n C hmin hess eff L x
  classical
  obtain ⟨hD, hmn⟩ := hmin
  have hopD : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
    intro g hg
    simpa using (hD g hg).1
  have tk : ∀ g ∈ C.gates, List.take (bif g.op.eval [false] then 1 else 2) g.inputs = PEqualNP.Outside.L_meta_6502.rds g := by
    intro g hg
    have hl := (hD g hg).2
    rcases hopD g hg with h | h | h
    · simp [PEqualNP.Outside.L_meta_6502.rds, h, PEqualNP.CircuitLowerBounds.GateOp.eval, List.take_of_length_le hl]
    · simp [PEqualNP.Outside.L_meta_6502.rds, h, PEqualNP.CircuitLowerBounds.GateOp.eval, List.take_of_length_le hl]
    · simp [PEqualNP.Outside.L_meta_6502.rds, h, PEqualNP.CircuitLowerBounds.GateOp.eval]
  let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map PEqualNP.Outside.L_meta_6502.nrm, C.output⟩
  have hf : PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.circuitFun n C := by
    funext y
    change (PEqualNP.Outside.L_meta_6502.run (C.gates.map PEqualNP.Outside.L_meta_6502.nrm) (List.ofFn y)).getD C.output false = (PEqualNP.Outside.L_meta_6502.run C.gates (List.ofFn y)).getD C.output false
    rw [PEqualNP.Outside.L_meta_6502.nrm_run C.gates hopD]
  have hrl : ∀ g ∈ C.gates, (PEqualNP.Outside.L_meta_6502.rds g).length ≤ 2 := by
    intro g hg
    have := (hD g hg).2
    rcases hopD g hg with h | h | h <;> simp [PEqualNP.Outside.L_meta_6502.rds, h] <;> omega
  have hFC : PEqualNP.MetaComplexity.FanInTwo C' := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact ⟨(hD g' hg').1, hrl g' hg'⟩
  have hlen : C'.gates.length = C.gates.length := by simp [C']
  have he : ∀ g ∈ C.gates, eff g = PEqualNP.Outside.L_meta_6502.rds g := tk
  -- every gate occurs in the list
  have Hu : ∀ k < C.gates.length, 1 ≤ L.count (n + k) := by
    intro k hk
    rw [Nat.succ_le_iff, List.count_pos_iff]
    by_contra hcon
    simp only [L, List.mem_cons, List.mem_flatMap, not_or, not_exists, not_and] at hcon
    obtain ⟨E, hE1, hE2, hE3⟩ := PEqualNP.Outside.L_meta_6502.del n C' hFC k (by omega) (fun j hj hkj hin => by
      have hj' : j < C.gates.length := by omega
      refine hcon.2 C.gates[j] (List.getElem_mem hj') ?_
      rw [he _ (List.getElem_mem hj')]
      simpa [C', PEqualNP.Outside.L_meta_6502.nrm] using hin) (fun h => hcon.1 h.symm)
    have h1 := hmn E hE1 (hE3.trans hf)
    have h2 : C'.size = C.size := by simp [PEqualNP.CircuitLowerBounds.Circuit.size, C']
    have h3 : C.size = C.gates.length := rfl
    omega
  -- every input occurs in the list
  have Hi : ∀ v : Fin n, 1 ≤ L.count (v : ℕ) := by
    intro v
    rw [Nat.succ_le_iff, List.count_pos_iff]
    by_contra hcon
    simp only [L, List.mem_cons, List.mem_flatMap, not_or, not_exists, not_and] at hcon
    obtain ⟨y, z, hyz, hne'⟩ := hess v
    refine hne' ?_
    refine PEqualNP.Outside.L_meta_6502.indep (v : ℕ) C.gates hopD (fun g hg hin => hcon.2 g hg (by rw [he g hg]; exact hin)) (List.ofFn y) (List.ofFn z) (by simp) ?_ C.output (fun h => hcon.1 h.symm)
    intro q hq
    by_cases hqn : q < n
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hqn, dif_pos, Option.getD_some]
      exact hyz ⟨q, hqn⟩ (fun h => hq (congrArg Fin.val h))
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have hx : ∀ v : Fin n, x v ≤ L.count (v : ℕ) := by
    intro v
    have h1 := PEqualNP.Outside.L_meta_6502.fcount eff (v : ℕ) C.gates
    have h2 : (List.flatMap eff C.gates).count (v : ℕ) ≤ L.count (v : ℕ) := List.count_le_count_cons
    exact h1.trans h2
  have hlen2 : L.length + (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => g.op.eval [false]) C.gates).length ≤ 1 + 2 * C.gates.length := by
    have := PEqualNP.Outside.L_meta_6502.flen eff C.gates (fun g hg => by
      simp only [eff, List.length_take]
      cases g.op.eval [false] <;> simp)
    simp only [L, List.length_cons]
    omega
  have tot := PEqualNP.Outside.L_meta_6502.csum L ((Finset.univ.image fun v : Fin n => (v : ℕ)) ∪ ((Finset.range C.gates.length).image fun k => n + k))
  rw [Finset.sum_union (by
    refine Finset.disjoint_left.2 fun w h1 h2 => ?_
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at h1 h2
    obtain ⟨v, rfl⟩ := h1
    obtain ⟨k, _, h⟩ := h2
    have := v.isLt
    omega), Finset.sum_image (fun a _ b _ h => Fin.ext h), Finset.sum_image (fun a _ b _ h => by simpa using h)] at tot
  have b1 : ∑ v : Fin n, max 1 (x v) ≤ ∑ v : Fin n, L.count (v : ℕ) := Finset.sum_le_sum fun v _ => max_le (Hi v) (hx v)
  have b2 : ∑ k ∈ Finset.range C.gates.length, (L.count (n + k) - 1) + C.gates.length ≤ ∑ k ∈ Finset.range C.gates.length, L.count (n + k) := by
    have e : C.gates.length = ∑ k ∈ Finset.range C.gates.length, 1 := by simp
    conv_lhs => rw [show ∑ k ∈ Finset.range C.gates.length, (L.count (n + k) - 1) + C.gates.length = ∑ k ∈ Finset.range C.gates.length, (L.count (n + k) - 1) + ∑ k ∈ Finset.range C.gates.length, 1 by simp]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k hk => ?_
    have := Hu k (Finset.mem_range.1 hk)
    omega
  have h3 : C.size = C.gates.length := rfl
  rw [h3]
  omega
