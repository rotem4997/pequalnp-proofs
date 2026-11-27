import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7362

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





theorem aux : True := trivial

end PEqualNP.Outside.L_meta_7362

theorem PEqualNP.Outside.L_meta_7362 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : Fin x1 → ℕ := fun (x6 : Fin x1) => (List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.inputs.contains ↑x6) x5.gates).length;   PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 → (∀ x9 ∈ x5.gates, x9.inputs.length + (x9.op.eval [Bool.false]).toNat ≤ (2 : ℕ)) → (∀ x10 ∉ x4, (2 : ℕ) ≤ x6 x10) → x4.card + (3 : ℕ) * x4ᶜ.card + List.countP (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval [Bool.false]) x5.gates ≤ x5.size + (1 : ℕ) + {x11 ∉ x4 | x6 x11 = (2 : ℕ)}.card := by
  intro n G _ O C x hmin hfun har h2
  classical
  have hmin' := hmin
  obtain ⟨hD, hmn⟩ := hmin
  have hopD : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
    intro g hg
    simpa using (hD g hg).1
  have tk : ∀ g ∈ C.gates, g.inputs = PEqualNP.Outside.L_meta_7362.rds g := by
    intro g hg
    have hl := har g hg
    rcases hopD g hg with h | h | h
    · simp [PEqualNP.Outside.L_meta_7362.rds, h]
    · simp [PEqualNP.Outside.L_meta_7362.rds, h]
    · simp only [PEqualNP.Outside.L_meta_7362.rds, h]
      rw [h] at hl
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval] at hl
      exact (List.take_of_length_le (by omega)).symm
  let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map PEqualNP.Outside.L_meta_7362.nrm, C.output⟩
  have hf : PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.circuitFun n C := by
    funext y
    change (PEqualNP.Outside.L_meta_7362.run (C.gates.map PEqualNP.Outside.L_meta_7362.nrm) (List.ofFn y)).getD C.output false = (PEqualNP.Outside.L_meta_7362.run C.gates (List.ofFn y)).getD C.output false
    rw [PEqualNP.Outside.L_meta_7362.nrm_run C.gates hopD]
  have hrl : ∀ g ∈ C.gates, (PEqualNP.Outside.L_meta_7362.rds g).length ≤ 2 := by
    intro g hg
    have := (hD g hg).2
    rcases hopD g hg with h | h | h <;> simp [PEqualNP.Outside.L_meta_7362.rds, h] <;> omega
  have hFC : PEqualNP.MetaComplexity.FanInTwo C' := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact ⟨(hD g' hg').1, hrl g' hg'⟩
  have hlen : C'.gates.length = C.gates.length := by simp [C']
  let I : Fin C.gates.length → Finset ℕ := fun j => (PEqualNP.Outside.L_meta_7362.rds C.gates[j]).toFinset
  have hI : ∀ j, (I j).card ≤ 2 := fun j => (List.toFinset_card_le _).trans (hrl _ (List.getElem_mem j.isLt))
  -- every gate but the output is read
  have Hu : ∀ k < C.gates.length, n + k ≠ C.output → ∃ j, n + k ∈ I j := by
    intro k hk hko
    by_contra hcon
    push Not at hcon
    obtain ⟨E, hE1, hE2, hE3⟩ := PEqualNP.Outside.L_meta_7362.del n C' hFC k (by omega) (fun j hj hkj hin => by
      have hj' : j < C.gates.length := by omega
      refine hcon ⟨j, hj'⟩ ?_
      simpa [I, C', PEqualNP.Outside.L_meta_7362.nrm] using hin) (fun h => hko h.symm)
    have h1 := hmn E hE1 (hE3.trans hf)
    have h2 : C'.size = C.size := by simp [PEqualNP.CircuitLowerBounds.Circuit.size, C']
    have h3 : C.size = C.gates.length := rfl
    omega
  have hI2 : ∀ j : Fin C.gates.length, (I j).card + (C.gates[j].op.eval [false]).toNat ≤ 2 := by
    intro j
    have h1 := har C.gates[j] (List.getElem_mem j.isLt)
    have h9 : (I j).card ≤ (PEqualNP.Outside.L_meta_7362.rds C.gates[j]).length := List.toFinset_card_le _
    have h8 := congrArg List.length (tk C.gates[j] (List.getElem_mem j.isLt))
    omega
  have hx : ∀ v, x v = ∑ j : Fin C.gates.length, if (v : ℕ) ∈ I j then 1 else 0 := by
    intro v
    simp only [x]
    rw [← List.countP_eq_length_filter, PEqualNP.Outside.L_meta_7362.cntp, Finset.card_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := tk (C.gates.get j) (List.getElem_mem j.isLt)
    rw [this]
    simp [I]
  have gf : ∀ y : Fin n → Bool, PEqualNP.MetaComplexity.NestedCover.graphFun G O y = true ↔ (∃ p ∈ O, y p = true) ∨ ∃ p q, G.Adj p q ∧ y p = true ∧ y q = true := by
    intro y; simp [PEqualNP.MetaComplexity.NestedCover.graphFun]
  -- an input of `O` is read or is the output
  have Hi : ∀ v ∈ O, (v : ℕ) ≠ C.output → 1 ≤ x v := by
    intro v hv hvo
    by_contra hcon
    have h0 : x v = 0 := by omega
    rw [hx v] at h0
    have hno : ∀ g ∈ C.gates, (v : ℕ) ∉ PEqualNP.Outside.L_meta_7362.rds g := by
      intro g hg hin
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      have := Finset.sum_eq_zero_iff.1 h0 ⟨j, hj⟩ (Finset.mem_univ _)
      have hmem : (v : ℕ) ∈ I ⟨j, hj⟩ := by simpa [I] using hin
      rw [if_pos hmem] at this
      omega
    let y : Fin n → Bool := fun _ => false
    have e := PEqualNP.Outside.L_meta_7362.indep (v : ℕ) C.gates hopD hno (List.ofFn y) (List.ofFn (Function.update y v true)) (by simp) (by
      intro q hq
      by_cases hqn : q < n
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hqn, dif_pos, Option.getD_some]
        rw [Function.update_of_ne]
        intro h
        exact hq (by simpa using congrArg Fin.val h)
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]) C.output (fun h => hvo h.symm)
    have f0 : PEqualNP.MetaComplexity.circuitFun n C y = false := by
      rw [hfun, ← Bool.not_eq_true, gf]
      simp [y]
    have f1 : PEqualNP.MetaComplexity.circuitFun n C (Function.update y v true) = true := by
      rw [hfun, gf]
      exact Or.inl ⟨v, hv, by simp⟩
    change (PEqualNP.Outside.L_meta_7362.run C.gates (List.ofFn y)).getD C.output false = false at f0
    change (PEqualNP.Outside.L_meta_7362.run C.gates (List.ofFn (Function.update y v true))).getD C.output false = true at f1
    rw [e, f1] at f0
    cases f0
  let K := (Finset.range C.gates.length).filter fun k => n + k ≠ C.output
  have hK2 : K.card ≤ ∑ k ∈ Finset.range C.gates.length, ∑ j : Fin C.gates.length, if n + k ∈ I j then 1 else 0 := by
    rw [Finset.card_eq_sum_ones]
    refine (Finset.sum_le_sum fun k hk => ?_).trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
    obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
    obtain ⟨j, hj⟩ := Hu k (Finset.mem_range.1 hk1) hk2
    have := Finset.single_le_sum (f := fun j => if n + k ∈ I j then 1 else 0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simp only [if_pos hj] at this
    exact this
  have tot : (∑ v, x v) + (∑ k ∈ Finset.range C.gates.length, ∑ j : Fin C.gates.length, (if n + k ∈ I j then 1 else 0)) + ∑ j : Fin C.gates.length, (C.gates[j].op.eval [false]).toNat ≤ 2 * C.gates.length := by
    rw [Finset.sum_congr rfl fun v _ => hx v, Finset.sum_comm, Finset.sum_comm (s := Finset.range C.gates.length), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine (Finset.sum_le_card_nsmul _ _ 2 fun j _ => ?_).trans (by simp [mul_comm])
    rw [← Finset.card_filter, ← Finset.card_filter]
    have a1 : (Finset.univ.filter fun v : Fin n => (v : ℕ) ∈ I j).card = ((Finset.univ.filter fun v : Fin n => (v : ℕ) ∈ I j).image Fin.val).card :=
      (Finset.card_image_of_injective _ Fin.val_injective).symm
    have a2 : ((Finset.range C.gates.length).filter fun k => n + k ∈ I j).card = (((Finset.range C.gates.length).filter fun k => n + k ∈ I j).image fun k => n + k).card :=
      (Finset.card_image_of_injective _ fun a b h => by simpa using h).symm
    have a3 : ((Finset.univ.filter fun v : Fin n => (v : ℕ) ∈ I j).image Fin.val).card + (((Finset.range C.gates.length).filter fun k => n + k ∈ I j).image fun k => n + k).card ≤ (I j).card := by
      rw [← Finset.card_union_of_disjoint]
      · refine Finset.card_le_card fun w hw => ?_
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hw
        rcases hw with ⟨v, ⟨_, h⟩, rfl⟩ | ⟨k, ⟨_, h⟩, rfl⟩ <;> exact h
      · refine Finset.disjoint_left.2 fun w h1 h2 => ?_
        simp only [Finset.mem_image, Finset.mem_filter] at h1 h2
        obtain ⟨v, _, rfl⟩ := h1
        obtain ⟨k, _, h⟩ := h2
        have := v.isLt
        omega
    have a4 := hI2 j
    omega
  have hnot : ∑ j : Fin C.gates.length, (C.gates[j].op.eval [false]).toNat = List.countP (fun g => g.op.eval [false]) C.gates := by
    rw [PEqualNP.Outside.L_meta_7362.cntp, Finset.card_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [List.get_eq_getElem, Fin.getElem_fin]
    cases (C.gates[(j : ℕ)].op.eval [false]) <;> rfl
  have split : ∑ v, x v = ∑ v ∈ O, x v + ∑ v ∈ Oᶜ, x v := (Finset.sum_add_sum_compl O x).symm
  have hc3 : 3 * Oᶜ.card ≤ ∑ v ∈ Oᶜ, x v + (Oᶜ.filter fun v => x v = 2).card := by
    have e1 : (Oᶜ.filter fun v => x v = 2).card = ∑ v ∈ Oᶜ, if x v = 2 then 1 else 0 := by
      rw [← Finset.card_filter]
    rw [e1, ← Finset.sum_add_distrib, mul_comm, ← smul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ 3 fun v hv => ?_
    have := h2 v (by simpa using hv)
    split_ifs <;> omega
  have hO : O.card + C.gates.length ≤ ∑ v ∈ O, x v + K.card + 1 := by
    by_cases hout : C.output < n
    · have k1 : K = Finset.range C.gates.length := by
        refine Finset.filter_true_of_mem fun k _ => ?_
        omega
      have k2 : (O.erase ⟨C.output, hout⟩).card ≤ ∑ v ∈ O, x v := by
        rw [Finset.card_eq_sum_ones]
        refine (Finset.sum_le_sum fun v hv => ?_).trans (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _))
        rw [Finset.mem_erase] at hv
        exact Hi v hv.2 fun h => hv.1 (Fin.ext h)
      have k3 := Finset.pred_card_le_card_erase (s := O) (a := (⟨C.output, hout⟩ : Fin n))
      rw [k1, Finset.card_range]
      omega
    · have k2 : O.card ≤ ∑ v ∈ O, x v := by
        rw [Finset.card_eq_sum_ones]
        refine Finset.sum_le_sum fun v hv => Hi v hv fun h => ?_
        have := v.isLt
        omega
      have h1 : (Finset.range C.gates.length).erase (C.output - n) ⊆ K := by
        intro k hk
        rw [Finset.mem_erase] at hk
        exact Finset.mem_filter.2 ⟨hk.2, fun h => hk.1 (by omega)⟩
      have h2 := Finset.card_le_card h1
      have h3 := Finset.pred_card_le_card_erase (s := Finset.range C.gates.length) (a := C.output - n)
      simp at h3
      omega
  have h3 : C.size = C.gates.length := rfl
  rw [hnot] at tot
  omega
