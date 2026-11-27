import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8043.A

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (w : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires w

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) :=
  rfl

theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run, Circuit.wires]
  | cons g gs ih =>
    rw [run_cons, ih]
    simp; omega

def sw : GateOp → GateOp
  | GateOp.and => GateOp.or
  | GateOp.or => GateOp.and
  | o => o

def rr (m w : ℕ) : ℕ := if w < m then w + 1 else 0

def dl : ℕ → List Gate → List Gate
  | _, [] => []
  | m, g :: gs => ⟨sw g.op, g.inputs.map (rr m)⟩ :: dl (m + 1) gs

theorem dl_length (m : ℕ) (gs : List Gate) : (dl m gs).length = gs.length := by
  induction gs generalizing m with
  | nil => rfl
  | cons g gs ih => simp [dl, ih]

theorem dl_get (gs : List Gate) (m i : ℕ) (h1 : i < (dl m gs).length) (h2 : i < gs.length) :
    ((dl m gs).get ⟨i, h1⟩).op = sw (gs.get ⟨i, h2⟩).op := by
  induction gs generalizing m i with
  | nil => simp at h2
  | cons g gs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih (m + 1) i _ (by simpa using h2)

theorem sw_and (o : GateOp) : sw o = GateOp.and ↔ o = GateOp.or := by
  cases o <;> simp [sw]

theorem dl_mono (m : ℕ) (gs : List Gate)
    (h : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ dl m gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing m with
  | nil => simp [dl]
  | cons g gs ih =>
    intro g' hg'
    simp only [dl, List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · obtain ⟨h1, h2⟩ := h g (by simp)
      refine ⟨?_, by simpa using h2⟩
      simp at h1
      rcases h1 with h1 | h1 <;> simp [h1, sw]
    · exact ih (m + 1) (fun g hg => h g (by simp [hg])) g' hg'

def Inv (m : ℕ) (W W' : List Bool) : Prop :=
  W.length = m ∧ W'.length = m + 1 ∧ ∀ w, W'.getD (rr m w) false = !W.getD w false

theorem demorgan (o : GateOp) (ho : o = GateOp.and ∨ o = GateOp.or) (l : List Bool) :
    (sw o).eval (l.map not) = !o.eval l := by
  rcases ho with rfl | rfl <;> simp only [sw, GateOp.eval, List.any_map, List.all_map] <;>
    induction l <;> simp_all

theorem inv_step (m : ℕ) (W W' : List Bool) (hI : Inv m W W') (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) :
    Inv (m + 1) (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)])
      (W' ++ [(sw g.op).eval ((g.inputs.map (rr m)).map fun i => W'.getD i false)]) := by
  obtain ⟨h1, h2, h3⟩ := hI
  have hv : (sw g.op).eval ((g.inputs.map (rr m)).map fun i => W'.getD i false)
      = !g.op.eval (g.inputs.map fun i => W.getD i false) := by
    rw [← demorgan g.op hg, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact h3 i
  refine ⟨by simp [h1], by simp [h2], ?_⟩
  intro w
  rw [hv]
  unfold rr
  rcases lt_trichotomy w m with hw | rfl | hw
  · have := h3 w
    unfold rr at this
    rw [if_pos hw] at this
    rw [if_pos (by omega), List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega),
      this]
  · rw [if_pos (by omega), List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega)]
    simp [h1, h2]
  · have := h3 m
    unfold rr at this
    rw [if_neg (lt_irrefl m), List.getD_eq_default W false (by omega)] at this
    rw [if_neg (by omega), List.getD_append W' _ false 0 (by omega), this,
      List.getD_eq_default (W ++ _) false (by simp; omega)]

theorem inv_run (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (m : ℕ) (W W' : List Bool) (hI : Inv m W W') :
    Inv (m + gs.length) (run gs W) (run (dl m gs) W') := by
  induction gs generalizing m W W' with
  | nil => simpa [run, Circuit.wires, dl] using hI
  | cons g gs ih =>
    rw [run_cons]
    simp only [dl]
    rw [run_cons]
    have := ih (fun g hg' => hg g (by simp [hg'])) (m + 1) _ _
      (inv_step m W W' hI g (hg g (by simp)))
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem inv_init (W : List Bool) : Inv W.length W (true :: W.map not) := by
  refine ⟨rfl, by simp, ?_⟩
  intro w
  unfold rr
  split_ifs with hw
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show W.length ≤ w by omega)]

theorem t4680 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 ∧ Nat.card { x4 : Fin x3.gates.length // (x3.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and } ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x3 fun (x5 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.cases Bool.true (fun (x6 : Fin (26 : ℕ)) => !x4 x6) x5) = !PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 x4 := by
  intro x1 hm
  have hg : ∀ g ∈ x1.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g h => by
    simpa using (hm g h).1
  refine ⟨⟨dl 26 x1.gates, rr (26 + x1.gates.length) x1.output⟩, dl_mono 26 _ hm, ?_, ?_⟩
  · apply le_of_eq
    rw [← Nat.card_coe_set_eq]
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (finCongr (dl_length 26 x1.gates)) (fun i => by
      show _ ↔ (x1.gates.get _).op = GateOp.or
      rw [← sw_and]
      exact Iff.of_eq (congrArg (· = GateOp.and) (dl_get x1.gates 26 i.1 i.2 _)))
  · intro x4
    have hW : List.ofFn (fun x5 : Fin (26 + 1) => Fin.cases true (fun x6 : Fin 26 => !x4 x6) x5)
        = true :: (List.ofFn x4).map not := by
      rw [List.ofFn_succ]
      simp
    have h0 : Inv 26 (List.ofFn x4) (true :: (List.ofFn x4).map not) := by
      have := inv_init (List.ofFn x4)
      rwa [List.length_ofFn] at this
    obtain ⟨-, -, h3⟩ := inv_run x1.gates hg 26 _ _ h0
    have := h3 x1.output
    unfold circuitFun Circuit.eval
    rw [hW]
    exact this

end PEqualNP.Outside.L_meta_8043.A

namespace PEqualNP.Outside.L_meta_8043.B

open PEqualNP.CircuitLowerBounds

abbrev Rec (n : ℕ) := Finset (Fin n) × Finset ℕ × Finset (Fin n) × Finset ℕ
abbrev Form (n : ℕ) := Option (Finset (Fin n) × Finset ℕ)

def zeroF {n : ℕ} : Form n := some (∅, ∅)

def orF {n : ℕ} : List (Form n) → Form n
  | [] => some (∅, ∅)
  | f :: fs =>
    match f, orF fs with
    | none, _ => none
    | some _, none => none
    | some (a, b), some (c, d) => some (a ∪ c, b ∪ d)

structure St (n : ℕ) where
  fs : List (Form n)
  rs : List (Rec n)

def getF {n : ℕ} (s : St n) (i : ℕ) : Form n := s.fs.getD i zeroF

def andStep {n : ℕ} (s : St n) (fa fb : Form n) : St n :=
  match fa, fb with
  | none, f => ⟨s.fs ++ [f], s.rs⟩
  | some p, none => ⟨s.fs ++ [some p], s.rs⟩
  | some (va, ga), some (vb, gb) => ⟨s.fs ++ [some (∅, {s.rs.length})], s.rs ++ [(va, ga, vb, gb)]⟩

def step {n : ℕ} (s : St n) (g : Gate) : St n :=
  match g.op, g.inputs with
  | GateOp.or, ins => ⟨s.fs ++ [orF (ins.map (getF s))], s.rs⟩
  | GateOp.and, [] => ⟨s.fs ++ [none], s.rs⟩
  | GateOp.and, [a] => ⟨s.fs ++ [getF s a], s.rs⟩
  | GateOp.and, a :: b :: _ => andStep s (getF s a) (getF s b)
  | _, _ => ⟨s.fs ++ [zeroF], s.rs⟩

def sv {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) (V : Finset (Fin n)) (G : Finset ℕ) : Bool :=
  decide (∃ v ∈ V, v ∈ U) || decide (∃ j ∈ G, vs.getD j false = true)

def rvStep {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) (r : Rec n) : List Bool :=
  vs ++ [sv U vs r.1 r.2.1 && sv U vs r.2.2.1 r.2.2.2]

def rvals {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) : List Bool := rs.foldl (rvStep U) []

def fv {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) : Form n → Bool
  | none => true
  | some p => sv U vs p.1 p.2

theorem fv_orF {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) (fs : List (Form n)) :
    fv U vs (orF fs) = fs.any (fv U vs) := by
  induction fs with
  | nil => simp [orF, fv, sv]
  | cons f fs ih =>
    rcases f with _ | ⟨a, b⟩
    · simp [orF, fv]
    · rcases h : orF fs with _ | ⟨c, d⟩
      · rw [h] at ih
        simp only [orF, h, List.any_cons]
        rw [← ih]
        simp [fv]
      · rw [h] at ih
        simp only [orF, h, List.any_cons]
        rw [← ih]
        simp only [fv, sv, Finset.mem_union, or_and_right, exists_or, Bool.decide_or]
        ac_rfl

theorem rv_pre {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) :
    ∀ (vs : List Bool) (j : ℕ), j < vs.length → (rs.foldl (rvStep U) vs).getD j false = vs.getD j false := by
  induction rs with
  | nil => intro vs j _; rfl
  | cons r rs ih =>
    intro vs j hj
    simp only [List.foldl_cons]
    rw [ih _ j (by simp [rvStep]; omega)]
    simp [rvStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem rv_len {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) :
    ∀ vs : List Bool, (rs.foldl (rvStep U) vs).length = vs.length + rs.length := by
  induction rs with
  | nil => intro vs; simp
  | cons r rs ih => intro vs; simp only [List.foldl_cons, ih]; simp [rvStep]; omega

theorem rvals_len {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) : (rvals U rs).length = rs.length := by
  simp [rvals, rv_len]

theorem rvals_snoc {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (r : Rec n) :
    rvals U (rs ++ [r]) = rvStep U (rvals U rs) r := by
  simp [rvals, List.foldl_append]

theorem sv_congr {n : ℕ} (U : Finset (Fin n)) (vs vs' : List Bool) (V : Finset (Fin n)) (G : Finset ℕ)
    (h : ∀ j ∈ G, vs.getD j false = vs'.getD j false) : sv U vs V G = sv U vs' V G := by
  unfold sv
  congr 2
  apply propext
  constructor
  · rintro ⟨j, hj, hv⟩; exact ⟨j, hj, (h j hj) ▸ hv⟩
  · rintro ⟨j, hj, hv⟩; exact ⟨j, hj, (h j hj).symm ▸ hv⟩

def RefsLt {n : ℕ} (m : ℕ) (f : Form n) : Prop := ∀ p, f = some p → ∀ j ∈ p.2, j < m

def GoodRecs {n : ℕ} (rs : List (Rec n)) : Prop :=
  ∀ k (hk : k < rs.length), (∀ j ∈ rs[k].2.1, j < k) ∧ (∀ j ∈ rs[k].2.2.2, j < k)

theorem fv_snoc {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (r : Rec n) (f : Form n)
    (hf : RefsLt rs.length f) : fv U (rvals U (rs ++ [r])) f = fv U (rvals U rs) f := by
  rcases f with _ | p
  · rfl
  · simp only [fv]
    apply sv_congr
    intro j hj
    have hjl := hf p rfl j hj
    rw [rvals_snoc]
    simp [rvStep, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [rvals_len U]; exact hjl)]

theorem refs_orF {n : ℕ} (m : ℕ) (fs : List (Form n)) (h : ∀ f ∈ fs, RefsLt m f) : RefsLt m (orF fs) := by
  induction fs with
  | nil => intro p hp j hj; simp [orF] at hp; subst hp; simp at hj
  | cons f fs ih =>
    have ih' := ih (fun f' hf' => h f' (by simp [hf']))
    have hf := h f (by simp)
    intro p hp j hj
    rcases f with _ | ⟨a, b⟩
    · simp [orF] at hp
    · rcases hq : orF fs with _ | ⟨c, d⟩
      · simp [orF, hq] at hp
      · simp only [orF, hq, Option.some.injEq] at hp
        subst hp
        rcases Finset.mem_union.1 hj with hj | hj
        · exact hf _ rfl j hj
        · exact ih' _ hq j hj

theorem refs_getF {n : ℕ} (m : ℕ) (s : St n) (h : ∀ f ∈ s.fs, RefsLt m f) (i : ℕ) : RefsLt m (getF s i) := by
  unfold getF
  by_cases hi : i < s.fs.length
  · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    intro p hp j hj
    simp [zeroF] at hp; subst hp; simp at hj

def Fw (W : List Bool) (g : Gate) : List Bool := W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]

def Inv {n : ℕ} (U : Finset (Fin n)) (W : List Bool) (s : St n) : Prop :=
  s.fs.length = W.length ∧ (∀ f ∈ s.fs, RefsLt s.rs.length f) ∧ GoodRecs s.rs ∧
    ∀ i, W.getD i false = fv U (rvals U s.rs) (getF s i)

theorem getF_push {n : ℕ} (fs : List (Form n)) (rs : List (Rec n)) (f : Form n) (i : ℕ) :
    getF ⟨fs ++ [f], rs⟩ i = if i < fs.length then fs.getD i zeroF else if i = fs.length then f else zeroF := by
  unfold getF
  split_ifs with h1 h2
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · subst h2; simp [List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem fv_zero {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) : fv U vs zeroF = false := by
  simp [fv, zeroF, sv]

theorem inv_push {n : ℕ} (U : Finset (Fin n)) (W : List Bool) (s : St n) (f : Form n) (x : Bool)
    (hI : Inv U W s) (hf : RefsLt s.rs.length f) (hx : x = fv U (rvals U s.rs) f) :
    Inv U (W ++ [x]) ⟨s.fs ++ [f], s.rs⟩ := by
  obtain ⟨hl, hr, hg, hv⟩ := hI
  refine ⟨by simp [hl], ?_, hg, ?_⟩
  · intro f' hf'
    rcases List.mem_append.1 hf' with h | h
    · exact hr f' h
    · simp at h; subst h; exact hf
  · intro i
    rw [getF_push]
    split_ifs with h1 h2
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      have := hv i
      unfold getF at this
      exact this
    · subst h2; rw [hl]; simp [List.getD_eq_getElem?_getD, hx]
    · rw [List.getD_eq_default _ _ (by simp; omega), fv_zero]

theorem inv_rec {n : ℕ} (U : Finset (Fin n)) (W : List Bool) (s : St n) (r : Rec n) (x : Bool)
    (hI : Inv U W s) (h1 : ∀ j ∈ r.2.1, j < s.rs.length) (h2 : ∀ j ∈ r.2.2.2, j < s.rs.length)
    (hx : x = (sv U (rvals U s.rs) r.1 r.2.1 && sv U (rvals U s.rs) r.2.2.1 r.2.2.2)) :
    Inv U (W ++ [x]) ⟨s.fs ++ [some (∅, {s.rs.length})], s.rs ++ [r]⟩ := by
  obtain ⟨hl, hr, hg, hv⟩ := hI
  refine ⟨by simp [hl], ?_, ?_, ?_⟩
  · intro f' hf'
    simp only [List.length_append, List.length_cons, List.length_nil]
    rcases List.mem_append.1 hf' with h | h
    · intro p hp j hj; have := hr f' h p hp j hj; omega
    · simp at h; subst h; intro p hp j hj; simp at hp; subst hp; simp at hj; omega
  · intro k hk
    simp only [List.length_append, List.length_cons, List.length_nil] at hk
    by_cases hk' : k < s.rs.length
    · rw [List.getElem_append_left hk']; exact hg k hk'
    · have : k = s.rs.length := by omega
      subst this
      simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
      exact ⟨h1, h2⟩
  · intro i
    rw [getF_push]
    split_ifs with hi1 hi2
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      have := hv i
      unfold getF at this
      rw [this, fv_snoc U s.rs r]
      have := hr _ (List.getElem_mem (by omega : i < s.fs.length))
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact this
    · subst hi2
      rw [hl]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.getD_some]
      have hlen : (rvals U s.rs).length = s.rs.length := rvals_len U s.rs
      simp only [fv, sv, rvals_snoc, rvStep, Finset.mem_singleton, exists_eq_left]
      rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
      simp [hx, sv]
    · rw [List.getD_eq_default _ _ (by simp; omega), fv_zero]

def Ok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem step_inv {n : ℕ} (U : Finset (Fin n)) (W : List Bool) (s : St n) (g : Gate)
    (hI : Inv U W s) (hg : Ok g) : Inv U (Fw W g) (step s g) := by
  have hv := hI.2.2.2
  have hR : ∀ i, RefsLt s.rs.length (getF s i) := refs_getF s.rs.length s hI.2.1
  obtain ⟨hop, hlen⟩ := hg
  rcases g with ⟨op, ins⟩
  simp only at hop hlen
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · apply inv_push U W s none _ hI (by intro p hp; simp at hp)
      simp [GateOp.eval, fv]
    · apply inv_push U W s (getF s a) _ hI (hR a)
      have := hv a
      simp only [List.getD_eq_getElem?_getD] at this
      simp [Fw, GateOp.eval, this]
    · show Inv U (Fw W ⟨GateOp.and, [a, b]⟩) (andStep s (getF s a) (getF s b))
      have ea := hv a
      have eb := hv b
      rcases hfa : getF s a with _ | ⟨va, ga⟩ <;> rcases hfb : getF s b with _ | ⟨vb, gb⟩
      · apply inv_push U W s none _ hI (by intro p hp; simp at hp)
        rw [hfa] at ea; rw [hfb] at eb
        simp [Fw, GateOp.eval, fv] at ea eb ⊢; simp [ea, eb]
      · apply inv_push U W s (some (vb, gb)) _ hI (hfb ▸ hR b)
        rw [hfa] at ea; rw [hfb] at eb
        simp [GateOp.eval, fv] at ea eb ⊢; simp [ea, eb]
      · apply inv_push U W s (some (va, ga)) _ hI (hfa ▸ hR a)
        rw [hfa] at ea; rw [hfb] at eb
        simp [GateOp.eval, fv] at ea eb ⊢; simp [ea, eb]
      · have ha := hR a; rw [hfa] at ha
        have hb := hR b; rw [hfb] at hb
        apply inv_rec U W s (va, ga, vb, gb) _ hI (ha _ rfl) (hb _ rfl)
        rw [hfa] at ea; rw [hfb] at eb
        simp only [fv, List.getD_eq_getElem?_getD] at ea eb
        simp [Fw, GateOp.eval, ea, eb]
    · simp at hlen
  · apply inv_push U W s (orF (ins.map (getF s))) _ hI
      (refs_orF _ _ (fun f hf => by
        obtain ⟨i, _, rfl⟩ := List.mem_map.1 hf
        exact hR i))
    rw [fv_orF]
    simp only [GateOp.eval, List.any_map]
    congr 1
    funext i
    have := hv i
    simp only [List.getD_eq_getElem?_getD] at this
    simp [Function.comp, this]

theorem fold_inv {n : ℕ} (U : Finset (Fin n)) (gs : List Gate) (hgs : ∀ g ∈ gs, Ok g) :
    ∀ (W : List Bool) (s : St n), Inv U W s → Inv U (gs.foldl Fw W) (gs.foldl step s) := by
  induction gs with
  | nil => intro W s h; exact h
  | cons g gs ih =>
    intro W s h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (by simp [hg'])) _ _ (step_inv U W s g h (hgs g (by simp)))

def isAnd (g : Gate) : Bool := match g.op with
  | GateOp.and => true
  | _ => false

theorem isAnd_iff (g : Gate) : isAnd g = true ↔ g.op = GateOp.and := by
  unfold isAnd
  split <;> simp_all

theorem step_rs {n : ℕ} (s : St n) (g : Gate) :
    (step s g).rs.length ≤ s.rs.length + (if isAnd g = true then 1 else 0) := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp only [step, isAnd] <;> try simp
  rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp only [step]
  · simp
  · simp
  · unfold andStep
    split <;> simp

theorem fold_rs {n : ℕ} (gs : List Gate) :
    ∀ s : St n, (gs.foldl step s).rs.length ≤ s.rs.length + gs.countP isAnd := by
  induction gs with
  | nil => intro s; simp
  | cons g gs ih =>
    intro s
    simp only [List.foldl_cons, List.countP_cons]
    have h1 := ih (step s g)
    have h2 := step_rs s g
    split_ifs at h2 ⊢ <;> omega

theorem rvals_split {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (k : ℕ) :
    rvals U rs = (rs.drop k).foldl (rvStep U) (rvals U (rs.take k)) := by
  unfold rvals
  rw [← List.foldl_append, List.take_append_drop]

theorem rvals_take {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (k j : ℕ) (hj : j < k) (hk : k ≤ rs.length) :
    (rvals U rs).getD j false = (rvals U (rs.take k)).getD j false := by
  rw [rvals_split U rs k, rv_pre]
  rw [rvals_len, List.length_take]; omega

theorem rec_val {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (hg : GoodRecs rs) (k : ℕ) (hk : k < rs.length) :
    (rvals U rs).getD k false = (sv U (rvals U rs) rs[k].1 rs[k].2.1 && sv U (rvals U rs) rs[k].2.2.1 rs[k].2.2.2) := by
  rw [rvals_take U rs (k + 1) k (by omega) (by omega)]
  rw [List.take_succ_eq_append_getElem hk, rvals_snoc]
  have hl : (rvals U (rs.take k)).length = k := by rw [rvals_len, List.length_take]; omega
  simp only [rvStep]
  rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
  simp only [List.getD_cons_zero]
  obtain ⟨h1, h2⟩ := hg k hk
  congr 1
  · apply sv_congr; intro j hj; exact (rvals_take U rs k j (h1 j hj) (by omega)).symm
  · apply sv_congr; intro j hj; exact (rvals_take U rs k j (h2 j hj) (by omega)).symm

def toACC {n : ℕ} (rs : List (Rec n)) (V : Finset (Fin n)) (G : Finset ℕ) : PEqualNP.AndCount.AndCountCircuit n where
  size := rs.length
  leftVars i := rs[i].1
  leftGates i := Finset.univ.filter (fun j : Fin rs.length => j.val ∈ rs[i].2.1)
  rightVars i := rs[i].2.2.1
  rightGates i := Finset.univ.filter (fun j : Fin rs.length => j.val ∈ rs[i].2.2.2)
  outVars := V
  outGates := Finset.univ.filter (fun j : Fin rs.length => j.val ∈ G)

theorem side_eq {n : ℕ} (U : Finset (Fin n)) (m : ℕ) (B : Finset (Fin n)) (G : Finset ℕ) (i : Fin m)
    (val : Fin m → Bool) (vs : List Bool) (hG : ∀ j ∈ G, j < i.val)
    (hval : ∀ j : Fin m, j < i → val j = vs.getD j false) :
    PEqualNP.AndCount.AndCountCircuit.sideTrue U B (Finset.univ.filter (fun j : Fin m => j.val ∈ G)) i val
      = sv U vs B G := by
  unfold PEqualNP.AndCount.AndCountCircuit.sideTrue sv
  rw [Bool.decide_or]
  congr 2
  apply propext
  constructor
  · rintro ⟨j, hj, hji, hv⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ⟨j.val, hj, by rw [← hval j hji]; exact hv⟩
  · rintro ⟨j, hj, hv⟩
    have hji := hG j hj
    refine ⟨⟨j, by omega⟩, by simp [hj], hji, ?_⟩
    rw [hval ⟨j, by omega⟩ hji]
    exact hv

theorem fuel {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (hg : GoodRecs rs) (V : Finset (Fin n)) (G : Finset ℕ) :
    ∀ d (i : Fin rs.length), i.val < d →
      (toACC rs V G).gateValFuel U d i = (rvals U rs).getD i false := by
  intro d
  induction d with
  | zero => intro i hi; omega
  | succ d ih =>
    intro i hi
    rw [rec_val U rs hg i i.isLt]
    obtain ⟨h1, h2⟩ := hg i i.isLt
    simp only [PEqualNP.AndCount.AndCountCircuit.gateValFuel]
    have hv : ∀ j : Fin rs.length, j < i → (toACC rs V G).gateValFuel U d j = (rvals U rs).getD j false :=
      fun j hj => ih j (by omega)
    congr 1
    · exact side_eq U rs.length _ _ i _ _ h1 hv
    · exact side_eq U rs.length _ _ i _ _ h2 hv

theorem eval_eq {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (hg : GoodRecs rs) (V : Finset (Fin n)) (G : Finset ℕ)
    (hG : ∀ j ∈ G, j < rs.length) : (toACC rs V G).eval U = sv U (rvals U rs) V G := by
  unfold PEqualNP.AndCount.AndCountCircuit.eval sv
  rw [Bool.decide_or]
  congr 2
  apply propext
  constructor
  · rintro ⟨j, hj, hv⟩
    have hj' : j.val ∈ G := (Finset.mem_filter.1 hj).2
    refine ⟨j.val, hj', ?_⟩
    exact (fuel U rs hg V G rs.length j j.isLt).symm.trans hv
  · rintro ⟨j, hj, hv⟩
    refine ⟨⟨j, hG j hj⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩, ?_⟩
    exact (fuel U rs hg V G rs.length ⟨j, hG j hj⟩ (hG j hj)).trans hv

theorem wf {n : ℕ} (rs : List (Rec n)) (hg : GoodRecs rs) (V : Finset (Fin n)) (G : Finset ℕ) :
    (toACC rs V G).WellFormed := by
  intro i
  obtain ⟨h1, h2⟩ := hg i i.isLt
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · exact h1 j (Finset.mem_filter.1 hj).2
  · exact h2 j (Finset.mem_filter.1 hj).2

theorem t4682 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∃ (x3 : Finset (Fin (27 : ℕ))), (PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x1 fun (x4 : Fin (27 : ℕ)) => Decidable.decide (x4 ∈ x3)) = Bool.false) → ∃ (x4 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)), x4.WellFormed ∧ x4.size ≤ Nat.card { x5 : Fin x1.gates.length // (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and } ∧ ∀ (x5 : Finset (Fin (27 : ℕ))), x4.eval x5 = PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x1 fun (x6 : Fin (27 : ℕ)) => Decidable.decide (x6 ∈ x5) := by
  intro C hmono hex
  obtain ⟨U0, hU0⟩ := hex
  have hok : ∀ g ∈ C.gates, PEqualNP.Outside.L_meta_8043.B.Ok g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hmono g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact ⟨h1, h2⟩
  let s0 : PEqualNP.Outside.L_meta_8043.B.St 27 := ⟨List.ofFn (fun i : Fin 27 => some ({i}, ∅)), []⟩
  let s := C.gates.foldl PEqualNP.Outside.L_meta_8043.B.step s0
  have hinit : ∀ U : Finset (Fin 27), PEqualNP.Outside.L_meta_8043.B.Inv U (List.ofFn fun x : Fin 27 => decide (x ∈ U)) s0 := by
    intro U
    refine ⟨by simp [s0], ?_, ?_, ?_⟩
    · intro f hf p hp j hj
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hf
      simp only [Option.some.injEq] at hp
      subst hp
      simp at hj
    · intro k hk; simp [s0] at hk
    · intro i
      by_cases hi : i < 27
      · simp only [PEqualNP.Outside.L_meta_8043.B.getF, s0]
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn,
          List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
        simp [PEqualNP.Outside.L_meta_8043.B.fv, PEqualNP.Outside.L_meta_8043.B.sv]
      · rw [List.getD_eq_default _ _ (by simp; omega)]
        simp only [PEqualNP.Outside.L_meta_8043.B.getF, s0]
        rw [List.getD_eq_default _ _ (by simp; omega), PEqualNP.Outside.L_meta_8043.B.fv_zero]
  have hinv : ∀ U : Finset (Fin 27), PEqualNP.Outside.L_meta_8043.B.Inv U (C.gates.foldl PEqualNP.Outside.L_meta_8043.B.Fw (List.ofFn fun x : Fin 27 => decide (x ∈ U))) s :=
    fun U => PEqualNP.Outside.L_meta_8043.B.fold_inv U C.gates hok _ _ (hinit U)
  have hfun : ∀ U : Finset (Fin 27), PEqualNP.MetaComplexity.circuitFun 27 C (fun x => decide (x ∈ U))
      = PEqualNP.Outside.L_meta_8043.B.fv U (PEqualNP.Outside.L_meta_8043.B.rvals U s.rs) (PEqualNP.Outside.L_meta_8043.B.getF s C.output) := fun U => (hinv U).2.2.2 C.output
  rcases hfo : PEqualNP.Outside.L_meta_8043.B.getF s C.output with _ | ⟨V, G⟩
  · have := hfun U0
    rw [hfo, hU0] at this
    simp [PEqualNP.Outside.L_meta_8043.B.fv] at this
  · have hG : ∀ j ∈ G, j < s.rs.length := PEqualNP.Outside.L_meta_8043.B.refs_getF _ s (hinv U0).2.1 C.output _ hfo
    have hgood := (hinv U0).2.2.1
    refine ⟨PEqualNP.Outside.L_meta_8043.B.toACC s.rs V G, PEqualNP.Outside.L_meta_8043.B.wf s.rs hgood V G, ?_, ?_⟩
    · have h1 := PEqualNP.Outside.L_meta_8043.B.fold_rs C.gates s0
      have h2 : C.gates.countP PEqualNP.Outside.L_meta_8043.B.isAnd = Nat.card {x5 : Fin C.gates.length // (C.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and} := by
        classical
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        conv_lhs => rw [← List.ofFn_get C.gates]
        rw [List.countP_ofFn]
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, PEqualNP.Outside.L_meta_8043.B.isAnd_iff]
      change s.rs.length ≤ s0.rs.length + _ at h1
      have h0 : s0.rs.length = 0 := rfl
      show s.rs.length ≤ _
      omega
    · intro U
      rw [PEqualNP.Outside.L_meta_8043.B.eval_eq U s.rs hgood V G hG, hfun U, hfo]
      rfl

end PEqualNP.Outside.L_meta_8043.B

theorem PEqualNP.Outside.L_meta_8043 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∃ (x3 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)), x3.WellFormed ∧ x3.size ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), x3.eval {x5 : Fin (27 : ℕ) | Fin.cases Bool.true (fun (x6 : Fin (26 : ℕ)) => !x4 x6) x5 = Bool.true} = !PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 x4 := by
  intro C hC
  obtain ⟨D, hD, hcard, hfun⟩ := PEqualNP.Outside.L_meta_8043.A.t4680 C hC
  by_cases hex : ∃ U0 : Finset (Fin 27),
      PEqualNP.MetaComplexity.circuitFun 27 D (fun x => decide (x ∈ U0)) = false
  · obtain ⟨E, hE, hsz, hev⟩ := PEqualNP.Outside.L_meta_8043.B.t4682 D hD hex
    refine ⟨E, hE, hsz.trans hcard, fun x4 => ?_⟩
    rw [hev, ← hfun x4]
    congr 1
    funext x6
    simp
  · push_neg at hex
    refine ⟨⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, {0}, ∅⟩,
      by intro i; exact i.elim0, Nat.zero_le _, fun x4 => ?_⟩
    rw [← hfun x4]
    have h1 := hex (Finset.univ.filter fun x5 : Fin 27 =>
      Fin.cases true (fun x6 : Fin 26 => !x4 x6) x5 = true)
    have e : (fun x : Fin 27 => decide (x ∈ Finset.univ.filter fun x5 : Fin 27 =>
        Fin.cases true (fun x6 : Fin 26 => !x4 x6) x5 = true))
        = (fun x5 : Fin (26 + 1) => Fin.cases true (fun x6 : Fin 26 => !x4 x6) x5) := by
      funext x
      simp
    rw [e] at h1
    have h3 : PEqualNP.MetaComplexity.circuitFun 27 D
        (fun x5 : Fin (26 + 1) => Fin.cases true (fun x6 : Fin 26 => !x4 x6) x5) = true := by
      simpa using h1
    refine Eq.trans ?_ h3.symm
    simp [PEqualNP.AndCount.AndCountCircuit.eval]
