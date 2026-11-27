import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_545_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

lemma run_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    run (gs₁ ++ gs₂) w = run gs₂ (run gs₁ w) :=
  List.foldl_append

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

lemma getD_snoc_lt {α : Type*} (w : List α) (b : α) (i : ℕ) (hi : i < w.length) (d : α) :
    (w ++ [b]).getD i d = w.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

lemma getD_snoc_eq {α : Type*} (w : List α) (b : α) (d : α) :
    (w ++ [b]).getD w.length d = b := by
  simp [List.getD]

lemma getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD, hi]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def NOk (g : Gate) : Prop :=
  Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp only [normGate]
  cases ins <;> simp [GateOp.eval]

lemma normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := h
  change op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not at hop
  rcases hop with rfl | rfl | rfl
  · exact ⟨⟨by simp [normGate], hlen⟩, by simp [normGate]⟩
  · exact ⟨⟨by simp [normGate], hlen⟩, by simp [normGate]⟩
  · refine ⟨⟨by simp [normGate], ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

lemma run_norm (gs : List Gate) (w : List Bool) :
    run (gs.map normGate) w = run gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons]
    change run (gs.map normGate) (step w (normGate g)) = run gs (step w g)
    have hstep : step w (normGate g) = step w g := by
      simp only [step, normGate_eval]
    rw [hstep, ih]

lemma run_indep_of_not_mem (n : ℕ) (gs : List Gate)
    (hno : ∀ g ∈ gs, n ∉ g.inputs)
    (w₁ w₂ : List Bool) (h1 : n + 1 ≤ w₁.length) (h2 : w₁.length = w₂.length)
    (hag : ∀ i, i ≠ n → w₁.getD i false = w₂.getD i false) :
    ∀ i, i ≠ n → (run gs w₁).getD i false = (run gs w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact hag
  | cons g gs ih =>
    change ∀ i, i ≠ n → (run gs (step w₁ g)).getD i false = (run gs (step w₂ g)).getD i false
    apply ih (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (step w₁ g) (step w₂ g)
    · simp [step]; omega
    · simp [step, h2]
    · intro i hi
      have hgeval : g.op.eval (g.inputs.map fun j => w₁.getD j false) =
          g.op.eval (g.inputs.map fun j => w₂.getD j false) := by
        congr 1
        apply List.map_congr_left
        intro j hj
        exact hag j (fun hjn => hno g (List.mem_cons_self ..) (hjn ▸ hj))
      by_cases hlt : i < w₁.length
      · rw [step, step, getD_snoc_lt _ _ _ hlt, getD_snoc_lt _ _ _ (by omega)]
        exact hag i hi
      · by_cases heq : i = w₁.length
        · subst heq
          rw [step, step, getD_snoc_eq, h2, getD_snoc_eq, hgeval]
        · rw [List.getD_eq_default _ _ (by simp [step]; omega),
            List.getD_eq_default _ _ (by simp [step]; omega)]

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; exact ⟨by simp, by simp⟩)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; exact ⟨by simp, by simp⟩)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; exact ⟨by simp, by simp⟩)
  · simp at hg
  · simp at hg

lemma simplify_none_of_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hlen : ins.length ≤ 2) (hnot : op = GateOp.not → ins.length ≤ 1)
    (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  rcases hc with ⟨c, hc⟩
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp at hc
    · cases a <;> simp [simplify, simpAnd] at hc ⊢
    · cases a <;> cases b <;> simp [simplify, simpAnd] at hc ⊢
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp at hc
    · cases a <;> simp [simplify, simpOr] at hc ⊢
    · cases a <;> cases b <;> simp [simplify, simpOr] at hc ⊢
    · simp at hlen
  · have h1 := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp at hc
    · cases a <;> simp [simplify, simpNot] at hc ⊢
    · simp at h1

lemma simplify_valid (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hlen : ins.length ≤ 2) (hnot : op = GateOp.not → ins.length ≤ 1)
    (hval : ∀ s ∈ ins, s.Valid m) :
    let res := simplify op m ins
    res.2.Valid (match res.1 with | none => m | some _ => m + 1) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid]
    · cases a with
      | const c => simp [simplify, simpAnd, Stat.Valid]
      | wire j => exact hval (Stat.wire j) (by simp)
    · cases a with
      | const c =>
        cases b with
        | const d => simp [simplify, simpAnd, Stat.Valid]
        | wire j =>
          cases c
          · simp [simplify, simpAnd, Stat.Valid]
          · simpa [simplify, simpAnd] using hval (Stat.wire j) (by simp)
      | wire j =>
        cases b with
        | const d =>
          cases d
          · simp [simplify, simpAnd, Stat.Valid]
          · simpa [simplify, simpAnd] using hval (Stat.wire j) (by simp)
        | wire k =>
          simpa [simplify, simpAnd, Stat.Valid] using Nat.lt_succ_self m
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid]
    · cases a with
      | const c => simp [simplify, simpOr, Stat.Valid]
      | wire j => exact hval (Stat.wire j) (by simp)
    · cases a with
      | const c =>
        cases b with
        | const d => simp [simplify, simpOr, Stat.Valid]
        | wire j =>
          cases c
          · simpa [simplify, simpOr] using hval (Stat.wire j) (by simp)
          · simp [simplify, simpOr, Stat.Valid]
      | wire j =>
        cases b with
        | const d =>
          cases d
          · simpa [simplify, simpOr] using hval (Stat.wire j) (by simp)
          · simp [simplify, simpOr, Stat.Valid]
        | wire k =>
          simpa [simplify, simpOr, Stat.Valid] using Nat.lt_succ_self m
    · simp at hlen
  · have h1 := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [simplify, simpNot, Stat.Valid]
    · cases a with
      | const c => simp [simplify, simpNot, Stat.Valid]
      | wire j => simpa [simplify, simpNot, Stat.Valid] using Nat.lt_succ_self m
    · simp at h1

lemma simplify_eval (op : GateOp) (w : List Bool) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hlen : ins.length ≤ 2) (hnot : op = GateOp.not → ins.length ≤ 1) :
    let res := simplify op w.length ins
    let w' := match res.1 with | none => w | some g => step w g
    res.2.val w' = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.val, GateOp.eval]
    · cases a <;> simp [simplify, simpAnd, Stat.val, GateOp.eval]
    · cases a with
      | const c => cases b with
        | const d => simp [simplify, simpAnd, Stat.val, GateOp.eval]
        | wire j => cases c <;> simp [simplify, simpAnd, Stat.val, GateOp.eval]
      | wire j => cases b with
        | const d => cases d <;> simp [simplify, simpAnd, Stat.val, GateOp.eval]
        | wire k =>
          simp [simplify, simpAnd, Stat.val, step, getD_snoc_eq, GateOp.eval]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.val, GateOp.eval]
    · cases a <;> simp [simplify, simpOr, Stat.val, GateOp.eval]
    · cases a with
      | const c => cases b with
        | const d => simp [simplify, simpOr, Stat.val, GateOp.eval]
        | wire j => cases c <;> simp [simplify, simpOr, Stat.val, GateOp.eval]
      | wire j => cases b with
        | const d => cases d <;> simp [simplify, simpOr, Stat.val, GateOp.eval]
        | wire k =>
          simp [simplify, simpOr, Stat.val, step, getD_snoc_eq, GateOp.eval]
    · simp at hlen
  · have h1 := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [simplify, simpNot, Stat.val, GateOp.eval]
    · cases a with
      | const c => simp [simplify, simpNot, Stat.val, GateOp.eval]
      | wire j =>
        simp [simplify, simpNot, Stat.val, step, getD_snoc_eq, GateOp.eval]
    · simp at h1

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  let (st, gs) := acc
  let ins := g.inputs.map fun i => st.getD i (Stat.const false)
  let (og, s) := simplify g.op (n + gs.length) ins
  let gs' := match og with | none => gs | some g' => gs ++ [g']
  (st ++ [s], gs')

def elimPass (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

lemma elimPass_main (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, NOk g) :
    ∀ (st : List Stat) (outGs : List Gate),
      (∀ s ∈ st, s.Valid (n + outGs.length)) →
      (∀ g ∈ outGs, Ok g) →
      let res := elimPass n gs (st, outGs)
      (∀ s ∈ res.1, s.Valid (n + res.2.length)) ∧
      (∀ g ∈ res.2, Ok g) ∧
      res.2.length ≤ outGs.length + gs.length ∧
      (∀ k < st.length, res.1.getD k (Stat.const false) = st.getD k (Stat.const false)) ∧
      ((∃ g ∈ gs, ∃ i ∈ g.inputs, i < st.length ∧ ∃ c, st.getD i (Stat.const false) = Stat.const c) →
        res.2.length + 1 ≤ outGs.length + gs.length) ∧
      (∀ (y : Fin n → Bool) (wOld : List Bool),
        wOld.length = st.length →
        (∀ i, wOld.getD i false = (st.getD i (Stat.const false)).val (run outGs (List.ofFn y))) →
        ∀ i, (run gs wOld).getD i false =
          (res.1.getD i (Stat.const false)).val (run res.2 (List.ofFn y))) := by
  induction gs with
  | nil =>
    intro st outGs hv ho
    refine ⟨hv, ho, le_rfl, fun _ _ => rfl, ?_, ?_⟩
    · rintro ⟨g, hg, _⟩; simp at hg
    · intro y wOld _ hag i; exact hag i
  | cons g gs ih =>
    intro st outGs hv ho
    have hg_nok : NOk g := hgs g (List.mem_cons_self ..)
    have hgs_nok : ∀ g' ∈ gs, NOk g' := fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    set ins := g.inputs.map fun i => st.getD i (Stat.const false)
    set res1 := simplify g.op (n + outGs.length) ins
    set outGs1 : List Gate := match res1.1 with | none => outGs | some g' => outGs ++ [g']
    set st1 : List Stat := st ++ [res1.2]
    have hins_val : ∀ s ∈ ins, s.Valid (n + outGs.length) := by
      intro s hs
      rcases List.mem_map.mp hs with ⟨i, _, rfl⟩
      by_cases hi : i < st.length
      · exact hv _ (by simp [List.getD, hi])
      · rw [List.getD_eq_default _ _ (by omega)]; trivial
    have hstep_len : outGs1.length ≤ outGs.length + 1 := by
      cases h : res1.1 <;> simp [outGs1, h]
    have hstep_ok : ∀ g' ∈ outGs1, Ok g' := by
      cases h : res1.1 with
      | none => simpa [outGs1, h] using ho
      | some g' =>
        intro x hx
        simp only [outGs1, h, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact ho x hx
        · exact simplify_ok g.op (n + outGs.length) ins x h
    have hstep_valid : ∀ s ∈ st1, s.Valid (n + outGs1.length) := by
      intro s hs
      simp only [st1, List.mem_append, List.mem_singleton] at hs
      rcases hs with hs | rfl
      · have hvs := hv s hs
        cases s with
        | const _ => trivial
        | wire j =>
          change j < n + outGs.length at hvs
          change j < n + outGs1.length
          cases h : res1.1 <;> simp [outGs1, h] <;> omega
      · have hvv := simplify_valid g.op (n + outGs.length) ins
          hg_nok.1.1 (by simpa [ins] using hg_nok.1.2)
          (fun hn => by simpa [ins] using hg_nok.2 hn) hins_val
        have hlen_m : (match res1.1 with | none => n + outGs.length | some _ => n + outGs.length + 1) =
            n + outGs1.length := by
          cases h : res1.1 <;> simp [outGs1, h] <;> omega
        simpa [res1, hlen_m] using hvv
    have hrec := ih hgs_nok st1 outGs1 hstep_valid hstep_ok
    obtain ⟨hv', ho', hlen', hget', hdrop', hev'⟩ := hrec
    have hpass_eq : elimPass n (g :: gs) (st, outGs) = elimPass n gs (st1, outGs1) := rfl
    dsimp only
    rw [hpass_eq]
    refine ⟨hv', ho', by simp; omega, ?_, ?_, ?_⟩
    · intro k hk
      rw [hget' k (by simp [st1]; omega)]
      exact getD_snoc_lt st res1.2 k hk (Stat.const false)
    · rintro ⟨g0, hg0, i, hi, hist, c, hc⟩
      simp only [List.mem_cons] at hg0
      rcases hg0 with hg0eq | hg0
      · rw [hg0eq] at hi
        have hcin : Stat.const c ∈ ins := List.mem_map.mpr ⟨i, hi, hc⟩
        have hnone : res1.1 = none :=
          simplify_none_of_const g.op (n + outGs.length) ins hg_nok.1.1
            (by simpa [ins] using hg_nok.1.2) (fun hn => by simpa [ins] using hg_nok.2 hn) ⟨c, hcin⟩
        have hout1_eq : outGs1 = outGs := by simp [outGs1, hnone]
        rw [hout1_eq] at hlen' ⊢
        simp; omega
      · have hdrop1 : (elimPass n gs (st1, outGs1)).2.length + 1 ≤ outGs1.length + gs.length :=
          hdrop' ⟨g0, hg0, i, hi, by simp [st1]; omega, c, by
            rw [getD_snoc_lt st res1.2 i hist (Stat.const false)]; exact hc⟩
        simp; omega
    · intro y wOld hlen_old hag
      have hlen_run : (run outGs (List.ofFn y)).length = n + outGs.length := by
        rw [run_length, List.length_ofFn]
      have hrun1 : run outGs1 (List.ofFn y) =
          match res1.1 with
          | none => run outGs (List.ofFn y)
          | some g' => step (run outGs (List.ofFn y)) g' := by
        cases h : res1.1 with
        | none => simp [outGs1, h]
        | some g' =>
          simp only [outGs1, h]
          rw [run_append]
          rfl
      have hve2 := simplify_eval g.op (run outGs (List.ofFn y)) ins
        hg_nok.1.1 (by simpa [ins] using hg_nok.1.2)
        (fun hn => by simpa [ins] using hg_nok.2 hn)
      rw [hlen_run] at hve2
      have hres2_val : res1.2.val (run outGs1 (List.ofFn y)) =
          g.op.eval (g.inputs.map fun j => wOld.getD j false) := by
        rw [hrun1]
        have hres2 : res1.2.val (match res1.1 with
            | none => run outGs (List.ofFn y)
            | some g' => step (run outGs (List.ofFn y)) g') =
            g.op.eval (ins.map (Stat.val (run outGs (List.ofFn y)))) := by
          simpa [res1] using hve2
        rw [hres2]
        congr 1
        simp only [ins, List.map_map]
        apply List.map_congr_left
        intro j _
        exact (hag j).symm
      apply hev' y (step wOld g) (by simp [step, st1, hlen_old])
      intro i
      by_cases hlt : i < wOld.length
      · have hlt_st : i < st.length := by omega
        rw [step, getD_snoc_lt _ _ _ hlt, show st1 = st ++ [res1.2] from rfl,
          getD_snoc_lt _ _ _ hlt_st, hag i]
        have hvi : (st.getD i (Stat.const false)).Valid (n + outGs.length) :=
          hv _ (by simp [List.getD, hlt_st])
        cases hs : st.getD i (Stat.const false) with
        | const c => rfl
        | wire j =>
          rw [hs] at hvi
          change j < n + outGs.length at hvi
          simp only [Stat.val]
          rw [hrun1]
          cases h : res1.1 with
          | none => rfl
          | some g' =>
            symm
            exact getD_snoc_lt _ _ _ (by rw [hlen_run]; exact hvi) false
      · by_cases heq : i = wOld.length
        · subst heq
          rw [step, getD_snoc_eq, hlen_old, show st1 = st ++ [res1.2] from rfl,
            getD_snoc_eq, hres2_val]
        · rw [List.getD_eq_default _ _ (by simp [step]; omega),
            List.getD_eq_default _ _ (by simp [st1]; omega)]
          rfl

theorem elim_last_false {n s : ℕ} (h : (Fin (n + 1) → Bool) → Bool)
    (hdep : ∃ y : Fin n → Bool, h (Fin.snoc y false) ≠ h (Fin.snoc y true))
    (hnc : ∃ y y' : Fin n → Bool, h (Fin.snoc y false) ≠ h (Fin.snoc y' false))
    (hcs : HasCircuitSize (n + 1) h s) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧ HasCircuitSize n (fun y => h (Fin.snoc y false)) s' := by
  obtain ⟨C, hfan, hsize, heval⟩ := hcs
  let gs := C.gates.map normGate
  have hgs_nok : ∀ g ∈ gs, NOk g := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
    exact normGate_nok g0 (hfan g0 hg0)
  have hgs_len : gs.length = C.gates.length := List.length_map ..
  have hgs_eval : ∀ x : Fin (n + 1) → Bool,
      (run gs (List.ofFn x)).getD C.output false = h x := by
    intro x
    rw [← heval x]
    change (run (C.gates.map normGate) (List.ofFn x)).getD C.output false =
      (run C.gates (List.ofFn x)).getD C.output false
    rw [run_norm]
  have hreads : ∃ g ∈ gs, n ∈ g.inputs := by
    by_contra hno
    push Not at hno
    by_cases hout : C.output = n
    · obtain ⟨y, y', hyy'⟩ := hnc
      have h1 : h (Fin.snoc y false) = false := by
        rw [← hgs_eval (Fin.snoc y false), hout]
        have hlt : n < (List.ofFn (Fin.snoc y false)).length := by simp
        -- wait: output n is invariant under run!
        have hrun_in : ∀ (l : List Gate) (w : List Bool), n < w.length →
            (run l w).getD n false = w.getD n false := by
          intro l
          induction l with
          | nil => intro _ _; rfl
          | cons g l ih =>
            intro w hw
            change (run l (step w g)).getD n false = w.getD n false
            rw [ih _ (by simp [step]; omega), step, getD_snoc_lt _ _ _ hw]
        rw [hrun_in gs _ hlt, getD_ofFn (Fin.snoc y false) n (by omega)]
        simpa [Fin.snoc]
      have h2 : h (Fin.snoc y' false) = false := by
        rw [← hgs_eval (Fin.snoc y' false), hout]
        have hlt : n < (List.ofFn (Fin.snoc y' false)).length := by simp
        have hrun_in : ∀ (l : List Gate) (w : List Bool), n < w.length →
            (run l w).getD n false = w.getD n false := by
          intro l
          induction l with
          | nil => intro _ _; rfl
          | cons g l ih =>
            intro w hw
            change (run l (step w g)).getD n false = w.getD n false
            rw [ih _ (by simp [step]; omega), step, getD_snoc_lt _ _ _ hw]
        rw [hrun_in gs _ hlt, getD_ofFn (Fin.snoc y' false) n (by omega)]
        simpa [Fin.snoc]
      exact hyy' (h1.trans h2.symm)
    · obtain ⟨y, hy⟩ := hdep
      have hsame := run_indep_of_not_mem n gs hno
        (List.ofFn (Fin.snoc y false)) (List.ofFn (Fin.snoc y true))
        (by simp) (by simp) (by
          intro i hi
          by_cases hlt : i < n
          · rw [getD_ofFn _ i (by omega), getD_ofFn _ i (by omega)]
            simp [Fin.snoc, hlt]
          · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)])
        C.output hout
      rw [hgs_eval, hgs_eval] at hsame
      exact hy hsame
  let st0 : List Stat := (List.range n).map Stat.wire ++ [Stat.const false]
  have hst0_len : st0.length = n + 1 := by simp [st0]
  have hst0_lt : ∀ i < n, st0.getD i (Stat.const false) = Stat.wire i := by
    intro i hi
    simp only [st0]
    rw [getD_snoc_lt _ _ _ (by simp; omega)]
    simp [List.getD, hi]
  have hst0_n : st0.getD n (Stat.const false) = Stat.const false := by
    simp only [st0]
    have hlen : ((List.range n).map Stat.wire).length = n := by simp
    simpa [hlen] using getD_snoc_eq ((List.range n).map Stat.wire) (Stat.const false) (Stat.const false)
  have hst0_val : ∀ s ∈ st0, s.Valid (n + ([] : List Gate).length) := by
    intro s hs
    simp only [st0, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hs
    rcases hs with ⟨i, hi, rfl⟩ | rfl
    · simpa [Stat.Valid] using hi
    · trivial
  obtain ⟨_, hok', _, _, hdrop', hev'⟩ := elimPass_main n gs hgs_nok st0 [] hst0_val (by simp)
  set res := elimPass n gs (st0, [])
  have hdrop : res.2.length + 1 ≤ s := by
    obtain ⟨g0, hg0, hn0⟩ := hreads
    have h1 := hdrop' ⟨g0, hg0, n, hn0, by omega, false, hst0_n⟩
    change C.gates.length ≤ s at hsize
    simp only [List.length_nil, zero_add] at h1
    omega
  have hev_all : ∀ y : Fin n → Bool,
      h (Fin.snoc y false) = (res.1.getD C.output (Stat.const false)).val (run res.2 (List.ofFn y)) := by
    intro y
    rw [← hgs_eval (Fin.snoc y false)]
    apply hev' y (List.ofFn (Fin.snoc y false)) (by simp [hst0_len])
    intro i
    by_cases hi : i < n
    · rw [hst0_lt i hi, getD_ofFn _ i (by omega)]
      simp [Stat.val, run, getD_ofFn y i hi, Fin.snoc, hi]
    · by_cases heq : i = n
      · rw [heq, hst0_n, getD_ofFn _ n (by omega)]
        simp [Stat.val, Fin.snoc]
      · rw [List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by omega)]
        rfl
  cases hout_st : res.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hyy'⟩ := hnc
    have h1 := hev_all y
    have h2 := hev_all y'
    rw [hout_st] at h1 h2
    exact hyy' (h1.trans h2.symm)
  | wire j =>
    refine ⟨res.2.length, hdrop, ⟨⟨res.2, j⟩, hok', le_rfl, fun y => ?_⟩⟩
    have hy := hev_all y
    rw [hout_st] at hy
    exact hy.symm

end PEqualNP.Outside.L_meta_545_aux

theorem PEqualNP.Outside.L_meta_545 :
    ∀ (n d s : ℕ) (g : (Fin n → Bool) → Bool) (v : Fin n),
      (∃ x : Fin n → Bool, x v = true ∧ g x = false) →
      PEqualNP.MetaComplexity.HasCircuitSize (n + (d + 1))
        (fun x : Fin (n + (d + 1)) → Bool =>
          g (fun i : Fin n => x (Fin.castAdd (d + 1) i)) ||
            (x (Fin.castAdd (d + 1) v) && decide (∃ j : Fin (d + 1), x (Fin.natAdd n j) = true))) s →
      ∃ s' : ℕ, s' + d ≤ s ∧
        PEqualNP.MetaComplexity.HasCircuitSize (n + 1)
          (fun x : Fin (n + 1) → Bool =>
            g (fun i : Fin n => x i.castSucc) || (x v.castSucc && x (Fin.last n))) s' := by
  intro n d
  induction d with
  | zero =>
    intro s g v _ hcs
    refine ⟨s, by omega, ?_⟩
    have hfun : (fun x : Fin (n + (0 + 1)) → Bool =>
        g (fun i : Fin n => x (Fin.castAdd (0 + 1) i)) ||
          (x (Fin.castAdd (0 + 1) v) && decide (∃ j : Fin (0 + 1), x (Fin.natAdd n j) = true))) =
        (fun x : Fin (n + 1) → Bool =>
          g (fun i : Fin n => x i.castSucc) || (x v.castSucc && x (Fin.last n))) := by
      funext x
      have hcast : ∀ i : Fin n, Fin.castAdd 1 i = i.castSucc := fun i => Fin.ext rfl
      have hex : decide (∃ j : Fin 1, x (Fin.natAdd n j) = true) = x (Fin.last n) := by
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨j, hj⟩
          have hj0 : j = 0 := Fin.ext (by omega)
          rw [hj0] at hj
          have hlast : Fin.natAdd n (0 : Fin 1) = Fin.last n := Fin.ext (by simp)
          rwa [hlast] at hj
        · intro h
          refine ⟨0, ?_⟩
          have hlast : Fin.natAdd n (0 : Fin 1) = Fin.last n := Fin.ext (by simp)
          rwa [hlast]
      simp only [hcast, hex]
    simpa only [hfun] using hcs
  | succ d ih =>
    intro s g v ⟨x0, hx0v, hx0g⟩ hcs
    let hd : (Fin (n + (d + 1)) → Bool) → Bool := fun y =>
      g (fun i : Fin n => y (Fin.castAdd (d + 1) i)) ||
        (y (Fin.castAdd (d + 1) v) && decide (∃ j : Fin (d + 1), y (Fin.natAdd n j) = true))
    let hd1 : (Fin ((n + (d + 1)) + 1) → Bool) → Bool := fun x =>
      g (fun i : Fin n => x (Fin.castAdd (d + 2) i)) ||
        (x (Fin.castAdd (d + 2) v) && decide (∃ j : Fin (d + 2), x (Fin.natAdd n j) = true))
    have hsnoc_f : ∀ y : Fin (n + (d + 1)) → Bool, hd1 (Fin.snoc y false) = hd y := by
      intro y
      have hcast : ∀ i : Fin n,
          (Fin.snoc y false : Fin ((n + (d + 1)) + 1) → Bool) (Fin.castAdd (d + 2) i) =
            y (Fin.castAdd (d + 1) i) := by
        intro i
        have heq : (Fin.castAdd (d + 2) i : Fin ((n + (d + 1)) + 1)) = (Fin.castAdd (d + 1) i).castSucc :=
          Fin.ext rfl
        rw [heq, Fin.snoc_castSucc]
      have hex : decide (∃ j : Fin (d + 2),
          (Fin.snoc y false : Fin ((n + (d + 1)) + 1) → Bool) (Fin.natAdd n j) = true) =
          decide (∃ j : Fin (d + 1), y (Fin.natAdd n j) = true) := by
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨j, hj⟩
          by_cases hlt : j.val < d + 1
          · refine ⟨⟨j.val, hlt⟩, ?_⟩
            have heq : (Fin.natAdd n j : Fin ((n + (d + 1)) + 1)) =
                (Fin.natAdd n (⟨j.val, hlt⟩ : Fin (d + 1))).castSucc :=
              Fin.ext rfl
            rw [heq, Fin.snoc_castSucc] at hj
            exact hj
          · exfalso
            have heq : (Fin.natAdd n j : Fin ((n + (d + 1)) + 1)) = Fin.last (n + (d + 1)) :=
              Fin.ext (by simp; omega)
            rw [heq, Fin.snoc_last] at hj
            exact Bool.false_ne_true hj
        · rintro ⟨j, hj⟩
          refine ⟨j.castSucc, ?_⟩
          have heq : (Fin.natAdd n j.castSucc : Fin ((n + (d + 1)) + 1)) =
              (Fin.natAdd n j).castSucc := Fin.ext rfl
          rw [heq, Fin.snoc_castSucc]
          exact hj
      simp only [hd1, hd, hcast, hex]
    let yFalse : Fin (n + (d + 1)) → Bool := fun i =>
      if h : i.val < n then x0 ⟨i.val, h⟩ else false
    let yTrue : Fin (n + (d + 1)) → Bool := fun i =>
      if h : i.val < n then x0 ⟨i.val, h⟩ else true
    have hyFalse_val : hd yFalse = false := by
      have hg0 : (fun i : Fin n => yFalse (Fin.castAdd (d + 1) i)) = x0 := by
        funext i; simp [yFalse, i.isLt]
      have hno : decide (∃ j : Fin (d + 1), yFalse (Fin.natAdd n j) = true) = false := by
        simp only [decide_eq_false_iff_not, not_exists]
        intro j
        have hge : ¬ (Fin.natAdd n j).val < n := by simp
        simp [yFalse, hge]
      simp only [hd, hg0, hx0g, hno, Bool.and_false, Bool.or_false]
    have hyTrue_val : hd yTrue = true := by
      have hv0 : yTrue (Fin.castAdd (d + 1) v) = true := by
        simp [yTrue, v.isLt, hx0v]
      have hyes : decide (∃ j : Fin (d + 1), yTrue (Fin.natAdd n j) = true) = true := by
        simp only [decide_eq_true_eq]
        refine ⟨⟨0, by omega⟩, ?_⟩
        have hge : ¬ (Fin.natAdd n (⟨0, by omega⟩ : Fin (d + 1))).val < n := by simp
        simp [yTrue, hge]
      simp only [hd, hv0, hyes, Bool.and_true, Bool.or_true]
    have hdep : ∃ y : Fin (n + (d + 1)) → Bool, hd1 (Fin.snoc y false) ≠ hd1 (Fin.snoc y true) := by
      refine ⟨yFalse, ?_⟩
      rw [hsnoc_f, hyFalse_val]
      have hv0 : (Fin.snoc yFalse true : Fin ((n + (d + 1)) + 1) → Bool) (Fin.castAdd (d + 2) v) = true := by
        have heq : (Fin.castAdd (d + 2) v : Fin ((n + (d + 1)) + 1)) = (Fin.castAdd (d + 1) v).castSucc :=
          Fin.ext rfl
        rw [heq, Fin.snoc_castSucc]
        simp [yFalse, v.isLt, hx0v]
      have hyes : decide (∃ j : Fin (d + 2),
          (Fin.snoc yFalse true : Fin ((n + (d + 1)) + 1) → Bool) (Fin.natAdd n j) = true) = true := by
        simp only [decide_eq_true_eq]
        refine ⟨Fin.last (d + 1), ?_⟩
        have heq : (Fin.natAdd n (Fin.last (d + 1)) : Fin ((n + (d + 1)) + 1)) =
            Fin.last (n + (d + 1)) := Fin.ext (by simp)
        rw [heq, Fin.snoc_last]
      simp only [hd1, hv0, hyes, Bool.and_true, Bool.or_true]
      decide
    have hnc : ∃ y y' : Fin (n + (d + 1)) → Bool, hd1 (Fin.snoc y false) ≠ hd1 (Fin.snoc y' false) := by
      refine ⟨yFalse, yTrue, ?_⟩
      rw [hsnoc_f, hsnoc_f, hyFalse_val, hyTrue_val]
      decide
    obtain ⟨s1, hs1, hcs1⟩ := PEqualNP.Outside.L_meta_545_aux.elim_last_false hd1 hdep hnc hcs
    have hfeq : (fun y : Fin (n + (d + 1)) → Bool => hd1 (Fin.snoc y false)) = hd := funext hsnoc_f
    rw [hfeq] at hcs1
    obtain ⟨s', hs', hcs'⟩ := ih s1 g v ⟨x0, hx0v, hx0g⟩ hcs1
    exact ⟨s', by omega, hcs'⟩
