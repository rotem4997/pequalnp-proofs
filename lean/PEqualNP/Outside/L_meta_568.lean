import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_568_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Circuit simplification adapted from L_meta_545.
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

abbrev Stat := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (s : Stat) (m : ℕ) : Prop := match s with
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
    (hc : ∃ c, Sum.inl c ∈ ins) :
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
    (hval : ∀ s ∈ ins, Stat.Valid s m) :
    let res := simplify op m ins
    Stat.Valid res.2 (match res.1 with | none => m | some _ => m + 1) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid]
    · cases a with
      | inl c => simp [simplify, simpAnd, Stat.Valid]
      | inr j => exact hval (Sum.inr j) (by simp)
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp [simplify, simpAnd, Stat.Valid]
        | inr j =>
          cases c
          · simp [simplify, simpAnd, Stat.Valid]
          · simpa [simplify, simpAnd] using hval (Sum.inr j) (by simp)
      | inr j =>
        cases b with
        | inl d =>
          cases d
          · simp [simplify, simpAnd, Stat.Valid]
          · simpa [simplify, simpAnd] using hval (Sum.inr j) (by simp)
        | inr k =>
          simpa [simplify, simpAnd, Stat.Valid] using Nat.lt_succ_self m
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid]
    · cases a with
      | inl c => simp [simplify, simpOr, Stat.Valid]
      | inr j => exact hval (Sum.inr j) (by simp)
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp [simplify, simpOr, Stat.Valid]
        | inr j =>
          cases c
          · simpa [simplify, simpOr] using hval (Sum.inr j) (by simp)
          · simp [simplify, simpOr, Stat.Valid]
      | inr j =>
        cases b with
        | inl d =>
          cases d
          · simpa [simplify, simpOr] using hval (Sum.inr j) (by simp)
          · simp [simplify, simpOr, Stat.Valid]
        | inr k =>
          simpa [simplify, simpOr, Stat.Valid] using Nat.lt_succ_self m
    · simp at hlen
  · have h1 := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [simplify, simpNot, Stat.Valid]
    · cases a with
      | inl c => simp [simplify, simpNot, Stat.Valid]
      | inr j => simpa [simplify, simpNot, Stat.Valid] using Nat.lt_succ_self m
    · simp at h1

lemma simplify_eval (op : GateOp) (w : List Bool) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hlen : ins.length ≤ 2) (hnot : op = GateOp.not → ins.length ≤ 1) :
    let res := simplify op w.length ins
    let w' := match res.1 with | none => w | some g => step w g
    Stat.val w' res.2 = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.val, GateOp.eval]
    · cases a <;> simp [simplify, simpAnd, Stat.val, GateOp.eval]
    · cases a with
      | inl c => cases b with
        | inl d => simp [simplify, simpAnd, Stat.val, GateOp.eval]
        | inr j => cases c <;> simp [simplify, simpAnd, Stat.val, GateOp.eval]
      | inr j => cases b with
        | inl d => cases d <;> simp [simplify, simpAnd, Stat.val, GateOp.eval]
        | inr k =>
          simp [simplify, simpAnd, Stat.val, step, getD_snoc_eq, GateOp.eval]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.val, GateOp.eval]
    · cases a <;> simp [simplify, simpOr, Stat.val, GateOp.eval]
    · cases a with
      | inl c => cases b with
        | inl d => simp [simplify, simpOr, Stat.val, GateOp.eval]
        | inr j => cases c <;> simp [simplify, simpOr, Stat.val, GateOp.eval]
      | inr j => cases b with
        | inl d => cases d <;> simp [simplify, simpOr, Stat.val, GateOp.eval]
        | inr k =>
          simp [simplify, simpOr, Stat.val, step, getD_snoc_eq, GateOp.eval]
    · simp at hlen
  · have h1 := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [simplify, simpNot, Stat.val, GateOp.eval]
    · cases a with
      | inl c => simp [simplify, simpNot, Stat.val, GateOp.eval]
      | inr j =>
        simp [simplify, simpNot, Stat.val, step, getD_snoc_eq, GateOp.eval]
    · simp at h1

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  let (st, gs) := acc
  let ins := g.inputs.map fun i => st.getD i (Sum.inl false)
  let (og, s) := simplify g.op (n + gs.length) ins
  let gs' := match og with | none => gs | some g' => gs ++ [g']
  (st ++ [s], gs')

def elimPass (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

lemma elimPass_main (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, NOk g) :
    ∀ (st : List Stat) (outGs : List Gate),
      (∀ s ∈ st, Stat.Valid s (n + outGs.length)) →
      (∀ g ∈ outGs, Ok g) →
      let res := elimPass n gs (st, outGs)
      (∀ s ∈ res.1, Stat.Valid s (n + res.2.length)) ∧
      (∀ g ∈ res.2, Ok g) ∧
      res.2.length ≤ outGs.length + gs.length ∧
      (∀ k < st.length, res.1.getD k (Sum.inl false) = st.getD k (Sum.inl false)) ∧
      ((∃ g ∈ gs, ∃ i ∈ g.inputs, i < st.length ∧ ∃ c, st.getD i (Sum.inl false) = Sum.inl c) →
        res.2.length + 1 ≤ outGs.length + gs.length) ∧
      (∀ (y : Fin n → Bool) (wOld : List Bool),
        wOld.length = st.length →
        (∀ i, wOld.getD i false = Stat.val (run outGs (List.ofFn y)) (st.getD i (Sum.inl false))) →
        ∀ i, (run gs wOld).getD i false =
          Stat.val (run res.2 (List.ofFn y)) (res.1.getD i (Sum.inl false))) := by
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
    set ins := g.inputs.map fun i => st.getD i (Sum.inl false)
    set res1 := simplify g.op (n + outGs.length) ins
    set outGs1 : List Gate := match res1.1 with | none => outGs | some g' => outGs ++ [g']
    set st1 : List Stat := st ++ [res1.2]
    have hins_val : ∀ s ∈ ins, Stat.Valid s (n + outGs.length) := by
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
    have hstep_valid : ∀ s ∈ st1, Stat.Valid s (n + outGs1.length) := by
      intro s hs
      simp only [st1, List.mem_append, List.mem_singleton] at hs
      rcases hs with hs | rfl
      · have hvs := hv s hs
        cases s with
        | inl _ => trivial
        | inr j =>
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
      exact getD_snoc_lt st res1.2 k hk (Sum.inl false)
    · rintro ⟨g0, hg0, i, hi, hist, c, hc⟩
      simp only [List.mem_cons] at hg0
      rcases hg0 with hg0eq | hg0
      · rw [hg0eq] at hi
        have hcin : Sum.inl c ∈ ins := List.mem_map.mpr ⟨i, hi, hc⟩
        have hnone : res1.1 = none :=
          simplify_none_of_const g.op (n + outGs.length) ins hg_nok.1.1
            (by simpa [ins] using hg_nok.1.2) (fun hn => by simpa [ins] using hg_nok.2 hn) ⟨c, hcin⟩
        have hout1_eq : outGs1 = outGs := by simp [outGs1, hnone]
        rw [hout1_eq] at hlen' ⊢
        simp; omega
      · have hdrop1 : (elimPass n gs (st1, outGs1)).2.length + 1 ≤ outGs1.length + gs.length :=
          hdrop' ⟨g0, hg0, i, hi, by simp [st1]; omega, c, by
            rw [getD_snoc_lt st res1.2 i hist (Sum.inl false)]; exact hc⟩
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
      have hres2_val : Stat.val (run outGs1 (List.ofFn y)) res1.2 =
          g.op.eval (g.inputs.map fun j => wOld.getD j false) := by
        rw [hrun1]
        have hres2 : Stat.val (match res1.1 with
            | none => run outGs (List.ofFn y)
            | some g' => step (run outGs (List.ofFn y)) g') res1.2 =
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
        have hvi : Stat.Valid (st.getD i (Sum.inl false)) (n + outGs.length) :=
          hv _ (by simp [List.getD, hlt_st])
        cases hs : st.getD i (Sum.inl false) with
        | inl c => rfl
        | inr j =>
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

lemma elimPass_append (n : ℕ) (L R : List Gate) (st : List Stat × List Gate) :
    elimPass n (L ++ R) st = elimPass n R (elimPass n L st) :=
  List.foldl_append

def gateArgs (st : List Stat × List Gate) (g : Gate) : List Stat :=
  g.inputs.map fun i => st.1.getD i (Sum.inl false)

def gateResult (n : ℕ) (st : List Stat × List Gate) (g : Gate) : Option Gate × Stat :=
  simplify g.op (n + st.2.length) (gateArgs st g)

lemma elimStep_env (n : ℕ) (st : List Stat × List Gate) (g : Gate) :
    (elimStep n st g).1 = st.1 ++ [(gateResult n st g).2] := by
  rcases st with ⟨env, out⟩
  rfl

lemma elimStep_size (n : ℕ) (st : List Stat × List Gate) (g : Gate) :
    (elimStep n st g).2.length ≤ st.2.length + 1 := by
  rcases st with ⟨env, out⟩
  simp only [elimStep]
  split <;> simp

lemma elimStep_no_gate (n : ℕ) (st : List Stat × List Gate) (g : Gate)
    (h : (gateResult n st g).1 = none) :
    (elimStep n st g).2 = st.2 := by
  rcases st with ⟨env, out⟩
  simpa [gateResult, gateArgs, elimStep] using
    (show (match (gateResult n (env, out) g).1 with
      | none => out
      | some gate => out ++ [gate]) = out by rw [h])

lemma elimPass_env (n : ℕ) (gs : List Gate) (st : List Stat × List Gate) :
    ∃ rest, (elimPass n gs st).1 = st.1 ++ rest := by
  induction gs generalizing st with
  | nil => exact ⟨[], by simp [elimPass]⟩
  | cons g gs ih =>
    obtain ⟨tail, ht⟩ := ih (elimStep n st g)
    refine ⟨(gateResult n st g).2 :: tail, ?_⟩
    change (elimPass n gs (elimStep n st g)).1 = _
    rw [ht, elimStep_env, List.append_assoc]
    rfl

lemma elimPass_get (n : ℕ) (gs : List Gate) (st : List Stat × List Gate)
    (i : ℕ) (hi : i < st.1.length) :
    (elimPass n gs st).1.getD i (Sum.inl false) = st.1.getD i (Sum.inl false) := by
  obtain ⟨tail, ht⟩ := elimPass_env n gs st
  rw [ht, List.getD_append _ _ _ _ hi]

lemma gateResult_no_gate_of_constant (n : ℕ) (st : List Stat × List Gate) (g : Gate)
    (hg : NOk g) (i : ℕ) (hi : i ∈ g.inputs) (b : Bool)
    (hc : st.1.getD i (Sum.inl false) = Sum.inl b) :
    (gateResult n st g).1 = none := by
  apply simplify_none_of_const g.op _ _ hg.1.1
  · simpa [gateArgs] using hg.1.2
  · intro h
    simpa [gateArgs] using hg.2 h
  · exact ⟨b, List.mem_map.mpr ⟨i, hi, hc⟩⟩

def stateAt (n : ℕ) (gs : List Gate) (st : List Stat × List Gate) (i : ℕ) :
    List Stat × List Gate := elimPass n (gs.take i) st

lemma stateAt_succ (n : ℕ) (gs : List Gate) (st : List Stat × List Gate)
    {i : ℕ} (hi : i < gs.length) :
    stateAt n gs st (i + 1) = elimStep n (stateAt n gs st i) gs[i] := by
  unfold stateAt
  rw [List.take_succ_eq_append_getElem hi, elimPass_append]
  rfl

lemma stateAt_size_bound (n : ℕ) (gs : List Gate) (st : List Stat × List Gate)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ gs.length) :
    (stateAt n gs st j).2.length ≤ (stateAt n gs st i).2.length + (j - i) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hj' ih =>
    have hjlt : j < gs.length := by omega
    rw [stateAt_succ n gs st hjlt]
    have hstep := elimStep_size n (stateAt n gs st j) gs[j]
    have hprev := ih (by omega)
    omega

lemma stateAt_preserves (n : ℕ) (gs : List Gate) (st : List Stat × List Gate)
    (i j w : ℕ) (hij : i ≤ j) (hj : j ≤ gs.length)
    (hw : w < (stateAt n gs st i).1.length) :
    (stateAt n gs st j).1.getD w (Sum.inl false) =
      (stateAt n gs st i).1.getD w (Sum.inl false) := by
  have hsplit : gs.take j = gs.take i ++ (gs.take j).drop i := by
    calc
      gs.take j = (gs.take j).take i ++ (gs.take j).drop i := (List.take_append_drop _ _).symm
      _ = _ := by rw [List.take_take, min_eq_left hij]
  have he : stateAt n gs st j = elimPass n ((gs.take j).drop i) (stateAt n gs st i) :=
    (congrArg (fun sub => elimPass n sub st) hsplit).trans (elimPass_append _ _ _ _)
  rw [he]
  exact elimPass_get _ _ _ _ hw

lemma stateAt_two_drops (n : ℕ) (gs : List Gate) (st : List Stat × List Gate)
    (i j : ℕ) (hij : i < j) (hj : j < gs.length)
    (hiDrop : (stateAt n gs st (i + 1)).2 = (stateAt n gs st i).2)
    (hjDrop : (stateAt n gs st (j + 1)).2 = (stateAt n gs st j).2) :
    (elimPass n gs st).2.length + 2 ≤ st.2.length + gs.length := by
  have hfirst := stateAt_size_bound n gs st 0 i (by omega) (by omega)
  have hmiddle := stateAt_size_bound n gs st (i + 1) j (by omega) (by omega)
  have hlast := stateAt_size_bound n gs st (j + 1) gs.length (by omega) le_rfl
  rw [hiDrop] at hmiddle
  rw [hjDrop] at hlast
  have hzero : stateAt n gs st 0 = st := rfl
  have hfull : stateAt n gs st gs.length = elimPass n gs st := by simp [stateAt]
  rw [hzero, Nat.sub_zero] at hfirst
  rw [hfull] at hlast
  omega

def wireEnv (k : ℕ) : List Stat := List.ofFn (fun i : Fin k => Sum.inr i.val)

lemma wireEnv_read (k i : ℕ) (hi : i < k) :
    (wireEnv k).getD i (Sum.inl false) = Sum.inr i := by
  simp [wireEnv, List.getD_eq_getElem?_getD, hi]

lemma statValid_wireEnv (k : ℕ) (u : Stat) (hu : u ∈ wireEnv k) : Stat.Valid u k := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
  exact i.isLt

lemma getD_set_same {α : Type*} (l : List α) (i : ℕ) (a d : α)
    (hi : i < l.length) : (l.set i a).getD i d = a := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma getD_set_other {α : Type*} (l : List α) (i j : ℕ) (a d : α)
    (hij : i ≠ j) : (l.set i a).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne hij]

lemma initEnv_valid (k : ℕ) (w : ℕ) (b : Bool) (u : Stat)
    (hu : u ∈ (wireEnv k).set w (Sum.inl b)) : Stat.Valid u k := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hu
  by_cases hw : w = i
  · subst w
    simp [Stat.Valid]
  · rw [List.getElem_set_ne hw]
    apply statValid_wireEnv
    exact List.getElem_mem _

lemma env_represents (wires : List Bool) (k w : ℕ) (b : Bool)
    (hk : wires.length = k) (hw : w < k) (i : ℕ) :
    (wires.set w b).getD i false =
      Stat.val wires (((wireEnv k).set w (Sum.inl b)).getD i (Sum.inl false)) := by
  by_cases hiw : i = w
  · subst i
    rw [getD_set_same _ _ _ _ (by simpa [hk] using hw),
      getD_set_same _ _ _ _ (by simpa [wireEnv] using hw)]
    rfl
  · rw [getD_set_other _ _ _ _ _ (Ne.symm hiw), getD_set_other _ _ _ _ _ (Ne.symm hiw)]
    by_cases hi : i < k
    · rw [wireEnv_read _ _ hi]
      rfl
    · rw [List.getD_eq_default _ _ (by omega),
        List.getD_eq_default _ _ (by simp [wireEnv]; omega)]
      rfl

lemma run_preserves (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega), step, getD_snoc_lt _ _ _ hi]

lemma step_at (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) :=
  getD_snoc_eq _ _ _

lemma step_off (w : List Bool) (g : Gate) (i : ℕ) (hi : i ≠ w.length) :
    (step w g).getD i false = w.getD i false := by
  by_cases hlt : i < w.length
  · exact getD_snoc_lt _ _ _ hlt _
  · rw [List.getD_eq_default _ _ (by simp [step]; omega),
      List.getD_eq_default _ _ (by omega)]

lemma run_agree (bad : ℕ → Prop) (gs : List Gate)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, ¬ bad i)
    (x y : List Bool) (hlen : x.length = y.length)
    (hag : ∀ i, ¬ bad i → x.getD i false = y.getD i false) :
    ∀ i, ¬ bad i → (run gs x).getD i false = (run gs y).getD i false := by
  induction gs generalizing x y with
  | nil => exact hag
  | cons g gs ih =>
    change ∀ i, ¬ bad i → (run gs (step x g)).getD i false = (run gs (step y g)).getD i false
    apply ih (fun d hd => hread d (List.mem_cons_of_mem _ hd)) _ _ (by simp [step, hlen])
    intro i hi
    by_cases he : i = x.length
    · subst i
      rw [step_at, hlen, step_at]
      congr 1
      exact List.map_congr_left fun j hj => hag j (hread g (by simp) j hj)
    · rw [step_off _ _ _ he, step_off _ _ _ (by omega)]
      exact hag i hi

lemma set_getD_self (w : List Bool) (v : ℕ) (hv : v < w.length) :
    w.set v (w.getD v false) = w := by
  rw [List.getD_eq_getElem _ _ hv]
  exact List.set_getElem_self hv

lemma elimPass_out (n : ℕ) (gs : List Gate) (st : List Stat × List Gate) :
    ∃ rest, (elimPass n gs st).2 = st.2 ++ rest := by
  induction gs generalizing st with
  | nil => exact ⟨[], by simp [elimPass]⟩
  | cons g gs ih =>
    obtain ⟨tail, ht⟩ := ih (elimStep n st g)
    rcases st with ⟨env, out⟩
    by_cases he : (gateResult n (env, out) g).1 = none
    · exact ⟨tail, ht.trans (congrArg (fun a => a ++ tail) (elimStep_no_gate _ _ _ he))⟩
    · cases hg : (gateResult n (env, out) g).1 with
      | none => exact False.elim (he hg)
      | some g' =>
        refine ⟨g' :: tail, ht.trans ?_⟩
        have hstep : (elimStep n (env, out) g).2 = out ++ [g'] := by
          change (match (gateResult n (env, out) g).1 with
            | none => out
            | some d => out ++ [d]) = _
          rw [hg]
        rw [hstep, List.append_assoc]
        rfl

def forceValue (C : Circuit) (m k v : ℕ) (b : Bool) (x : Fin m → Bool) : Bool :=
  (run (C.gates.drop k) ((run (C.gates.take k) (List.ofFn x)).set v b)).getD C.output false

def cutState (C : Circuit) (m k v : ℕ) : List Stat × List Gate :=
  ((wireEnv (m + k)).set v (Sum.inl false), C.gates.take k)

def compiledCut (C : Circuit) (m k v : ℕ) : List Stat × List Gate :=
  elimPass m (C.gates.drop k) (cutState C m k v)

lemma cut_prefix_length (C : Circuit) (m k : ℕ) (hk : k ≤ C.gates.length)
    (x : Fin m → Bool) :
    (run (C.gates.take k) (List.ofFn x)).length = m + k := by
  rw [run_length, List.length_ofFn, List.length_take_of_le hk]

lemma cut_actual (C : Circuit) (m k v : ℕ) (hk : k ≤ C.gates.length) (hv : v < m + k)
    (x : Fin m → Bool) :
    forceValue C m k v ((run (C.gates.take k) (List.ofFn x)).getD v false) x =
      circuitFun m C x := by
  unfold forceValue
  rw [set_getD_self _ _ (by rw [cut_prefix_length _ _ _ hk]; exact hv), ← run_append,
    List.take_append_drop]
  rfl

lemma cut_or (C : Circuit) (m k v : ℕ) (hk : k ≤ C.gates.length) (hv : v < m + k)
    (hot : ∀ x : Fin m → Bool, forceValue C m k v true x = true) (x : Fin m → Bool) :
    circuitFun m C x =
      ((run (C.gates.take k) (List.ofFn x)).getD v false || forceValue C m k v false x) := by
  have h := cut_actual C m k v hk hv x
  cases hb : (run (C.gates.take k) (List.ofFn x)).getD v false
  · rw [hb] at h
    simpa using h.symm
  · rw [hb, hot x] at h
    simpa using h.symm

lemma cut_compile (C : Circuit) (m k v : ℕ) (hk : k ≤ C.gates.length) (hv : v < m + k)
    (hlegal : ∀ g ∈ C.gates, NOk g) :
    let z := compiledCut C m k v
    (∀ g ∈ z.2, Ok g) ∧
    (∀ x : Fin m → Bool, forceValue C m k v false x =
      Stat.val (run z.2 (List.ofFn x)) (z.1.getD C.output (Sum.inl false))) ∧
    (∀ x : Fin m → Bool, (run z.2 (List.ofFn x)).getD v false =
      (run (C.gates.take k) (List.ofFn x)).getD v false) := by
  have hrest : ∀ g ∈ C.gates.drop k, NOk g := fun g hg => hlegal g ((List.drop_sublist _ _).subset hg)
  have hpre : ∀ g ∈ C.gates.take k, Ok g := fun g hg => (hlegal g ((List.take_sublist _ _).subset hg)).1
  have henv : ∀ s ∈ (wireEnv (m + k)).set v (Sum.inl false), Stat.Valid s (m + (C.gates.take k).length) := by
    rw [List.length_take_of_le hk]
    exact initEnv_valid _ _ _
  obtain ⟨_, hok, _, _, _, hsem⟩ := elimPass_main m (C.gates.drop k) hrest _ _ henv hpre
  refine ⟨hok, ?_, ?_⟩
  · intro x
    apply hsem x ((run (C.gates.take k) (List.ofFn x)).set v false)
    · simp [cut_prefix_length _ _ _ hk, wireEnv]
    · exact env_represents _ _ _ _ (cut_prefix_length _ _ _ hk _) hv
  · intro x
    obtain ⟨tail, ht⟩ := elimPass_out m (C.gates.drop k) (cutState C m k v)
    change (run (compiledCut C m k v).2 (List.ofFn x)).getD v false = _
    rw [show (compiledCut C m k v).2 = C.gates.take k ++ tail from ht, run_append]
    apply run_preserves
    rwa [cut_prefix_length _ _ _ hk]

def attachOr (m v : ℕ) (gs : List Gate) (s : Stat) : Circuit :=
  match s with
  | Sum.inl false => ⟨gs, v⟩
  | Sum.inl true => ⟨gs ++ [⟨GateOp.and, []⟩], m + gs.length⟩
  | Sum.inr w => ⟨gs ++ [⟨GateOp.or, [v, w]⟩], m + gs.length⟩

lemma attachOr_spec (m v : ℕ) (gs : List Gate) (s : Stat) (hg : ∀ g ∈ gs, Ok g) :
    FanInTwo (attachOr m v gs s) ∧ (attachOr m v gs s).size ≤ gs.length + 1 ∧
    ∀ x : Fin m → Bool, circuitFun m (attachOr m v gs s) x =
      ((run gs (List.ofFn x)).getD v false || Stat.val (run gs (List.ofFn x)) s) := by
  have appendOk (g : Gate) (h : Ok g) :
      FanInTwo ⟨gs ++ [g], m + gs.length⟩ := by
    intro g' h'
    rcases List.mem_append.mp h' with hm | hm
    · exact hg g' hm
    · simp only [List.mem_singleton] at hm
      subst g'
      exact h
  have output (g : Gate) (x : Fin m → Bool) :
      circuitFun m ⟨gs ++ [g], m + gs.length⟩ x =
        g.op.eval (g.inputs.map fun i => (run gs (List.ofFn x)).getD i false) := by
    change (run (gs ++ [g]) (List.ofFn x)).getD (m + gs.length) false = _
    have hl : (run gs (List.ofFn x)).length = m + gs.length := by simp [run_length]
    rw [run_append, ← hl]
    exact step_at _ _
  cases s with
  | inl b =>
    cases b
    · refine ⟨hg, by simp [attachOr, Circuit.size], ?_⟩
      intro x
      change (run gs (List.ofFn x)).getD v false = (_ || false)
      simp
    · refine ⟨appendOk _ ⟨by simp, by simp⟩, by simp [attachOr, Circuit.size], ?_⟩
      intro x
      rw [attachOr, output]
      simp [GateOp.eval, Stat.val]
  | inr w =>
    refine ⟨appendOk _ ⟨by simp, by simp⟩, by simp [attachOr, Circuit.size], ?_⟩
    intro x
    rw [attachOr, output]
    simp [GateOp.eval, Stat.val]

lemma too_many_drops (C : Circuit) (m k v : ℕ) (hk : k ≤ C.gates.length)
    (hv : v < m + k) (hlegal : ∀ g ∈ C.gates, NOk g) (hmin : IsMinimalCircuit m C)
    (hot : ∀ x : Fin m → Bool, forceValue C m k v true x = true)
    (saved : (compiledCut C m k v).2.length + 2 ≤ C.gates.length) : False := by
  obtain ⟨hok, hsem, hprefix⟩ := cut_compile C m k v hk hv hlegal
  let z := compiledCut C m k v
  let D := attachOr m v z.2 (z.1.getD C.output (Sum.inl false))
  obtain ⟨hfan, hsize, hfun⟩ := attachOr_spec m v z.2 (z.1.getD C.output (Sum.inl false)) hok
  have heq : circuitFun m D = circuitFun m C := by
    funext x
    change circuitFun m (attachOr m v z.2 (z.1.getD C.output (Sum.inl false))) x = _
    rw [hfun x, hprefix x, ← hsem x, cut_or C m k v hk hv hot x]
  have hle := hmin.2 D hfan heq
  change C.gates.length ≤ D.size at hle
  change D.size ≤ (compiledCut C m k v).2.length + 1 at hsize
  omega

lemma wireEnv_represents (wires : List Bool) (k : ℕ) (hk : wires.length = k) (i : ℕ) :
    wires.getD i false = Stat.val wires ((wireEnv k).getD i (Sum.inl false)) := by
  by_cases hi : i < k
  · rw [wireEnv_read _ _ hi]
    rfl
  · rw [List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by simp [wireEnv]; omega)]
    rfl

lemma minimal_keeps_gate (C : Circuit) (m j : ℕ) (hj : j < C.gates.length)
    (hlegal : ∀ g ∈ C.gates, NOk g) (hmin : IsMinimalCircuit m C)
    (hvar : ∃ x y : Fin m → Bool, circuitFun m C x ≠ circuitFun m C y) :
    (gateResult m (wireEnv (m + j), C.gates.take j) C.gates[j]).1 ≠ none := by
  intro hd
  let rest := C.gates.drop j
  let pre := C.gates.take j
  let st := (wireEnv (m + j), pre)
  let z := elimPass m rest st
  have hrest : ∀ g ∈ rest, NOk g := fun g hg => hlegal g ((List.drop_sublist _ _).subset hg)
  have hpre : ∀ g ∈ pre, Ok g := fun g hg => (hlegal g ((List.take_sublist _ _).subset hg)).1
  have hprelen : pre.length = j := List.length_take_of_le (by omega)
  have hv : ∀ s ∈ st.1, Stat.Valid s (m + pre.length) := by
    rw [hprelen]
    exact statValid_wireEnv _
  obtain ⟨_, hok, _, _, _, hsem⟩ := elimPass_main m rest hrest st.1 pre hv hpre
  have hfun (x : Fin m → Bool) :
      circuitFun m C x = Stat.val (run z.2 (List.ofFn x)) (z.1.getD C.output (Sum.inl false)) := by
    change (run C.gates (List.ofFn x)).getD C.output false = _
    conv_lhs => rw [← List.take_append_drop j C.gates, run_append]
    apply hsem x (run pre (List.ofFn x))
    · simp [st, wireEnv, pre, cut_prefix_length _ _ _ (by omega : j ≤ C.gates.length)]
    · exact wireEnv_represents _ _ (cut_prefix_length C m j (by omega) x)
  have hlen : rest.length = C.gates.length - j := List.length_drop
  have hlt : 0 < rest.length := by omega
  have hr : rest[0] = C.gates[j] := by simp [rest]
  have hst0 : stateAt m rest st 0 = st := rfl
  have hst1 : (stateAt m rest st 1).2 = pre := by
    rw [stateAt_succ m rest st hlt, hr, hst0]
    exact elimStep_no_gate _ _ _ hd
  have hsize := stateAt_size_bound m rest st 1 rest.length (by omega) le_rfl
  have hz : stateAt m rest st rest.length = z := by simp [stateAt, z]
  rw [hz, hst1, hprelen, hlen] at hsize
  cases he : z.1.getD C.output (Sum.inl false) with
  | inl b =>
    obtain ⟨x, y, hxy⟩ := hvar
    apply hxy
    rw [hfun x, hfun y, he]
    rfl
  | inr w =>
    let D : Circuit := ⟨z.2, w⟩
    have hEq : circuitFun m D = circuitFun m C := by
      funext x
      rw [hfun x, he]
      rfl
    have hl := hmin.2 D hok hEq
    change C.gates.length ≤ z.2.length at hl
    omega

lemma minimal_inputs_before (C : Circuit) (m j : ℕ) (hj : j < C.gates.length)
    (hlegal : ∀ g ∈ C.gates, NOk g) (hmin : IsMinimalCircuit m C)
    (hvar : ∃ x y : Fin m → Bool, circuitFun m C x ≠ circuitFun m C y) :
    ∀ w ∈ (C.gates[j]).inputs, w < m + j := by
  intro w hw
  by_contra hn
  apply minimal_keeps_gate C m j hj hlegal hmin hvar
  have hg := hlegal C.gates[j] (List.getElem_mem _)
  apply gateResult_no_gate_of_constant _ _ _ hg w hw false
  exact List.getD_eq_default _ _ (by simp [wireEnv]; omega)

lemma minimal_or_binary (C : Circuit) (m j : ℕ) (hj : j < C.gates.length)
    (hlegal : ∀ g ∈ C.gates, NOk g) (hmin : IsMinimalCircuit m C)
    (hvar : ∃ x y : Fin m → Bool, circuitFun m C x ≠ circuitFun m C y)
    (hor : (C.gates[j]).op = GateOp.or) :
    (C.gates[j]).inputs.length = 2 := by
  have hg := (hlegal C.gates[j] (List.getElem_mem _)).1.2
  by_contra hn
  apply minimal_keeps_gate C m j hj hlegal hmin hvar
  rcases he : (C.gates[j]).inputs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp [gateResult, gateArgs, hor, he, simplify, simpOr]
  · simp only [gateResult, gateArgs, hor, he, simplify, List.map_cons, List.map_nil]
    cases (wireEnv (m + j)).getD a (Sum.inl false) <;> rfl
  · simp only [he, List.length_cons] at hg hn
    omega

lemma drop_split (gs : List Gate) (k j : ℕ) (hk : k ≤ j) (hj : j < gs.length) :
    gs.drop k = (gs.drop k).take (j - k) ++ gs[j] :: gs.drop (j + 1) := by
  calc
    gs.drop k = (gs.drop k).take (j - k) ++ (gs.drop k).drop (j - k) :=
      (List.take_append_drop _ _).symm
    _ = _ := by
      rw [List.drop_drop, show k + (j - k) = j by omega, List.drop_eq_getElem_cons hj]

lemma take_split (gs : List Gate) (k j : ℕ) (hk : k ≤ j) (hj : j < gs.length) :
    gs.take (j + 1) = (gs.take k ++ (gs.drop k).take (j - k)) ++ [gs[j]] := by
  rw [List.take_succ_eq_append_getElem hj]
  have hs := (List.take_append_drop k (gs.take j)).symm
  rw [List.take_take, min_eq_left hk, List.drop_take] at hs
  rw [hs]

def Reads (C : Circuit) (v : ℕ) (j : Fin C.gates.length) : Prop :=
  v ∈ (C.gates.get j).inputs

lemma readers_avoid_middle (C : Circuit) (k v : ℕ) (j : Fin C.gates.length)
    (hk : k ≤ j.val) (hu : ∀ r, Reads C v r → r = j) :
    ∀ g ∈ (C.gates.drop k).take (j.val - k), v ∉ g.inputs := by
  intro g hg hv
  obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hg
  have hr' : r < j.val - k := lt_of_lt_of_le hr (List.length_take_le _ _)
  have hlt : k + r < C.gates.length := by omega
  have hRead : Reads C v ⟨k + r, hlt⟩ := by simpa [Reads] using hv
  have he := congrArg Fin.val (hu _ hRead)
  change k + r = j.val at he
  omega

lemma readers_avoid_tail (C : Circuit) (v : ℕ) (j : Fin C.gates.length)
    (hu : ∀ r, Reads C v r → r = j) :
    ∀ g ∈ C.gates.drop (j.val + 1), v ∉ g.inputs := by
  intro g hg hv
  obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hg
  have hlt : j.val + 1 + r < C.gates.length := by
    simp only [List.length_drop] at hr
    omega
  have hRead : Reads C v ⟨j.val + 1 + r, hlt⟩ := by simpa [Reads] using hv
  have he := congrArg Fin.val (hu _ hRead)
  change j.val + 1 + r = j.val at he
  omega

def beforeReader (C : Circuit) (m k : ℕ) (j : Fin C.gates.length) (x : Fin m → Bool) : List Bool :=
  run ((C.gates.drop k).take (j.val - k)) (run (C.gates.take k) (List.ofFn x))

def forcedBeforeReader (C : Circuit) (m k v : ℕ) (j : Fin C.gates.length)
    (x : Fin m → Bool) : List Bool :=
  run ((C.gates.drop k).take (j.val - k)) ((run (C.gates.take k) (List.ofFn x)).set v true)

lemma beforeReader_cut (C : Circuit) (m k v : ℕ) (j : Fin C.gates.length)
    (hk : k ≤ j.val) (hv : v < m + k) (hu : ∀ r, Reads C v r → r = j)
    (x : Fin m → Bool) :
    let w := beforeReader C m k j x
    let u := forcedBeforeReader C m k v j x
    w.length = m + j.val ∧ u.length = w.length ∧
    u.getD v false = true ∧ (∀ i, i ≠ v → u.getD i false = w.getD i false) := by
  let B := (C.gates.drop k).take (j.val - k)
  let pre := run (C.gates.take k) (List.ofFn x)
  have hpre : pre.length = m + k := cut_prefix_length C m k (by omega) x
  have hB : B.length = j.val - k := by
    unfold B
    apply List.length_take_of_le
    simp only [List.length_drop]
    omega
  have hvpre : v < pre.length := hpre ▸ hv
  change (run B pre).length = _ ∧ (run B (pre.set v true)).length = (run B pre).length ∧ _ ∧ _
  refine ⟨by rw [run_length, hpre, hB]; omega, by simp [run_length], ?_, ?_⟩
  · change (run B (pre.set v true)).getD v false = true
    rw [run_preserves _ _ _ (by simpa using hvpre)]
    exact getD_set_same _ _ _ _ hvpre
  · refine run_agree (fun i => i = v) B ?_ (pre.set v true) pre (by simp) ?_
    · intro g hg i hi h
      subst i
      exact readers_avoid_middle C k v j hk hu g hg hi
    · intro i hi
      exact getD_set_other _ _ _ _ _ (Ne.symm hi)

lemma force_read_split (C : Circuit) (m k v : ℕ) (j : Fin C.gates.length)
    (hk : k ≤ j.val) (x : Fin m → Bool) :
    forceValue C m k v true x =
      (run (C.gates.drop (j.val + 1))
        (step (forcedBeforeReader C m k v j x) (C.gates.get j))).getD C.output false := by
  unfold forceValue forcedBeforeReader
  conv_lhs => rw [drop_split C.gates k j.val hk j.isLt, run_append]
  rfl

lemma actual_read_split (C : Circuit) (m k : ℕ) (j : Fin C.gates.length)
    (hk : k ≤ j.val) (x : Fin m → Bool) :
    circuitFun m C x = (run (C.gates.drop (j.val + 1))
      (step (beforeReader C m k j x) (C.gates.get j))).getD C.output false := by
  change (run C.gates (List.ofFn x)).getD C.output false = _
  conv_lhs => rw [← List.take_append_drop k C.gates, run_append,
    drop_split C.gates k j.val hk j.isLt, run_append]
  rfl

lemma prefix_read_split (C : Circuit) (m k : ℕ) (j : Fin C.gates.length)
    (hk : k ≤ j.val) (x : Fin m → Bool) :
    run (C.gates.take (j.val + 1)) (List.ofFn x) =
      step (beforeReader C m k j x) (C.gates.get j) := by
  rw [take_split C.gates k j.val hk j.isLt, run_append, run_append]
  rfl

lemma force_advance (C : Circuit) (m k v : ℕ) (j : Fin C.gates.length)
    (hk : k ≤ j.val) (hv : v < m + k) (hout : C.output ≠ v)
    (hread : Reads C v j) (hu : ∀ r, Reads C v r → r = j)
    (hor : (C.gates.get j).op = GateOp.or) (x : Fin m → Bool) :
    forceValue C m k v true x = forceValue C m (j.val + 1) (m + j.val) true x := by
  rw [force_read_split C m k v j hk]
  unfold forceValue
  rw [prefix_read_split C m k j hk]
  let w := beforeReader C m k j x
  let u := forcedBeforeReader C m k v j x
  let g := C.gates.get j
  obtain ⟨hwl, hul, hhot, hag⟩ := beforeReader_cut C m k v j hk hv hu x
  change w.length = m + j.val at hwl
  change u.length = w.length at hul
  change u.getD v false = true at hhot
  have halt : (step u g).getD (m + j.val) false = true := by
    rw [← hwl, ← hul, step_at]
    change (C.gates.get j).op.eval _ = true
    rw [hor]
    exact List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨v, hread, hhot⟩, rfl⟩
  apply run_agree (fun i => i = v) _ _ (step u g)
    ((step w g).set (m + j.val) true) (by simp [step, hul]) _ C.output hout
  · intro d hd i hi he
    subst i
    exact readers_avoid_tail C v j hu d hd hi
  · intro i hi
    by_cases he : i = m + j.val
    · subst i
      rw [halt, getD_set_same _ _ _ _ (by simp [step, hwl])]
    · rw [getD_set_other _ _ _ _ _ (Ne.symm he), step_off _ _ _ (by omega), step_off _ _ _ (by omega)]
      exact hag i hi

lemma force_irrelevant_of_dead_reader (C : Circuit) (m k v : ℕ) (j : Fin C.gates.length)
    (hk : k ≤ j.val) (hv : v < m + k) (hout : C.output ≠ v)
    (hu : ∀ r, Reads C v r → r = j) (hdead : ∀ r, ¬ Reads C (m + j.val) r)
    (houtJ : C.output ≠ m + j.val) (x : Fin m → Bool) :
    forceValue C m k v true x = circuitFun m C x := by
  rw [force_read_split C m k v j hk, actual_read_split C m k j hk]
  let w := beforeReader C m k j x
  let u := forcedBeforeReader C m k v j x
  let g := C.gates.get j
  obtain ⟨hwl, hul, _, hag⟩ := beforeReader_cut C m k v j hk hv hu x
  change w.length = m + j.val at hwl
  change u.length = w.length at hul
  apply run_agree (fun i => i = v ∨ i = m + j.val) _ _ (step u g) (step w g)
    (by simp [step, hul]) _ C.output (fun h => h.elim hout houtJ)
  · intro d hd i hi h
    rcases h with h | h
    · rw [h] at hi
      exact readers_avoid_tail C v j hu d hd hi
    · rw [h] at hi
      obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hd
      have hlt : j.val + 1 + r < C.gates.length := by
        simp only [List.length_drop] at hr
        omega
      apply hdead ⟨j.val + 1 + r, hlt⟩
      simpa [Reads] using hi
  · intro i hi
    rw [step_off _ _ _ (by intro h; apply hi; right; omega),
      step_off _ _ _ (by intro h; apply hi; right; omega)]
    exact hag i (fun he => hi (Or.inl he))

lemma force_irrelevant_without_reader (C : Circuit) (m k v : ℕ)
    (hn : ∀ j, ¬ Reads C v j) (ho : C.output ≠ v) (x : Fin m → Bool) :
    forceValue C m k v true x = circuitFun m C x := by
  change (run (C.gates.drop k) ((run (C.gates.take k) (List.ofFn x)).set v true)).getD C.output false =
    (run C.gates (List.ofFn x)).getD C.output false
  conv_rhs => rw [← List.take_append_drop k C.gates, run_append]
  apply run_agree (fun i => i = v) _ _ _ _ (by simp) _ C.output ho
  · intro d hd i hi h
    subst i
    obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hd
    have hlt : k + r < C.gates.length := by
      simp only [List.length_drop] at hr
      omega
    apply hn ⟨k + r, hlt⟩
    simpa [Reads] using hi
  · intro i hi
    exact getD_set_other _ _ _ _ _ (Ne.symm hi)

lemma stateAt_env_length (n : ℕ) (gs : List Gate) (st : List Stat × List Gate)
    (i : ℕ) (hi : i ≤ gs.length) :
    (stateAt n gs st i).1.length = st.1.length + i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [stateAt_succ n gs st (by omega : i < gs.length), elimStep_env, List.length_append,
      List.length_singleton, ih (by omega)]
    omega

def atReader (C : Circuit) (m k v : ℕ) (j : Fin C.gates.length) : List Stat × List Gate :=
  stateAt m (C.gates.drop k) (cutState C m k v) (j.val - k)

lemma reader_index (C : Circuit) (k : ℕ) (j : Fin C.gates.length) (hk : k ≤ j.val) :
    j.val - k < (C.gates.drop k).length := by
  simp only [List.length_drop]
  omega

lemma reader_gate_eq (C : Circuit) (k : ℕ) (j : Fin C.gates.length) (hk : k ≤ j.val) :
    (C.gates.drop k)[j.val - k]'(reader_index C k j hk) = C.gates.get j := by
  simp [show k + (j.val - k) = j.val by omega]

lemma atReader_constant (C : Circuit) (m k v : ℕ) (j : Fin C.gates.length)
    (hk : k ≤ j.val) (hv : v < m + k) :
    (atReader C m k v j).1.getD v (Sum.inl false) = Sum.inl false := by
  let st := cutState C m k v
  have hl : v < st.1.length := by simpa [st, cutState, wireEnv] using hv
  have h := stateAt_preserves m (C.gates.drop k) st 0 (j.val - k) v (by omega)
    (Nat.le_of_lt (reader_index C k j hk)) hl
  change (stateAt m (C.gates.drop k) st (j.val - k)).1.getD v (Sum.inl false) = _
  rw [h]
  exact getD_set_same _ _ _ _ (by simpa [wireEnv] using hv)

lemma reader_drop (C : Circuit) (m k v : ℕ) (j : Fin C.gates.length)
    (hk : k ≤ j.val) (hg : NOk (C.gates.get j)) (w : ℕ) (hr : Reads C w j)
    (b : Bool) (hc : (atReader C m k v j).1.getD w (Sum.inl false) = Sum.inl b) :
    (stateAt m (C.gates.drop k) (cutState C m k v) (j.val - k + 1)).2 =
      (atReader C m k v j).2 := by
  rw [stateAt_succ m _ _ (reader_index C k j hk), reader_gate_eq C k j hk]
  exact elimStep_no_gate _ _ _ (gateResult_no_gate_of_constant _ _ _ hg w hr b hc)

lemma both_readers_save (C : Circuit) (m k v : ℕ) (j t : Fin C.gates.length)
    (hkj : k ≤ j.val) (hjt : j < t) (hlegal : ∀ g ∈ C.gates, NOk g)
    (hj : Reads C v j) (hv : v < m + k)
    (w : ℕ) (ht : Reads C w t) (b : Bool)
    (hconst : (atReader C m k v t).1.getD w (Sum.inl false) = Sum.inl b) :
    (compiledCut C m k v).2.length + 2 ≤ C.gates.length := by
  have hkt : k ≤ t.val := by omega
  have hdrop := stateAt_two_drops m (C.gates.drop k) (cutState C m k v)
    (j.val - k) (t.val - k) (by omega) (reader_index C k t hkt)
    (reader_drop C m k v j hkj (hlegal _ (List.get_mem _ _)) v hj false
      (atReader_constant C m k v j hkj hv))
    (reader_drop C m k v t hkt (hlegal _ (List.get_mem _ _)) w ht b hconst)
  change (compiledCut C m k v).2.length + 2 ≤ _ at hdrop
  simpa [cutState, List.length_take_of_le (by omega : k ≤ C.gates.length),
    List.length_drop, Nat.add_sub_of_le (by omega : k ≤ C.gates.length)] using hdrop

lemma otherGateConstant (n : ℕ) (st : List Stat × List Gate) (g : Gate)
    (hg : NOk g) (v : ℕ) (hread : v ∈ g.inputs)
    (hc : st.1.getD v (Sum.inl false) = Sum.inl false)
    (hbad : g.op ≠ GateOp.or ∨ g.inputs = [v, v]) :
    ∃ b, (gateResult n st g).2 = Sum.inl b := by
  have hop := hg.1.1
  change g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not at hop
  rcases hop with hop | hop | hop
  · rcases he : g.inputs with _ | ⟨a, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩
    · simp [he] at hread
    · have h : v = a := by simpa [he] using hread
      subst a
      exact ⟨false, by simp only [gateResult, gateArgs, hop, he, List.map_cons, List.map_nil, hc, simplify, simpAnd]⟩
    · have hm : v = a ∨ v = d := by simpa [he] using hread
      rcases hm with h | h
      · subst a
        refine ⟨false, ?_⟩
        simp only [gateResult, gateArgs, hop, he, List.map_cons, List.map_nil, hc, simplify]
        cases st.1.getD d (Sum.inl false) <;> rfl
      · subst d
        refine ⟨false, ?_⟩
        simp only [gateResult, gateArgs, hop, he, List.map_cons, List.map_nil, hc, simplify]
        cases st.1.getD a (Sum.inl false) with
        | inl b => cases b <;> rfl
        | inr _ => rfl
    · have hh := hg.1.2
      simp only [he, List.length_cons] at hh
      omega
  · have he := hbad.resolve_left (fun hn => hn hop)
    exact ⟨false, by simp only [gateResult, gateArgs, hop, he, List.map_cons, List.map_nil, hc, simplify, simpOr, Bool.false_or]⟩
  · have hs := hg.2 hop
    rcases he : g.inputs with _ | ⟨a, _ | ⟨d, rest⟩⟩
    · simp [he] at hread
    · have h : v = a := by simpa [he] using hread
      subst a
      exact ⟨true, by simp only [gateResult, gateArgs, hop, he, List.map_cons, List.map_nil, hc, simplify, simpNot, Bool.not_false]⟩
    · simp only [he, List.length_cons] at hs
      omega

lemma cut_remembers_result (C : Circuit) (m k v : ℕ) (j : Fin C.gates.length)
    (hkj : k ≤ j.val) (b : Bool)
    (he : (gateResult m (atReader C m k v j) (C.gates.get j)).2 = Sum.inl b) :
    let p := j.val - k + 1
    let st := cutState C m k v
    let gs := C.gates.drop k
    (∀ t, p ≤ t → t ≤ gs.length →
      (stateAt m gs st t).1.getD (m + j.val) (Sum.inl false) = Sum.inl b) := by
  intro p st gs t hpt htl
  have hj := reader_index C k j hkj
  have hz : st.1.length = m + k := by simp [st, cutState, wireEnv]
  have hlen := stateAt_env_length m gs st (j.val - k) (Nat.le_of_lt hj)
  have hidx : (stateAt m gs st (j.val - k)).1.length = m + j.val := by
    rw [hlen, hz]
    omega
  have hp : (stateAt m gs st p).1.getD (m + j.val) (Sum.inl false) = Sum.inl b := by
    change (stateAt m gs st (j.val - k + 1)).1.getD (m + j.val) (Sum.inl false) = _
    rw [stateAt_succ m _ _ hj, elimStep_env, reader_gate_eq C k j hkj, ← hidx, getD_snoc_eq]
    exact he
  have hpos : m + j.val < (stateAt m gs st p).1.length := by
    rw [stateAt_env_length m gs st p (by omega), hz]
    dsimp [p]
    omega
  rw [stateAt_preserves m gs st p t _ hpt htl hpos]
  exact hp

lemma constant_output_at_cut (C : Circuit) (m k v : ℕ)
    (hlegal : ∀ g ∈ C.gates, NOk g) (hmin : IsMinimalCircuit m C)
    (hk : k < C.gates.length) (hv : v < m + k)
    (hot : ∀ x : Fin m → Bool, forceValue C m k v true x = true)
    (hfalse : ∃ x : Fin m → Bool, circuitFun m C x = false) (b : Bool)
    (hconst : (compiledCut C m k v).1.getD C.output (Sum.inl false) = Sum.inl b) : False := by
  have hn : ∀ x : Fin m → Bool, forceValue C m k v false x = b := by
    obtain ⟨_, hsem, _⟩ := cut_compile C m k v (by omega) hv hlegal
    intro x
    rw [hsem x, hconst]
    rfl
  cases b
  · let D : Circuit := ⟨C.gates.take k, v⟩
    have hd : FanInTwo D := fun g hg => (hlegal g ((List.take_sublist _ _).subset hg)).1
    have he : circuitFun m D = circuitFun m C := by
      funext x
      rw [cut_or C m k v (by omega) hv hot x, hn x, Bool.or_false]
      rfl
    have hle := hmin.2 D hd he
    change C.gates.length ≤ (C.gates.take k).length at hle
    rw [List.length_take_of_le (by omega)] at hle
    omega
  · obtain ⟨x, hx⟩ := hfalse
    rw [cut_or C m k v (by omega) hv hot x, hn x, Bool.or_true] at hx
    contradiction

def OrLink (C : Circuit) (m v : ℕ) (j : Fin C.gates.length) : Prop :=
  (C.gates.get j).op = GateOp.or ∧ (C.gates.get j).inputs.length = 2 ∧
    Reads C v j ∧ (∀ r, Reads C v r → r = j) ∧
    ∃ w ∈ (C.gates.get j).inputs, w ≠ v ∧ w < m + j.val

lemma next_or (C : Circuit) (m k v : ℕ) (hboundary : v + 1 = m + k)
    (hlegal : ∀ g ∈ C.gates, NOk g) (hmin : IsMinimalCircuit m C)
    (hvar : ∃ x y : Fin m → Bool, circuitFun m C x ≠ circuitFun m C y)
    (hfalse : ∃ x : Fin m → Bool, circuitFun m C x = false)
    (hout : C.output ≠ v) (hot : ∀ x : Fin m → Bool, forceValue C m k v true x = true) :
    ∃ j : Fin C.gates.length, k ≤ j.val ∧ OrLink C m v j := by
  have hv : v < m + k := by omega
  have hpos (r : Fin C.gates.length) (hr : Reads C v r) : k ≤ r.val := by
    have hi := minimal_inputs_before C m r.val r.isLt hlegal hmin hvar v hr
    omega
  have hex : ∃ j, Reads C v j := by
    by_contra! hn
    obtain ⟨x, hx⟩ := hfalse
    have he := force_irrelevant_without_reader C m k v hn hout x
    rw [hot x, hx] at he
    contradiction
  obtain ⟨j, hj⟩ := hex
  have hkj := hpos j hj
  have huniq (r : Fin C.gates.length) (hr : Reads C v r) : r = j := by
    by_contra hne
    have hkr := hpos r hr
    apply too_many_drops C m k v (by omega) hv hlegal hmin hot
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact both_readers_save C m k v r j hkr hlt hlegal hr hv v hj false
        (atReader_constant C m k v j hkj hv)
    · exact both_readers_save C m k v j r hkj hgt hlegal hj hv v hr false
        (atReader_constant C m k v r hkr hv)
  have hproper : ¬ ((C.gates.get j).op ≠ GateOp.or ∨ (C.gates.get j).inputs = [v, v]) := by
    intro hbad
    obtain ⟨b, he⟩ := otherGateConstant m (atReader C m k v j) (C.gates.get j)
      (hlegal _ (List.get_mem _ _)) v hj (atReader_constant C m k v j hkj hv) hbad
    have hrm := cut_remembers_result C m k v j hkj b he
    by_cases hoj : C.output = m + j.val
    · apply constant_output_at_cut C m k v hlegal hmin (by omega) hv hot hfalse b
      rw [hoj]
      have hend : j.val - k + 1 ≤ (C.gates.drop k).length := by
        have h := reader_index C k j hkj
        omega
      simpa only [stateAt, List.take_length, compiledCut] using hrm _ hend le_rfl
    · have hnext : ∃ t, Reads C (m + j.val) t := by
        by_contra! hdead
        obtain ⟨x, hx⟩ := hfalse
        have he := force_irrelevant_of_dead_reader C m k v j hkj hv hout huniq hdead hoj x
        rw [hot x, hx] at he
        contradiction
      obtain ⟨t, ht⟩ := hnext
      have hjt : j < t := by
        have hlt := minimal_inputs_before C m t.val t.isLt hlegal hmin hvar (m + j.val) ht
        change j.val < t.val
        omega
      have hkt : k ≤ t.val := by omega
      have hti := reader_index C k t hkt
      have hc := hrm (t.val - k) (by omega) (by omega)
      exact too_many_drops C m k v (by omega) hv hlegal hmin hot
        (both_readers_save C m k v j t hkj hjt hlegal hj hv (m + j.val) ht b hc)
  have hor : (C.gates.get j).op = GateOp.or := by
    by_contra hn
    exact hproper (Or.inl hn)
  have hlen := minimal_or_binary C m j.val j.isLt hlegal hmin hvar hor
  change (C.gates.get j).inputs.length = 2 at hlen
  refine ⟨j, hkj, hor, hlen, hj, huniq, ?_⟩
  rcases he : (C.gates.get j).inputs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · rw [he] at hlen
    simp at hlen
  · rw [he] at hlen
    simp at hlen
  · have hnil : rest = [] := by
      apply List.length_eq_zero_iff.mp
      rw [he] at hlen
      simp only [List.length_cons] at hlen
      omega
    subst rest
    have hm : v = a ∨ v = b := by
      change v ∈ (C.gates.get j).inputs at hj
      rw [he] at hj
      simpa using hj
    rcases hm with ha | hb
    · refine ⟨b, by simp, ?_, ?_⟩
      · intro hb
        exact hproper (Or.inr (by simpa [ha, hb] using he))
      · have hm : b ∈ (C.gates.get j).inputs := by rw [he]; simp
        exact minimal_inputs_before C m j.val j.isLt hlegal hmin hvar b hm
    · refine ⟨a, by simp, ?_, ?_⟩
      · intro ha
        exact hproper (Or.inr (by simpa [ha, hb] using he))
      · have hm : a ∈ (C.gates.get j).inputs := by rw [he]; simp
        exact minimal_inputs_before C m j.val j.isLt hlegal hmin hvar a hm

def HasWireChain (C : Circuit) (m v : ℕ) : Prop :=
  ∃ (l : ℕ) (f : Fin (l + 1) → ℕ), f 0 = v ∧ f (Fin.last l) = C.output ∧
    ∀ i : Fin l, ∃ j : Fin C.gates.length,
      f i.succ = m + j.val ∧ OrLink C m (f i.castSucc) j ∧ f i.castSucc < f i.succ

lemma cut_chain (C : Circuit) (m : ℕ)
    (hlegal : ∀ g ∈ C.gates, NOk g) (hmin : IsMinimalCircuit m C)
    (hvar : ∃ x y : Fin m → Bool, circuitFun m C x ≠ circuitFun m C y)
    (hfalse : ∃ x : Fin m → Bool, circuitFun m C x = false)
    (k v : ℕ) (hboundary : v + 1 = m + k) (hk : k ≤ C.gates.length)
    (hot : ∀ x : Fin m → Bool, forceValue C m k v true x = true) :
    HasWireChain C m v := by
  by_cases hout : C.output = v
  · exact ⟨0, fun _ => v, rfl, hout.symm, fun i => Fin.elim0 i⟩
  obtain ⟨j, hjk, hj⟩ := next_or C m k v hboundary hlegal hmin hvar hfalse hout hot
  have hnow : v < m + j.val := by omega
  have hhot' (x : Fin m → Bool) : forceValue C m (j.val + 1) (m + j.val) true x = true :=
    (force_advance C m k v j hjk (by omega) hout hj.2.2.1 hj.2.2.2.1 hj.1 x).symm.trans (hot x)
  obtain ⟨l, f, hstart, hend, hf⟩ :=
    cut_chain C m hlegal hmin hvar hfalse (j.val + 1) (m + j.val) (by omega) (by omega) hhot'
  refine ⟨l + 1, Fin.cons v f, by simp, by simpa [← Fin.succ_last] using hend, ?_⟩
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · refine ⟨j, ?_, ?_, ?_⟩
    · simpa using hstart
    · simpa using hj
    · simpa [hstart] using hnow
  · obtain ⟨r, hr, hor, hlt⟩ := hf a
    exact ⟨r, by simpa using hr, by simpa using hor, by simpa using hlt⟩
termination_by C.gates.length - k
decreasing_by omega

lemma ofFn_set_last (n : ℕ) (x : Fin (n + 1) → Bool) (b : Bool) :
    (List.ofFn x).set n b = List.ofFn (Fin.snoc (fun i : Fin n => x i.castSucc) b) := by
  apply List.ext_getElem (by simp)
  intro i hi₁ hi₂
  have hi : i < n + 1 := by simpa using hi₁
  by_cases he : i = n
  · subst i
    rw [List.getElem_set_self, List.getElem_ofFn]
    change b = (Fin.snoc (fun i : Fin n => x i.castSucc) b : Fin (n + 1) → Bool) (Fin.last n)
    rw [Fin.snoc_last]
  · rw [List.getElem_set_ne (Ne.symm he)]
    simp only [List.getElem_ofFn]
    have hlt : i < n := by omega
    change x (⟨i, hlt⟩ : Fin n).castSucc =
      (Fin.snoc (fun p : Fin n => x p.castSucc) b : Fin (n + 1) → Bool) (⟨i, hlt⟩ : Fin n).castSucc
    rw [Fin.snoc_castSucc]

lemma output_within (C : Circuit) (m : ℕ) (x : Fin m → Bool)
    (ht : circuitFun m C x = true) : C.output < m + C.gates.length := by
  by_contra h
  have hout : (run C.gates (List.ofFn x)).getD C.output false = false :=
    List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)
  change (run C.gates (List.ofFn x)).getD C.output false = true at ht
  rw [ht] at hout
  contradiction

lemma minimal_last_output (C : Circuit) (m : ℕ) (hmin : IsMinimalCircuit m C)
    (hge : m ≤ C.output) (hlt : C.output < m + C.gates.length) :
    C.output + 1 = m + C.gates.length := by
  let k := C.output + 1 - m
  have hk : k ≤ C.gates.length := by omega
  let D : Circuit := ⟨C.gates.take k, C.output⟩
  have hl : FanInTwo D := fun g hg => hmin.1 g ((List.take_sublist _ _).subset hg)
  have he : circuitFun m D = circuitFun m C := by
    funext x
    change (run (C.gates.take k) (List.ofFn x)).getD C.output false =
      (run C.gates (List.ofFn x)).getD C.output false
    conv_rhs => rw [← List.take_append_drop k C.gates, run_append]
    symm
    apply run_preserves
    rw [cut_prefix_length _ _ _ hk]
    omega
  have hb := hmin.2 D hl he
  change C.gates.length ≤ (C.gates.take k).length at hb
  rw [List.length_take_of_le hk] at hb
  omega

lemma h_false_and_true (n : ℕ) (H : (Fin n → Bool) → Bool)
    (hH : ∃ y y', H y ≠ H y') : (∃ x, H x = false) ∧ (∃ x, H x = true) := by
  obtain ⟨y, y', hn⟩ := hH
  cases hy : H y <;> cases hy' : H y'
  · rw [hy, hy'] at hn
    contradiction
  · exact ⟨⟨y, hy⟩, ⟨y', hy'⟩⟩
  · exact ⟨⟨y', hy'⟩, ⟨y, hy⟩⟩
  · rw [hy, hy'] at hn
    contradiction

lemma x_or_H_not_input (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool)
    (htrue : ∃ y, H y = true)
    (hfn : ∀ x : Fin (n + 1) → Bool, circuitFun (n + 1) C x =
      (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) : n + 1 ≤ C.output := by
  by_contra! hout
  have ein (x : Fin (n + 1) → Bool) :
      circuitFun (n + 1) C x = x ⟨C.output, hout⟩ := by
    change (run C.gates (List.ofFn x)).getD C.output false = _
    rw [run_preserves _ _ _ (by simpa using hout)]
    exact getD_ofFn _ _ hout
  by_cases he : C.output = n
  · obtain ⟨y, hy⟩ := htrue
    let x : Fin (n + 1) → Bool := Fin.snoc y false
    have hx := ein x
    have hlast : (⟨C.output, hout⟩ : Fin (n + 1)) = Fin.last n := Fin.ext he
    rw [hlast] at hx
    have h := hfn x
    have hf : (fun i : Fin n => x i.castSucc) = y := by
      funext i
      exact Fin.snoc_castSucc _ _ _
    rw [hf, hy, Bool.or_true] at h
    rw [h] at hx
    simpa [x] using hx
  · let x : Fin (n + 1) → Bool := Fin.snoc (fun _ : Fin n => false) true
    let i : Fin n := ⟨C.output, by omega⟩
    have hx := ein x
    change circuitFun (n + 1) C x = x i.castSucc at hx
    have hh : circuitFun (n + 1) C x = true := by
      rw [hfn x]
      simp [x]
    rw [hh] at hx
    simpa [x] using hx

lemma start_chain (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool)
    (hlegal : ∀ g ∈ C.gates, NOk g) (hmin : IsMinimalCircuit (n + 1) C)
    (hH : ∃ y y' : Fin n → Bool, H y ≠ H y')
    (hfn : ∀ x : Fin (n + 1) → Bool, circuitFun (n + 1) C x =
      (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) :
    C.output + 1 = n + 1 + C.gates.length ∧ n + 1 ≤ C.output ∧
    HasWireChain C (n + 1) n ∧
    ∀ j : Fin C.gates.length, ∀ w, Reads C w j → w < n + 1 + j.val := by
  obtain ⟨⟨y₀, hy₀⟩, ⟨y₁, hy₁⟩⟩ := h_false_and_true n H hH
  have hcase (y : Fin n → Bool) (b : Bool) :
      circuitFun (n + 1) C (Fin.snoc y b) = (b || H y) := by
    rw [hfn]
    simp
  have h0 : circuitFun (n + 1) C (Fin.snoc y₀ false) = false := by
    rw [hcase, hy₀]
    rfl
  have h1 : circuitFun (n + 1) C (Fin.snoc y₁ false) = true := by
    rw [hcase, hy₁]
    rfl
  have hvar : ∃ x y : Fin (n + 1) → Bool, circuitFun (n + 1) C x ≠ circuitFun (n + 1) C y :=
    ⟨Fin.snoc y₀ false, Fin.snoc y₁ false, by rw [h0, h1]; decide⟩
  have hge := x_or_H_not_input n C H ⟨y₁, hy₁⟩ hfn
  have hlast := minimal_last_output C (n + 1) hmin hge (output_within C _ _ h1)
  have hstart (x : Fin (n + 1) → Bool) : forceValue C (n + 1) 0 n true x = true := by
    change (run C.gates ((List.ofFn x).set n true)).getD C.output false = true
    rw [ofFn_set_last]
    change circuitFun (n + 1) C (Fin.snoc (fun i : Fin n => x i.castSucc) true) = true
    rw [hcase]
    rfl
  refine ⟨hlast, hge, cut_chain C _ hlegal hmin hvar ⟨_, h0⟩ 0 n (by omega) (by omega) hstart, ?_⟩
  intro j w hw
  exact minimal_inputs_before C (n + 1) j.val j.isLt hlegal hmin hvar w hw

def normalized (C : Circuit) : Circuit := ⟨C.gates.map normGate, C.output⟩

lemma normalized_len (C : Circuit) : (normalized C).gates.length = C.gates.length := by
  simp [normalized]

lemma normalized_legal (C : Circuit) (h : FanInTwo C) :
    ∀ g ∈ (normalized C).gates, NOk g := by
  intro g hg
  obtain ⟨origin, ho, rfl⟩ := List.mem_map.mp hg
  exact normGate_nok origin (h origin ho)

lemma normalized_fun (C : Circuit) (m : ℕ) : circuitFun m (normalized C) = circuitFun m C := by
  funext x
  change (run (C.gates.map normGate) (List.ofFn x)).getD C.output false =
    (run C.gates (List.ofFn x)).getD C.output false
  rw [run_norm]

lemma normalized_min (C : Circuit) (m : ℕ) (hc : IsMinimalCircuit m C) :
    IsMinimalCircuit m (normalized C) := by
  refine ⟨fun g hg => (normalized_legal C hc.1 g hg).1, ?_⟩
  intro D hD he
  rw [normalized_fun] at he
  simpa [Circuit.size, normalized_len] using hc.2 D hD he

def EffRead (C : Circuit) (v : ℕ) (j : Fin C.gates.length) : Prop :=
  ((C.gates.get j).op = GateOp.not ∧ (C.gates.get j).inputs.head? = some v) ∨
    ((C.gates.get j).op ≠ GateOp.not ∧ v ∈ (C.gates.get j).inputs)

def Link (C : Circuit) (m a b : ℕ) : Prop :=
  ∃ j : Fin C.gates.length, b = m + j.val ∧ EffRead C a j

lemma normGate_op (g : Gate) : (normGate g).op = g.op := by
  cases g with
  | mk op ins => cases op <;> rfl

lemma normGate_of_or (g : Gate) (hg : g.op = GateOp.or) : normGate g = g := by
  cases g with
  | mk op ins => change op = GateOp.or at hg; subst op; rfl

lemma norm_index (C : Circuit) (j : Fin (normalized C).gates.length) :
    (normalized C).gates.get j = normGate (C.gates.get (Fin.cast (normalized_len C) j)) := by
  have hj : j.val < C.gates.length := by simpa only [normalized_len] using j.isLt
  have hjm : j.val < (C.gates.map normGate).length := by simpa only [List.length_map] using hj
  change (C.gates.map normGate)[j.val]'hjm = normGate (C.gates[j.val]'hj)
  rw [List.getElem_map]

lemma norm_eff (C : Circuit) (v : ℕ) (j : Fin (normalized C).gates.length) :
    Reads (normalized C) v j ↔ EffRead C v (Fin.cast (normalized_len C) j) := by
  unfold Reads EffRead
  rw [norm_index]
  generalize (C.gates.get (Fin.cast (normalized_len C) j)) = g
  rcases g with ⟨op, ins⟩
  cases op <;> simp [normGate]
  cases ins <;> simp [eq_comm]

def EffOrLink (C : Circuit) (m v : ℕ) (j : Fin C.gates.length) : Prop :=
  (C.gates.get j).op = GateOp.or ∧ (C.gates.get j).inputs.length = 2 ∧
    EffRead C v j ∧ (∀ r, EffRead C v r → r = j) ∧
    ∃ w ∈ (C.gates.get j).inputs, w ≠ v ∧ w < m + j.val

lemma norm_link (C : Circuit) (m v : ℕ) (j : Fin (normalized C).gates.length)
    (h : OrLink (normalized C) m v j) :
    EffOrLink C m v (Fin.cast (normalized_len C) j) := by
  obtain ⟨ho, hl, hr, hu, hw⟩ := h
  have hop : (C.gates.get (Fin.cast (normalized_len C) j)).op = GateOp.or := by
    rw [norm_index, normGate_op] at ho
    exact ho
  have hg : (normalized C).gates.get j = C.gates.get (Fin.cast (normalized_len C) j) :=
    (norm_index C j).trans (normGate_of_or _ hop)
  refine ⟨hop, hg ▸ hl, (norm_eff C v j).mp hr, ?_, hg ▸ hw⟩
  intro r hRead
  let r' := Fin.cast (normalized_len C).symm r
  have hr' : Fin.cast (normalized_len C) r' = r := by simp [r']
  have he : Reads (normalized C) v r' := (norm_eff C v r').mpr (hr'.symm ▸ hRead)
  rw [← hr', hu r' he]

def HasEffChain (C : Circuit) (m v : ℕ) : Prop :=
  ∃ (l : ℕ) (f : Fin (l + 1) → ℕ), f 0 = v ∧ f (Fin.last l) = C.output ∧
    ∀ i : Fin l, ∃ j : Fin C.gates.length,
      f i.succ = m + j.val ∧ EffOrLink C m (f i.castSucc) j ∧ f i.castSucc < f i.succ

lemma transfer_chain (C : Circuit) (m v : ℕ) (h : HasWireChain (normalized C) m v) :
    HasEffChain C m v := by
  obtain ⟨l, f, h0, hend, hs⟩ := h
  refine ⟨l, f, h0, hend, ?_⟩
  intro i
  obtain ⟨j, hval, hj, hlt⟩ := hs i
  exact ⟨Fin.cast (normalized_len C) j, hval, norm_link C m (f i.castSucc) j hj, hlt⟩

lemma transfer_input_bound (C : Circuit) (m : ℕ)
    (h : ∀ j : Fin (normalized C).gates.length, ∀ w, Reads (normalized C) w j → w < m + j.val) :
    ∀ j : Fin C.gates.length, ∀ w, EffRead C w j → w < m + j.val := by
  intro j w hr
  let j' := Fin.cast (normalized_len C).symm j
  have hj' : Fin.cast (normalized_len C) j' = j := by simp [j']
  exact h j' w ((norm_eff C w j').mpr (hj'.symm ▸ hr))

lemma eff_or_read (C : Circuit) (v : ℕ) (j : Fin C.gates.length)
    (ho : (C.gates.get j).op = GateOp.or) :
    EffRead C v j ↔ v ∈ (C.gates.get j).inputs := by
  unfold EffRead
  rw [ho]
  simp

lemma reach_chain (C : Circuit) (m k : ℕ) (f : Fin (k + 1 + 1) → ℕ)
    (c : Fin (k + 1) → Fin C.gates.length)
    (hval : ∀ i : Fin (k + 1), f i.succ = m + (c i).val)
    (hlink : ∀ i : Fin (k + 1), EffOrLink C m (f i.castSucc) (c i))
    (hend : f (Fin.last (k + 1)) = C.output)
    (hfinal : ∀ j : Fin C.gates.length, ¬ EffRead C C.output j) :
    ∀ w, Relation.TransGen (Link C m) (f 0) w ↔ ∃ i : Fin (k + 1), f i.succ = w := by
  have hstep (i : Fin (k + 1)) : Link C m (f i.castSucc) (f i.succ) :=
    ⟨c i, hval i, (hlink i).2.2.1⟩
  intro w
  constructor
  · intro hw
    induction hw with
    | single h =>
      obtain ⟨j, he, hr⟩ := h
      have hu := (hlink 0).2.2.2.1 j (by simpa using hr)
      rw [hu] at he
      exact ⟨0, (hval 0).trans he.symm⟩
    | tail _ ht ih =>
      obtain ⟨i, hi⟩ := ih
      obtain ⟨j, he, hr⟩ := ht
      by_cases hlast : i.val = k
      · have hf : i.succ = Fin.last (k + 1) := Fin.ext (by simp [hlast])
        rw [← hi, hf, hend] at hr
        exact False.elim (hfinal j hr)
      · let t : Fin (k + 1) := ⟨i.val + 1, by omega⟩
        have hp : t.castSucc = i.succ := Fin.ext rfl
        have hread : EffRead C (f t.castSucc) j := by rwa [hp, hi]
        have hu := (hlink t).2.2.2.1 j hread
        rw [hu] at he
        exact ⟨t, (hval t).trans he.symm⟩
  · rintro ⟨i, rfl⟩
    have hInd (j : ℕ) (hj : j < k + 1) :
        Relation.TransGen (Link C m) (f 0) (f (⟨j, hj⟩ : Fin (k + 1)).succ) := by
      induction j with
      | zero => exact Relation.TransGen.single (hstep ⟨0, hj⟩)
      | succ j ih =>
        exact Relation.TransGen.tail (ih (by omega)) (hstep ⟨j + 1, hj⟩)
    exact hInd i.val i.isLt

lemma other_not_reachable (C : Circuit) (m k : ℕ) (f : Fin (k + 1 + 1) → ℕ)
    (c : Fin (k + 1) → Fin C.gates.length) (hf : StrictMono f) (hc : StrictMono c)
    (hval : ∀ i : Fin (k + 1), f i.succ = m + (c i).val)
    (hlink : ∀ i : Fin (k + 1), EffOrLink C m (f i.castSucc) (c i))
    (hreach : ∀ w, Relation.TransGen (Link C m) (f 0) w ↔ ∃ i : Fin (k + 1), f i.succ = w)
    (i : Fin (k + 1)) (w : ℕ)
    (hread : EffRead C w (c i)) (hne : w ≠ f i.castSucc) (hlt : w < m + (c i).val) :
    ¬ Relation.TransGen (Link C m) (f 0) w := by
  intro hr
  obtain ⟨t, ht⟩ := (hreach w).mp hr
  have hlt' : f t.succ < f i.succ := by rwa [ht, hval]
  have hti : t.val < i.val := by
    have hs := hf.lt_iff_lt.mp hlt'
    change t.val + 1 < i.val + 1 at hs
    omega
  have hne' : t.val + 1 ≠ i.val := by
    intro he
    have hf' : t.succ = i.castSucc := Fin.ext he
    apply hne
    rw [← ht, hf']
  let u : Fin (k + 1) := ⟨t.val + 1, by omega⟩
  have hu : u.castSucc = t.succ := Fin.ext rfl
  have hru : EffRead C (f u.castSucc) (c i) := by rwa [hu, ht]
  have hic := (hlink u).2.2.2.1 (c i) hru
  have hiu := congrArg Fin.val (hc.injective hic)
  change i.val = t.val + 1 at hiu
  omega

lemma finish_chain (C : Circuit) (m v : ℕ) (hv : v < m) (hout : m ≤ C.output)
    (hfinal : C.output + 1 = m + C.gates.length)
    (htop : ∀ j : Fin C.gates.length, ∀ w, EffRead C w j → w < m + j.val)
    (hchain : HasEffChain C m v) :
    ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length),
      StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧
      C.output = m + (c (Fin.last k)).val ∧
      (∀ i : Fin (k + 1), (C.gates.get (c i)).op = GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧
      v ∈ (C.gates.get (c 0)).inputs ∧
      (∀ i : Fin k, m + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧
      (∀ j, EffRead C v j → j = c 0) ∧
      (∀ (i : Fin k) j, EffRead C (m + (c i.castSucc).val) j → j = c i.succ) ∧
      (∀ j : Fin C.gates.length, Relation.TransGen (Link C m) v (m + j.val) ↔
        ∃ i : Fin (k + 1), c i = j) ∧
      (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ v ∧ w < m + (c 0).val ∧
        ¬ Relation.TransGen (Link C m) v w) ∧
      (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs,
        w ≠ m + (c i.castSucc).val ∧ w ≠ v ∧ w < m + (c i.succ).val ∧
          ¬ Relation.TransGen (Link C m) v w) := by
  obtain ⟨l, f, hstart, hend, hs⟩ := hchain
  cases l with
  | zero =>
    have he : (0 : Fin (0 + 1)) = Fin.last 0 := Fin.ext rfl
    rw [← he, hstart] at hend
    omega
  | succ k =>
    let c (i : Fin (k + 1)) : Fin C.gates.length := Classical.choose (hs i)
    have hstep (i : Fin (k + 1)) :=
      Classical.choose_spec (hs i)
    have hval (i : Fin (k + 1)) : f i.succ = m + (c i).val := (hstep i).1
    have hlink (i : Fin (k + 1)) : EffOrLink C m (f i.castSucc) (c i) := (hstep i).2.1
    have hf : StrictMono f := Fin.strictMono_iff_lt_succ.mpr fun i => (hstep i).2.2
    have hc : StrictMono c := by
      intro i j hij
      have h := hf (show i.succ < j.succ by simpa using hij)
      rw [hval i, hval j] at h
      change (c i).val < (c j).val
      omega
    have hout' : C.output = m + (c (Fin.last k)).val := by
      rw [← hend]
      simpa [Fin.succ_last] using hval (Fin.last k)
    have hno (j : Fin C.gates.length) : ¬ EffRead C C.output j := by
      intro hj
      have hb := htop j C.output hj
      omega
    have hr := reach_chain C m k f c hval hlink hend hno
    have hstart' : f (0 : Fin (k + 1)).castSucc = v := hstart
    have hpred (i : Fin k) : f i.succ.castSucc = m + (c i.castSucc).val := by
      have he : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
      rw [he, hval]
    have hr0 : EffRead C v (c 0) := by
      have he := (hlink 0).2.2.1
      rwa [hstart'] at he
    have hunique0 (j : Fin C.gates.length) (hj : EffRead C v j) : j = c 0 :=
      (hlink 0).2.2.2.1 j (hstart'.symm ▸ hj)
    have hrstep (i : Fin k) : EffRead C (m + (c i.castSucc).val) (c i.succ) := by
      have he := (hlink i.succ).2.2.1
      rwa [hpred i] at he
    have hunique (i : Fin k) (j : Fin C.gates.length)
        (hj : EffRead C (m + (c i.castSucc).val) j) : j = c i.succ :=
      (hlink i.succ).2.2.2.1 j ((hpred i).symm ▸ hj)
    have other (i : Fin (k + 1)) :
        ∃ w ∈ (C.gates.get (c i)).inputs, w ≠ f i.castSucc ∧ w < m + (c i).val ∧
          ¬ Relation.TransGen (Link C m) v w := by
      obtain ⟨w, hw, hne, hlt⟩ := (hlink i).2.2.2.2
      refine ⟨w, hw, hne, hlt, ?_⟩
      rw [← hstart]
      exact other_not_reachable C m k f c hf hc hval hlink hr i w
        ((eff_or_read C w (c i) (hlink i).1).mpr hw) hne hlt
    refine ⟨k, c, hc, by omega, hout', fun i => ⟨(hlink i).1, (hlink i).2.1⟩, ?_, ?_,
      hunique0, hunique, ?_, ?_, ?_⟩
    · exact (eff_or_read C v (c 0) (hlink 0).1).mp hr0
    · intro i
      exact (eff_or_read C _ _ (hlink i.succ).1).mp (hrstep i)
    · intro j
      rw [← hstart, hr]
      constructor
      · rintro ⟨i, hi⟩
        refine ⟨i, Fin.ext ?_⟩
        rw [hval i] at hi
        omega
      · rintro ⟨i, h⟩
        exact ⟨i, by rw [hval i, h]⟩
    · simpa only [hstart'] using other 0
    · intro i
      obtain ⟨w, hw, hne, hlt, hnr⟩ := other i.succ
      have hnv : w ≠ v := by
        intro he
        have hread := (eff_or_read C w (c i.succ) (hlink i.succ).1).mpr hw
        rw [he] at hread
        have hEq := congrArg Fin.val (hc.injective (hunique0 _ hread))
        change i.val + 1 = 0 at hEq
        omega
      exact ⟨w, hw, by simpa only [hpred i] using hne, hnv, hlt, hnr⟩

lemma solve (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool)
    (hmin : IsMinimalCircuit (n + 1) C)
    (hH : ∃ y y' : Fin n → Bool, H y ≠ H y')
    (hfn : ∀ x : Fin (n + 1) → Bool, circuitFun (n + 1) C x =
      (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) :
    ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length),
      StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧
      C.output = n + 1 + (c (Fin.last k)).val ∧
      (∀ i : Fin (k + 1), (C.gates.get (c i)).op = GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧
      n ∈ (C.gates.get (c 0)).inputs ∧
      (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧
      (∀ j, EffRead C n j → j = c 0) ∧
      (∀ (i : Fin k) j, EffRead C (n + 1 + (c i.castSucc).val) j → j = c i.succ) ∧
      (∀ j : Fin C.gates.length, Relation.TransGen (Link C (n + 1)) n (n + 1 + j.val) ↔
        ∃ i : Fin (k + 1), c i = j) ∧
      (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧
        ¬ Relation.TransGen (Link C (n + 1)) n w) ∧
      (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs,
        w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧
          ¬ Relation.TransGen (Link C (n + 1)) n w) := by
  have hn (x : Fin (n + 1) → Bool) :
      circuitFun (n + 1) (normalized C) x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc)) := by
    rw [normalized_fun]
    exact hfn x
  obtain ⟨hlast, hge, hchain, htop⟩ :=
    start_chain n (normalized C) H (normalized_legal C hmin.1) (normalized_min C _ hmin) hH hn
  have hlast' : C.output + 1 = n + 1 + C.gates.length := by
    rw [normalized_len] at hlast
    exact hlast
  exact finish_chain C (n + 1) n (by omega) hge hlast'
    (transfer_input_bound C _ htop) (transfer_chain C _ _ hchain)

end PEqualNP.Outside.L_meta_568_aux

theorem PEqualNP.Outside.L_meta_568 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (H : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y y' : Fin n → Bool, H y ≠ H y') → (∀ x : Fin (n + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) → ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length), StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧ C.output = n + 1 + (c (Fin.last k)).val ∧ (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧ n ∈ (C.gates.get (c 0)).inputs ∧ (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧ (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → j = c 0) ∧ (∀ (i : Fin k) (j : Fin C.gates.length), ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ) ∧ (∀ j : Fin C.gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧ (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) ∧ (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) := by
  intro n C H hmin hH hfn
  exact PEqualNP.Outside.L_meta_568_aux.solve n C H hmin hH hfn
