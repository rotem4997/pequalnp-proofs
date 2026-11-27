import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6965

open PEqualNP.CircuitLowerBounds

inductive Sym where
  | wire (i : ℕ)
  | cst (b : Bool)
  deriving DecidableEq

def Sym.val (V : List Bool) : Sym → Bool
  | .wire i => V.getD i false
  | .cst b => b

def Sym.isW : Sym → Bool
  | .wire _ => true
  | .cst _ => false

def Sym.idx : Sym → ℕ
  | .wire i => i
  | .cst _ => 0

def Sym.wf (L : ℕ) : Sym → Prop
  | .wire i => i < L
  | .cst _ => True

def finish (c : Bool) (op : GateOp) : List Sym → Sym ⊕ (GateOp × List ℕ)
  | [] => .inl (.cst c)
  | [w] => .inl w
  | w1 :: w2 :: rest => .inr (op, (w1 :: w2 :: rest).map Sym.idx)

def proc : GateOp → List Sym → Sym ⊕ (GateOp × List ℕ)
  | .and, ss => if Sym.cst false ∈ ss then .inl (.cst false)
      else finish true .and (ss.filter Sym.isW)
  | .or, ss => if Sym.cst true ∈ ss then .inl (.cst true)
      else finish false .or (ss.filter Sym.isW)
  | .not, [] => .inl (.cst true)
  | .not, (.cst c :: _) => .inl (.cst (!c))
  | .not, (.wire i :: _) => .inr (.not, [i])
  | .mod _, _ => .inl (.cst false)
  | .maj, _ => .inl (.cst false)

theorem finish_inl {c : Bool} {op : GateOp} {ws : List Sym} {s : Sym}
    (h : finish c op ws = .inl s) : (ws = [] ∧ s = .cst c) ∨ ws = [s] := by
  rcases ws with _ | ⟨w, _ | ⟨w2, rest⟩⟩
  · simp only [finish, Sum.inl.injEq] at h
    subst h
    exact Or.inl ⟨rfl, rfl⟩
  · simp only [finish, Sum.inl.injEq] at h
    subst h
    exact Or.inr rfl
  · simp [finish] at h

theorem finish_inr {c : Bool} {op op' : GateOp} {ws : List Sym} {is : List ℕ}
    (h : finish c op ws = .inr (op', is)) : op' = op ∧ is = ws.map Sym.idx := by
  rcases ws with _ | ⟨w, _ | ⟨w2, rest⟩⟩
  · simp [finish] at h
  · simp [finish] at h
  · simp only [finish, Sum.inr.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.symm⟩

theorem finish_short {c : Bool} {op : GateOp} {ws : List Sym} (h : ws.length ≤ 1) :
    ∃ s, finish c op ws = .inl s := by
  rcases ws with _ | ⟨w, _ | ⟨w2, rest⟩⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · simp at h

theorem and_filter (V : List Bool) : ∀ ss : List Sym, Sym.cst false ∉ ss →
    (ss.map (Sym.val V)).all id = ((ss.filter Sym.isW).map (Sym.val V)).all id
  | [] => by simp
  | s :: ss => by
      intro h
      have h2 : Sym.cst false ∉ ss := fun e => h (by simp [e])
      have ih := and_filter V ss h2
      cases s with
      | wire i => simp [List.filter_cons, Sym.isW, ih]
      | cst b =>
        cases b
        · exact (h (by simp)).elim
        · simp [List.filter_cons, Sym.isW, Sym.val, ih]

theorem or_filter (V : List Bool) : ∀ ss : List Sym, Sym.cst true ∉ ss →
    (ss.map (Sym.val V)).any id = ((ss.filter Sym.isW).map (Sym.val V)).any id
  | [] => by simp
  | s :: ss => by
      intro h
      have h2 : Sym.cst true ∉ ss := fun e => h (by simp [e])
      have ih := or_filter V ss h2
      cases s with
      | wire i => simp [List.filter_cons, Sym.isW, ih]
      | cst b =>
        cases b
        · simp [List.filter_cons, Sym.isW, Sym.val, ih]
        · exact (h (by simp)).elim

theorem wires_map (V : List Bool) (ws : List Sym) (h : ∀ s ∈ ws, s.isW = true) :
    (ws.map Sym.idx).map (fun i => V.getD i false) = ws.map (Sym.val V) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro s hs
  cases s with
  | wire i => rfl
  | cst b =>
    have := h _ hs
    simp [Sym.isW] at this

theorem filter_lt : ∀ (ss : List Sym) (s : Sym), s ∈ ss → s.isW = false →
    (ss.filter Sym.isW).length + 1 ≤ ss.length
  | [], s, h, _ => by simp at h
  | t :: ss, s, h, hs => by
      rcases List.mem_cons.1 h with rfl | h'
      · have := List.length_filter_le Sym.isW ss
        have e : (s :: ss).filter Sym.isW = ss.filter Sym.isW := by simp [List.filter_cons, hs]
        rw [e, List.length_cons]
        omega
      · have := filter_lt ss s h' hs
        by_cases ht : t.isW = true
        · have e : (t :: ss).filter Sym.isW = t :: ss.filter Sym.isW := by
            simp [List.filter_cons, ht]
          rw [e, List.length_cons, List.length_cons]
          omega
        · have e : (t :: ss).filter Sym.isW = ss.filter Sym.isW := by simp [List.filter_cons, ht]
          rw [e, List.length_cons]
          omega

theorem proc_inl (V : List Bool) {op : GateOp} {ss : List Sym} {s : Sym}
    (hop : op = .and ∨ op = .or ∨ op = .not) (h : proc op ss = .inl s) :
    s.val V = op.eval (ss.map (Sym.val V)) ∧ (s ∈ ss ∨ ∃ b, s = .cst b) := by
  rcases hop with rfl | rfl | rfl
  · by_cases hf : Sym.cst false ∈ ss
    · simp only [proc, hf, if_true, Sum.inl.injEq] at h
      subst h
      refine ⟨?_, Or.inr ⟨_, rfl⟩⟩
      cases hall : (ss.map (Sym.val V)).all id
      · simp only [GateOp.eval, Sym.val, hall]
      · have := List.all_eq_true.1 hall (Sym.val V (.cst false)) (List.mem_map.2 ⟨_, hf, rfl⟩)
        simp [Sym.val] at this
    · simp only [proc, hf, if_false] at h
      have key := and_filter V ss hf
      rcases finish_inl h with ⟨he, rfl⟩ | he
      · rw [he] at key
        refine ⟨?_, Or.inr ⟨_, rfl⟩⟩
        simp only [GateOp.eval, key]
        simp [Sym.val]
      · have hm : s ∈ ss := List.mem_of_mem_filter (by rw [he]; simp)
        rw [he] at key
        refine ⟨?_, Or.inl hm⟩
        simp only [GateOp.eval, key]
        simp
  · by_cases hf : Sym.cst true ∈ ss
    · simp only [proc, hf, if_true, Sum.inl.injEq] at h
      subst h
      refine ⟨?_, Or.inr ⟨_, rfl⟩⟩
      simp only [GateOp.eval]
      exact (List.any_eq_true.2 ⟨true, List.mem_map.2 ⟨_, hf, rfl⟩, rfl⟩).symm
    · simp only [proc, hf, if_false] at h
      have key := or_filter V ss hf
      rcases finish_inl h with ⟨he, rfl⟩ | he
      · rw [he] at key
        refine ⟨?_, Or.inr ⟨_, rfl⟩⟩
        simp only [GateOp.eval, key]
        simp [Sym.val]
      · have hm : s ∈ ss := List.mem_of_mem_filter (by rw [he]; simp)
        rw [he] at key
        refine ⟨?_, Or.inl hm⟩
        simp only [GateOp.eval, key]
        simp
  · rcases ss with _ | ⟨t, ss⟩
    · simp only [proc, Sum.inl.injEq] at h
      subst h
      exact ⟨by simp [GateOp.eval, Sym.val], Or.inr ⟨_, rfl⟩⟩
    · cases t with
      | cst c =>
        simp only [proc, Sum.inl.injEq] at h
        subst h
        exact ⟨by simp [GateOp.eval, Sym.val], Or.inr ⟨_, rfl⟩⟩
      | wire i => simp [proc] at h

theorem proc_inr (V : List Bool) {op op' : GateOp} {ss : List Sym} {is : List ℕ}
    (h : proc op ss = .inr (op', is)) :
    (op' = .and ∨ op' = .or ∨ op' = .not) ∧ is.length ≤ ss.length ∧
    op'.eval (is.map (fun i => V.getD i false)) = op.eval (ss.map (Sym.val V)) := by
  cases op with
  | and =>
    by_cases hf : Sym.cst false ∈ ss
    · simp [proc, hf] at h
    · simp only [proc, hf, if_false] at h
      obtain ⟨rfl, rfl⟩ := finish_inr h
      have hw : ∀ s ∈ ss.filter Sym.isW, s.isW = true := fun s hs => (List.mem_filter.1 hs).2
      refine ⟨Or.inl rfl, by rw [List.length_map]; exact List.length_filter_le _ _, ?_⟩
      simp only [GateOp.eval]
      rw [wires_map V _ hw, and_filter V ss hf]
  | or =>
    by_cases hf : Sym.cst true ∈ ss
    · simp [proc, hf] at h
    · simp only [proc, hf, if_false] at h
      obtain ⟨rfl, rfl⟩ := finish_inr h
      have hw : ∀ s ∈ ss.filter Sym.isW, s.isW = true := fun s hs => (List.mem_filter.1 hs).2
      refine ⟨Or.inr (Or.inl rfl), by rw [List.length_map]; exact List.length_filter_le _ _, ?_⟩
      simp only [GateOp.eval]
      rw [wires_map V _ hw, or_filter V ss hf]
  | not =>
    rcases ss with _ | ⟨t, ss⟩
    · simp [proc] at h
    · cases t with
      | cst c => simp [proc] at h
      | wire j =>
        simp only [proc, Sum.inr.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨Or.inr (Or.inr rfl), by simp, by simp [GateOp.eval, Sym.val]⟩
  | mod m => simp [proc] at h
  | maj => simp [proc] at h

structure St where
  gs : List Gate
  m : List Sym

def look (m : List Sym) (i : ℕ) : Sym := m.getD i (.cst false)

def stepS (n : ℕ) (st : St) (g : Gate) : St :=
  match proc g.op (g.inputs.map (look st.m)) with
  | .inl s => ⟨st.gs, st.m ++ [s]⟩
  | .inr (op', is) => ⟨st.gs ++ [⟨op', is⟩], st.m ++ [.wire (n + st.gs.length)]⟩

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len_fold : ∀ (gs : List Gate) (X : List Bool),
    (gs.foldl wstep X).length = X.length + gs.length
  | [], X => by simp
  | g :: gs, X => by
      rw [List.foldl_cons, len_fold gs]
      simp only [wstep, List.length_append, List.length_cons, List.length_nil]
      omega

theorem getD_snoc_lt {α : Type} (l : List α) (b d : α) {i : ℕ} (h : i < l.length) :
    (l ++ [b]).getD i d = l.getD i d := List.getD_append _ _ _ _ h

theorem getD_snoc_eq {α : Type} (l : List α) (b d : α) : (l ++ [b]).getD l.length d = b := by
  simp

theorem getD_snoc_gt {α : Type} (l : List α) (b d : α) {i : ℕ} (h : l.length < i) :
    (l ++ [b]).getD i d = d := List.getD_eq_default _ _ (by simp; omega)

theorem wstep_len (w : List Bool) (g : Gate) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

theorem wstep_lt (w : List Bool) (g : Gate) {i : ℕ} (h : i < w.length) :
    (wstep w g).getD i false = w.getD i false := getD_snoc_lt _ _ _ h

theorem wstep_gt (w : List Bool) (g : Gate) {i : ℕ} (h : w.length < i) :
    (wstep w g).getD i false = false := getD_snoc_gt _ _ _ h

theorem val_snoc (V : List Bool) (c : Bool) (s : Sym) (h : s.wf V.length) :
    s.val (V ++ [c]) = s.val V := by
  cases s with
  | wire i => exact getD_snoc_lt V c false h
  | cst b => rfl

theorem wf_mono {L L' : ℕ} (s : Sym) (h : s.wf L) (hL : L ≤ L') : s.wf L' := by
  cases s with
  | wire i => exact lt_of_lt_of_le h hL
  | cst b => trivial

abbrev Fan (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

abbrev Inv (X : List Bool) (n a b : ℕ) (W : List Bool) (st : St) : Prop :=
  X.length = n ∧ st.m.length = W.length ∧ n ≤ W.length ∧
  (∀ i, W.getD i false = (look st.m i).val (st.gs.foldl wstep X)) ∧
  (∀ i, (look st.m i).wf (st.gs.foldl wstep X).length) ∧
  look st.m a = .cst false ∧ look st.m b = .cst false ∧
  (∀ g ∈ st.gs, Fan g) ∧ a < n ∧ b < n

theorem step_inv (X : List Bool) (n a b : ℕ) (W : List Bool) (st : St) (g : Gate)
    (hI : Inv X n a b W st) (hg : Fan g) :
    Inv X n a b (wstep W g) (stepS n st g) := by
  obtain ⟨hXn, hlen, hnW, hval, hwf, ha, hb, hfan, haX, hbX⟩ := hI
  have hop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
    have := hg.1
    simpa using this
  have hinp : g.inputs.map (fun i => W.getD i false) =
      (g.inputs.map (look st.m)).map (Sym.val (st.gs.foldl wstep X)) := by
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => hval i)
  have hWv : (wstep W g).getD W.length false = g.op.eval (g.inputs.map fun i => W.getD i false) :=
    getD_snoc_eq _ _ _
  cases hp : proc g.op (g.inputs.map (look st.m)) with
  | inl s =>
    obtain ⟨hs1, hs2⟩ := proc_inl (st.gs.foldl wstep X) hop hp
    have hswf : s.wf (st.gs.foldl wstep X).length := by
      rcases hs2 with hs | ⟨c, rfl⟩
      · obtain ⟨j, _, rfl⟩ := List.mem_map.1 hs
        exact hwf j
      · trivial
    have hst : stepS n st g = ⟨st.gs, st.m ++ [s]⟩ := by simp only [stepS, hp]
    rw [hst]
    refine ⟨hXn, by rw [wstep_len, List.length_append, hlen]; rfl,
      by rw [wstep_len]; omega, ?_, ?_, ?_, ?_, hfan, haX, hbX⟩
    · intro i
      rcases lt_trichotomy i W.length with hi | rfl | hi
      · rw [wstep, getD_snoc_lt _ _ _ hi, look, getD_snoc_lt _ _ _ (hlen ▸ hi)]
        exact hval i
      · rw [hWv, look, ← hlen, getD_snoc_eq, hs1, ← hinp]
      · rw [wstep, getD_snoc_gt _ _ _ hi, look, getD_snoc_gt _ _ _ (hlen ▸ hi)]
        rfl
    · intro i
      rcases lt_trichotomy i st.m.length with hi | rfl | hi
      · rw [look, getD_snoc_lt _ _ _ hi]
        exact hwf i
      · rw [look, getD_snoc_eq]
        exact hswf
      · rw [look, getD_snoc_gt _ _ _ hi]
        trivial
    · rw [look, getD_snoc_lt _ _ _ (by omega)]
      exact ha
    · rw [look, getD_snoc_lt _ _ _ (by omega)]
      exact hb
  | inr p =>
    rcases p with ⟨op', is⟩
    obtain ⟨hop', hislen, hev⟩ := proc_inr (st.gs.foldl wstep X) hp
    have hst : stepS n st g = ⟨st.gs ++ [⟨op', is⟩], st.m ++ [.wire (n + st.gs.length)]⟩ := by
      simp only [stepS, hp]
    rw [hst]
    simp only [Inv]
    have hV' : (st.gs ++ [(⟨op', is⟩ : Gate)]).foldl wstep X =
        wstep (st.gs.foldl wstep X) (⟨op', is⟩ : Gate) := by
      simp [List.foldl_append]
    have hn : n + st.gs.length = (st.gs.foldl wstep X).length := by
      rw [len_fold]
      omega
    rw [hV', hn]
    refine ⟨hXn, by rw [wstep_len, List.length_append, hlen]; rfl,
      by rw [wstep_len]; omega, ?_, ?_, ?_, ?_, ?_, haX, hbX⟩
    · intro i
      rcases lt_trichotomy i W.length with hi | rfl | hi
      · rw [wstep_lt W g hi, look, getD_snoc_lt _ _ _ (hlen ▸ hi)]
        rw [wstep]
        exact (hval i).trans (val_snoc _ _ _ (hwf i)).symm
      · rw [hWv, look, ← hlen, getD_snoc_eq]
        show _ = (wstep (List.foldl wstep X st.gs) ⟨op', is⟩).getD
          (List.foldl wstep X st.gs).length false
        rw [wstep, getD_snoc_eq, hinp]
        exact hev.symm
      · rw [wstep_gt W g hi, look, getD_snoc_gt _ _ _ (hlen ▸ hi)]
        rfl
    · intro i
      rcases lt_trichotomy i st.m.length with hi | rfl | hi
      · rw [look, getD_snoc_lt _ _ _ hi]
        exact wf_mono _ (hwf i) (by rw [wstep_len]; omega)
      · rw [look, getD_snoc_eq]
        show _ < _
        rw [wstep_len]
        omega
      · rw [look, getD_snoc_gt _ _ _ hi]
        trivial
    · rw [look, getD_snoc_lt _ _ _ (by omega)]
      exact ha
    · rw [look, getD_snoc_lt _ _ _ (by omega)]
      exact hb
    · intro g' hg'
      rcases List.mem_append.1 hg' with h' | h'
      · exact hfan g' h'
      · simp only [List.mem_singleton] at h'
        subst h'
        refine ⟨?_, ?_⟩
        · show op' ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)
          rcases hop' with h1 | h1 | h1 <;> simp [h1]
        · show is.length ≤ 2
          have := hg.2
          simp only [List.length_map] at hislen
          omega

theorem fold_inv (X : List Bool) (n a b : ℕ) : ∀ (gs : List Gate) (W : List Bool) (st : St),
    Inv X n a b W st → (∀ g ∈ gs, Fan g) →
    Inv X n a b (gs.foldl wstep W) (gs.foldl (stepS n) st)
  | [], W, st, h, _ => h
  | g :: gs, W, st, h, hf => by
      rw [List.foldl_cons, List.foldl_cons]
      exact fold_inv X n a b gs _ _ (step_inv X n a b W st g h (hf g (by simp)))
        (fun g' hg' => hf g' (by simp [hg']))

def P (a b : ℕ) (g : Gate) : Bool :=
  (List.take (bif g.op.eval [false] then 1 else 2) g.inputs).any fun j => j == a || j == b

theorem P_inl (m : List Sym) (a b : ℕ) (g : Gate) (hg : Fan g)
    (ha : look m a = .cst false) (hb : look m b = .cst false) (hP : P a b g = true) :
    ∃ s, proc g.op (g.inputs.map (look m)) = .inl s := by
  have hop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
    have := hg.1
    simpa using this
  have hlen := hg.2
  have hj : ∃ j ∈ g.inputs, j = a ∨ j = b := by
    simp only [P, List.any_eq_true] at hP
    obtain ⟨j, hj, hj2⟩ := hP
    exact ⟨j, List.mem_of_mem_take hj, by simpa using hj2⟩
  obtain ⟨j, hjm, hjab⟩ := hj
  have hmem : Sym.cst false ∈ g.inputs.map (look m) :=
    List.mem_map.2 ⟨j, hjm, by rcases hjab with rfl | rfl; exacts [ha, hb]⟩
  rcases hop with h | h | h
  · rw [h]
    simp only [proc, hmem, if_true]
    exact ⟨_, rfl⟩
  · rw [h]
    simp only [proc]
    split_ifs with ht
    · exact ⟨_, rfl⟩
    · apply finish_short
      have := filter_lt _ _ hmem rfl
      simp only [List.length_map] at this
      omega
  · rcases hin : g.inputs with _ | ⟨k, rest⟩
    · rw [hin] at hjm
      simp at hjm
    · simp [P, h, hin, GateOp.eval] at hP
      rw [h]
      simp only [List.map_cons]
      rcases hP with rfl | rfl
      · rw [ha]
        exact ⟨_, rfl⟩
      · rw [hb]
        exact ⟨_, rfl⟩

theorem fold_cnt (n a b : ℕ) : ∀ (gs : List Gate) (st : St),
    look st.m a = .cst false → look st.m b = .cst false → a < st.m.length → b < st.m.length →
    (∀ g ∈ gs, Fan g) →
    (gs.foldl (stepS n) st).gs.length + gs.countP (P a b) ≤ st.gs.length + gs.length
  | [], st, _, _, _, _, _ => by simp
  | g :: gs, st, ha, hb, ha', hb', hf => by
      have hg := hf g (by simp)
      have hrest : ∀ g' ∈ gs, Fan g' := fun g' h' => hf g' (by simp [h'])
      rw [List.foldl_cons, List.length_cons]
      have hm : ∃ s, (stepS n st g).m = st.m ++ [s] := by
        unfold stepS
        cases hp : proc g.op (g.inputs.map (look st.m)) with
        | inl s => exact ⟨s, rfl⟩
        | inr p =>
          rcases p with ⟨op', is⟩
          exact ⟨_, rfl⟩
      obtain ⟨s, hs⟩ := hm
      have ha2 : look (stepS n st g).m a = .cst false := by
        rw [hs, look, getD_snoc_lt _ _ _ ha']
        exact ha
      have hb2 : look (stepS n st g).m b = .cst false := by
        rw [hs, look, getD_snoc_lt _ _ _ hb']
        exact hb
      have hl2 : (stepS n st g).m.length = st.m.length + 1 := by
        rw [hs, List.length_append, List.length_singleton]
      have ih := fold_cnt n a b gs (stepS n st g) ha2 hb2 (by omega) (by omega) hrest
      have hle : (stepS n st g).gs.length ≤ st.gs.length + 1 := by
        unfold stepS
        cases hp : proc g.op (g.inputs.map (look st.m)) with
        | inl s => simp
        | inr p =>
          rcases p with ⟨op', is⟩
          simp
      by_cases hP : P a b g = true
      · have hc : (g :: gs).countP (P a b) = gs.countP (P a b) + 1 := by
          simp [List.countP_cons, hP]
        obtain ⟨s', hs'⟩ := P_inl st.m a b g hg ha hb hP
        have heq : (stepS n st g).gs = st.gs := by simp only [stepS, hs']
        rw [hc]
        rw [heq] at ih
        omega
      · have hc : (g :: gs).countP (P a b) = gs.countP (P a b) := by
          simp [List.countP_cons, hP]
        rw [hc]
        omega

theorem getD_ofFn' {α : Type} {m : ℕ} (F : Fin m → α) (d : α) (i : ℕ) (h : i < m) :
    (List.ofFn F).getD i d = F ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

def m0 (n : ℕ) (a b : Fin n) : List Sym :=
  List.ofFn (fun i : Fin n => if i = a ∨ i = b then Sym.cst false else Sym.wire i)

theorem init_inv (n : ℕ) (a b : Fin n) (x : Fin n → Bool) :
    Inv (List.ofFn x) n a b
      (List.ofFn (Function.update (Function.update x a false) b false)) ⟨[], m0 n a b⟩ := by
  refine ⟨by simp, by simp [m0], by simp, ?_, ?_, ?_, ?_, ?_, a.isLt, b.isLt⟩
  · intro i
    simp only [List.foldl_nil]
    by_cases hi : i < n
    · rw [getD_ofFn' _ _ _ hi, look, m0, getD_ofFn' _ _ _ hi]
      by_cases hab : (⟨i, hi⟩ : Fin n) = a ∨ (⟨i, hi⟩ : Fin n) = b
      · rw [if_pos hab]
        rcases hab with h | h
        · rw [h]
          simp [Function.update_apply, Sym.val]
        · rw [h]
          simp [Function.update_apply, Sym.val]
      · rw [if_neg hab]
        push_neg at hab
        show _ = (List.ofFn x).getD i false
        rw [getD_ofFn' _ _ _ hi]
        simp [Function.update_apply, hab.1, hab.2]
    · rw [List.getD_eq_default _ _ (by simp; omega), look,
        List.getD_eq_default _ _ (by simp [m0]; omega)]
      rfl
  · intro i
    simp only [List.foldl_nil]
    by_cases hi : i < n
    · rw [look, m0, getD_ofFn' _ _ _ hi]
      split_ifs
      · trivial
      · show i < (List.ofFn x).length
        simpa using hi
    · rw [look, List.getD_eq_default _ _ (by simp [m0]; omega)]
      trivial
  · rw [look, m0, getD_ofFn' _ _ _ a.isLt]
    simp
  · rw [look, m0, getD_ofFn' _ _ _ b.isLt]
    simp
  · intro g hg
    simp at hg

def outIdx (n : ℕ) (st : St) (o : ℕ) : ℕ :=
  match look st.m o with
  | .wire i => i
  | .cst _ => n + st.gs.length

theorem main (n : ℕ) (C : Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hz : C.eval (List.ofFn fun (_ : Fin n) => false) = false) (a b : Fin n) :
    (C.gates.foldl (stepS n) ⟨[], m0 n a b⟩).gs.length + C.gates.countP (P a b) ≤ C.size ∧
    PEqualNP.MetaComplexity.HasCircuitSize n
      (fun x => C.eval (List.ofFn (Function.update (Function.update x a false) b false)))
      (C.gates.foldl (stepS n) ⟨[], m0 n a b⟩).gs.length := by
  have hF : ∀ g ∈ C.gates, Fan g := hfan
  have hI : ∀ x : Fin n → Bool, Inv (List.ofFn x) n a b
      (C.wires (List.ofFn (Function.update (Function.update x a false) b false)))
      (C.gates.foldl (stepS n) ⟨[], m0 n a b⟩) :=
    fun x => fold_inv (List.ofFn x) n a b C.gates _ _ (init_inv n a b x) hF
  refine ⟨?_, ?_⟩
  · obtain ⟨_, hl0, _, _, _, ha0, hb0, _, ha1, hb1⟩ := init_inv n a b (fun _ => false)
    have := fold_cnt n a b C.gates ⟨[], m0 n a b⟩ ha0 hb0 (by simp [m0]) (by simp [m0]) hF
    simpa [Circuit.size] using this
  · obtain ⟨_, _, _, _, _, _, _, hfanD, _, _⟩ := hI (fun _ => false)
    refine ⟨⟨(C.gates.foldl (stepS n) ⟨[], m0 n a b⟩).gs,
      outIdx n (C.gates.foldl (stepS n) ⟨[], m0 n a b⟩) C.output⟩, hfanD, le_refl _, ?_⟩
    intro x
    obtain ⟨_, _, _, hval, _, _, _, _, _, _⟩ := hI x
    have hVlen := len_fold (C.gates.foldl (stepS n) ⟨[], m0 n a b⟩).gs (List.ofFn x)
    show ((C.gates.foldl (stepS n) ⟨[], m0 n a b⟩).gs.foldl wstep (List.ofFn x)).getD
      (outIdx n (C.gates.foldl (stepS n) ⟨[], m0 n a b⟩) C.output) false =
      (C.wires (List.ofFn (Function.update (Function.update x a false) b false))).getD C.output false
    rw [hval C.output]
    unfold outIdx
    cases hl : look (C.gates.foldl (stepS n) ⟨[], m0 n a b⟩).m C.output with
    | wire i => rfl
    | cst c =>
      cases c
      · rw [List.getD_eq_default _ _ (by rw [hVlen, List.length_ofFn])]
        rfl
      · exfalso
        obtain ⟨_, _, _, hval0, _⟩ := hI (fun _ => false)
        have h1 := hval0 C.output
        rw [hl] at h1
        have h2 : Function.update (Function.update (fun _ : Fin n => false) a false) b false =
            fun _ => false := by
          funext i
          simp [Function.update_apply]
        rw [h2] at h1
        have h3 : C.eval (List.ofFn fun _ : Fin n => false) = true := h1
        rw [hz] at h3
        exact Bool.false_ne_true h3

end PEqualNP.Outside.L_meta_6965

theorem PEqualNP.Outside.L_meta_6965 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.eval (List.ofFn fun (x4 : Fin x1) => Bool.false) = Bool.false →       ∀ (x5 x6 : Fin x1),         have x7 : PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => List.take (bif x7.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x7.inputs;         ∃ (x8 : ℕ), x8 + List.countP (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => (x7 x9).any fun (x10 : ℕ) => x10 == ↑x5 || x10 == ↑x6) x2.gates ≤ x2.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x9 : Fin x1 → Bool) => x2.eval (List.ofFn (Function.update (Function.update x9 x5 Bool.false) x6 Bool.false))) x8 := by
  intro n C hfan hz a b
  dsimp only
  obtain ⟨h1, h2⟩ := PEqualNP.Outside.L_meta_6965.main n C hfan hz a b
  exact ⟨_, h1, h2⟩
