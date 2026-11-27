import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4717

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


theorem getD_sn (l : List Bool) (b : Bool) (t : ℕ) :
    (l ++ [b]).getD t false = if t = l.length then b else l.getD t false := by
  rcases lt_trichotomy t l.length with h | h | h
  · rw [if_neg (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]


def ch {k : ℕ} (B xs : List (Fin k → Bool)) : Prop := ∀ (i : ℕ) (hi : i < xs.length),
  ∃ a ∈ B ++ List.take i xs, ∃ b ∈ B ++ List.take i xs, ∃ (p q : Bool),
    xs[i] = fun t => (a t ^^ p) && (b t ^^ q)

theorem ch_snoc {k : ℕ} (B xs : List (Fin k → Bool)) (v : Fin k → Bool) (h : ch B xs)
    (hv : ∃ a ∈ B ++ xs, ∃ b ∈ B ++ xs, ∃ (p q : Bool), v = fun t => (a t ^^ p) && (b t ^^ q)) :
    ch B (xs ++ [v]) := by
  intro i hi
  by_cases hlt : i < xs.length
  · obtain ⟨a, ha, b, hb, p, q, e⟩ := h i hlt
    refine ⟨a, ?_, b, ?_, p, q, ?_⟩
    · rw [List.take_append_of_le_length hlt.le]; exact ha
    · rw [List.take_append_of_le_length hlt.le]; exact hb
    · rw [List.getElem_append_left hlt]; exact e
  · have hi' : i = xs.length := by simp at hi; omega
    subst hi'
    obtain ⟨a, ha, b, hb, p, q, e⟩ := hv
    refine ⟨a, ?_, b, ?_, p, q, ?_⟩
    · rw [List.take_append_of_le_length le_rfl, List.take_length]; exact ha
    · rw [List.take_append_of_le_length le_rfl, List.take_length]; exact hb
    · rw [← e]; simp

def Rep {k : ℕ} (S : List (Fin k → Bool)) (f : Fin k → Bool) : Prop :=
  ∃ g ∈ S, ∃ s : Bool, ∀ t, f t = (g t ^^ s)

theorem rep_mono {k : ℕ} (S T : List (Fin k → Bool)) (f : Fin k → Bool) (h : ∀ x ∈ S, x ∈ T)
    (hf : Rep S f) : Rep T f := by
  obtain ⟨g, hg, s, e⟩ := hf
  exact ⟨g, h g hg, s, e⟩

theorem rep_not {k : ℕ} (S : List (Fin k → Bool)) (f : Fin k → Bool) (hf : Rep S f) :
    Rep S fun t => !f t := by
  obtain ⟨g, hg, s, e⟩ := hf
  exact ⟨g, hg, !s, fun t => by show (!f t) = _; rw [e]; cases g t <;> cases s <;> rfl⟩

theorem rep_const {k : ℕ} (S : List (Fin k → Bool)) (h0 : (fun _ => false) ∈ S) (c : Bool) :
    Rep S fun _ => c := ⟨_, h0, c, fun t => by simp⟩

theorem rep_two {k : ℕ} (B xs : List (Fin k → Bool)) (hx : ch B xs) (o : GateOp)
    (ho : o = GateOp.and ∨ o = GateOp.or) (f g : Fin k → Bool)
    (hf : Rep (B ++ xs) f) (hg : Rep (B ++ xs) g) :
    ∃ v, ch B (xs ++ [v]) ∧ Rep (B ++ (xs ++ [v])) fun t => o.eval [f t, g t] := by
  obtain ⟨a, ha, p, hp⟩ := hf
  obtain ⟨b, hb, q, hq⟩ := hg
  rcases ho with rfl | rfl
  · refine ⟨fun t => (a t ^^ p) && (b t ^^ q), ch_snoc B xs _ hx ⟨a, ha, b, hb, p, q, rfl⟩,
      _, List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self _)), false, fun t => ?_⟩
    simp [GateOp.eval, hp, hq]
  · refine ⟨fun t => (a t ^^ !p) && (b t ^^ !q), ch_snoc B xs _ hx ⟨a, ha, b, hb, !p, !q, rfl⟩,
      _, List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self _)), true, fun t => ?_⟩
    simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false, hp, hq]
    cases a t <;> cases b t <;> cases p <;> cases q <;> rfl

theorem build {n k : ℕ} (X : Fin n → Fin k → Bool) (gs : List Gate)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) :
    ∃ xs : List (Fin k → Bool), xs.length ≤ List.countP (fun g => !g.op.eval [false]) gs ∧
      ch ((fun _ => false) :: List.ofFn X) xs ∧
      ∀ w, Rep (((fun _ => false) :: List.ofFn X) ++ xs)
        fun t => (run gs (List.ofFn fun i => X i t)).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], by simp, fun i hi => by simp at hi, fun w => ?_⟩
    by_cases hw : w < n
    · refine ⟨X ⟨w, hw⟩, by simp, false, fun t => ?_⟩
      simp [run, List.getD_eq_getElem?_getD, hw]
    · have e : (fun t => (run [] (List.ofFn fun i => X i t)).getD w false) = fun _ => false := by
        funext t
        exact List.getD_eq_default _ _ (by simp [run]; omega)
      rw [e]
      exact rep_const _ (by simp) false
  | append_singleton gs g ih =>
    obtain ⟨xs, h1, h2, h3⟩ := ih fun g' h => hops g' (by simp [h])
    obtain ⟨hop, hlen⟩ := hops g (by simp)
    have main : ∃ hs : List (Fin k → Bool),
        hs.length ≤ List.countP (fun g => !g.op.eval [false]) [g] ∧
        ch ((fun _ => false) :: List.ofFn X) (xs ++ hs) ∧
        Rep (((fun _ => false) :: List.ofFn X) ++ (xs ++ hs)) fun t =>
          g.op.eval (g.inputs.map fun i => (run gs (List.ofFn fun i => X i t)).getD i false) := by
      have triv : Rep (((fun _ => false) :: List.ofFn X) ++ xs) (fun t =>
          g.op.eval (g.inputs.map fun i => (run gs (List.ofFn fun i => X i t)).getD i false)) →
          ∃ hs : List (Fin k → Bool),
        hs.length ≤ List.countP (fun g => !g.op.eval [false]) [g] ∧
        ch ((fun _ => false) :: List.ofFn X) (xs ++ hs) ∧
        Rep (((fun _ => false) :: List.ofFn X) ++ (xs ++ hs)) fun t =>
          g.op.eval (g.inputs.map fun i => (run gs (List.ofFn fun i => X i t)).getD i false) :=
        fun h => ⟨[], by simp, by simpa using h2, by simpa using h⟩
      match hI : g.inputs, hlen with
      | [], _ =>
        rw [hI] at triv
        exact triv (rep_const _ (by simp) (g.op.eval []))
      | [a], _ =>
        rw [hI] at triv
        apply triv
        rcases hop with ho | ho | ho
        · have := h3 a
          simpa [ho, GateOp.eval] using this
        · have := h3 a
          simpa [ho, GateOp.eval] using this
        · have := rep_not _ _ (h3 a)
          simpa [ho, GateOp.eval] using this
      | [a, b], _ =>
        rw [hI] at triv
        by_cases hn : g.op = GateOp.not
        · apply triv
          have := rep_not _ _ (h3 a)
          simpa [hn, GateOp.eval] using this
        · have hao : g.op = GateOp.and ∨ g.op = GateOp.or := by
            rcases hop with h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · exact absurd h hn
          obtain ⟨v, k1, k2⟩ := rep_two _ xs h2 g.op hao _ _ (h3 a) (h3 b)
          refine ⟨[v], ?_, k1, k2⟩
          rcases hao with h | h <;> simp [h, GateOp.eval]
    obtain ⟨hs, k1, k2, k3⟩ := main
    refine ⟨xs ++ hs, ?_, k2, fun w => ?_⟩
    · rw [List.countP_append, List.length_append]
      omega
    · by_cases hw : w = n + gs.length
      · have e : (fun t => (run (gs ++ [g]) (List.ofFn fun i => X i t)).getD w false) = fun t =>
            g.op.eval (g.inputs.map fun i => (run gs (List.ofFn fun i => X i t)).getD i false) := by
          funext t
          rw [run_snoc, getD_sn, if_pos (by rw [run_length, List.length_ofFn, hw])]
        rw [e]
        exact k3
      · have e : (fun t => (run (gs ++ [g]) (List.ofFn fun i => X i t)).getD w false) = fun t =>
            (run gs (List.ofFn fun i => X i t)).getD w false := by
          funext t
          rw [run_snoc, getD_sn, if_neg (by rw [run_length, List.length_ofFn]; exact hw)]
        rw [e]
        refine rep_mono _ _ _ (fun x hx => ?_) (h3 w)
        rcases List.mem_append.1 hx with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_append_left _ h)

end PEqualNP.Outside.L_meta_4717

open PEqualNP.Outside.L_meta_4717 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4717 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin x1 → Fin x2 → Bool),   PEqualNP.MetaComplexity.FanInTwo x3 →     have x6 : List (Fin x2 → Bool) := (fun (x6 : Fin x2) => Bool.false) :: List.ofFn x4;     ∃ (x7 : List (Fin x2 → Bool)), x7.length ≤ List.countP (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => !x8.op.eval [Bool.false]) x3.gates ∧ (∀ (x8 : ℕ) (x9 : x8 < x7.length), ∃ x10 ∈ x6 ++ List.take x8 x7, ∃ x11 ∈ x6 ++ List.take x8 x7, ∃ (x12 : Bool) (x13 : Bool), x7[x8] = fun (x14 : Fin x2) => (x10 x14 ^^ x12) && (x11 x14 ^^ x13)) ∧ ∃ x8 ∈ x6 ++ x7, ∃ (x9 : Bool), ∀ (x10 : Fin x2), x3.eval (List.ofFn fun (x11 : Fin x1) => x4 x11 x10) = (x8 x10 ^^ x9) := by
  intro n k C X hC
  obtain ⟨xs, h1, h2, h3⟩ := build X C.gates fun g hg => by
    obtain ⟨e1, e2⟩ := hC g hg
    exact ⟨by simpa using e1, e2⟩
  exact ⟨xs, h1, h2, h3 C.output⟩
