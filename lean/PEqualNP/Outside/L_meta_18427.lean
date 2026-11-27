import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18427

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem getD_snoc (L : List Bool) (b : Bool) (j : ℕ) :
    (L ++ [b]).getD j false = if j = L.length then b else L.getD j false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h1 | h1
    · rw [List.getD_append _ _ _ _ h1]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem step_prefix (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp only [step]
  rw [List.getD_append _ _ _ _ hi]

theorem step_new (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [step]
  rw [getD_snoc]
  simp

theorem foldl_length (gs : List Gate) : ∀ (w : List Bool),
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; rw [List.foldl_cons, ih, step_length]; simp; omega

theorem foldl_prefix (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih _ _ (by rw [step_length]; omega), step_prefix _ _ _ hi]

def dflt : Gate := ⟨GateOp.or, []⟩

theorem getD_mem (gs : List Gate) (j : ℕ) (hj : j < gs.length) : gs.getD j dflt ∈ gs := by
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

theorem any_congr' {α : Type} (l : List α) (f g : α → Bool) (h : ∀ b ∈ l, f b = g b) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

theorem foldl_reads (gs : List Gate) : ∀ (w : List Bool),
    (∀ g ∈ gs, ∀ i ∈ g.inputs, i < w.length) → ∀ j < gs.length,
    (gs.foldl step w).getD (w.length + j) false =
      (gs.getD j dflt).op.eval ((gs.getD j dflt).inputs.map fun i => w.getD i false) := by
  induction gs with
  | nil => intro w _ j hj; simp at hj
  | cons g gs ih =>
    intro w hr j hj
    rw [List.foldl_cons]
    cases j with
    | zero =>
      rw [Nat.add_zero, foldl_prefix _ _ _ (by rw [step_length]; omega), step_new]
      rfl
    | succ j =>
      simp only [List.length_cons] at hj
      have hl : (step w g).length = w.length + 1 := step_length w g
      have h2 := ih (step w g) (fun g' hg' i hi => by
        have := hr g' (List.mem_cons_of_mem _ hg') i hi; omega) j (by omega)
      rw [show w.length + (j + 1) = (step w g).length + j by omega, h2]
      simp only [List.getD_cons_succ]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact step_prefix _ _ _ (hr _ (List.mem_cons_of_mem _ (getD_mem gs j (by omega))) i hi)

def chainG (W cur : ℕ) : List ℕ → List Gate
  | [] => []
  | b :: rest => ⟨GateOp.or, [cur, b]⟩ :: chainG (W + 1) W rest

def chainOut (W cur : ℕ) : List ℕ → ℕ
  | [] => cur
  | _ :: rest => chainOut (W + 1) W rest

theorem chainG_length (l : List ℕ) : ∀ (W cur : ℕ), (chainG W cur l).length = l.length := by
  induction l with
  | nil => intro W cur; rfl
  | cons b rest ih => intro W cur; simp [chainG, ih]

theorem chainOut_lt (l : List ℕ) : ∀ (W cur : ℕ), cur < W → chainOut W cur l < W + l.length := by
  induction l with
  | nil => intro W cur h; simpa [chainOut] using h
  | cons b rest ih =>
    intro W cur h
    have := ih (W + 1) W (by omega)
    simp only [chainOut, List.length_cons]
    omega

theorem chain_sem (l : List ℕ) : ∀ (W cur : ℕ) (w : List Bool), w.length = W → cur < W →
    (∀ b ∈ l, b < W) →
    ((chainG W cur l).foldl step w).getD (chainOut W cur l) false =
      (w.getD cur false || l.any (fun b => w.getD b false)) := by
  induction l with
  | nil =>
    intro W cur w _ _ _
    simp [chainG, chainOut]
  | cons b rest ih =>
    intro W cur w hw hc hl
    simp only [chainG, chainOut, List.foldl_cons]
    have hlen : (step w ⟨GateOp.or, [cur, b]⟩).length = W + 1 := by rw [step_length, hw]
    rw [ih (W + 1) W _ hlen (by omega) (fun b' hb' => by have := hl b' (by simp [hb']); omega)]
    have hnew : (step w ⟨GateOp.or, [cur, b]⟩).getD W false =
        (w.getD cur false || w.getD b false) := by
      rw [← hw, step_new]; simp [GateOp.eval]
    rw [hnew]
    rw [any_congr' rest _ (fun b' => w.getD b' false)
      (fun b' hb' => step_prefix _ _ _ (by have := hl b' (by simp [hb']); omega))]
    simp only [List.any_cons, Bool.or_assoc]

theorem chainG_mem (l : List ℕ) : ∀ (W cur : ℕ) (g : Gate), g ∈ chainG W cur l →
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction l with
  | nil => intro W cur g hg; simp [chainG] at hg
  | cons b rest ih =>
    intro W cur g hg
    simp only [chainG, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp
    · exact ih _ _ _ hg

def chainsG (W : ℕ) : List (ℕ × List ℕ) → List Gate
  | [] => []
  | p :: rest => chainG W p.1 p.2 ++ chainsG (W + p.2.length) rest

def chainsOut (W : ℕ) : List (ℕ × List ℕ) → List ℕ
  | [] => []
  | p :: rest => chainOut W p.1 p.2 :: chainsOut (W + p.2.length) rest

theorem chainsG_length (ls : List (ℕ × List ℕ)) : ∀ (W : ℕ),
    (chainsG W ls).length = (ls.map fun p => p.2.length).sum := by
  induction ls with
  | nil => intro W; rfl
  | cons p rest ih => intro W; simp [chainsG, chainG_length, ih]

theorem chainsG_mem (ls : List (ℕ × List ℕ)) : ∀ (W : ℕ) (g : Gate), g ∈ chainsG W ls →
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction ls with
  | nil => intro W g hg; simp [chainsG] at hg
  | cons p rest ih =>
    intro W g hg
    simp only [chainsG, List.mem_append] at hg
    rcases hg with hg | hg
    · exact chainG_mem _ _ _ _ hg
    · exact ih _ _ hg

theorem chainsOut_lt (ls : List (ℕ × List ℕ)) : ∀ (W : ℕ), (∀ p ∈ ls, p.1 < W) →
    ∀ o ∈ chainsOut W ls, o < W + (ls.map fun p => p.2.length).sum := by
  induction ls with
  | nil => intro W _ o ho; simp [chainsOut] at ho
  | cons p rest ih =>
    intro W hp o ho
    simp only [chainsOut, List.mem_cons] at ho
    simp only [List.map_cons, List.sum_cons]
    rcases ho with rfl | ho
    · have := chainOut_lt p.2 W p.1 (hp p (by simp))
      omega
    · have := ih (W + p.2.length) (fun q hq => by have := hp q (by simp [hq]); omega) o ho
      omega

theorem chains_sem (ls : List (ℕ × List ℕ)) : ∀ (W : ℕ) (w : List Bool), w.length = W →
    (∀ p ∈ ls, p.1 < W ∧ ∀ b ∈ p.2, b < W) →
    (chainsOut W ls).map (fun o => ((chainsG W ls).foldl step w).getD o false) =
      ls.map (fun p => w.getD p.1 false || p.2.any (fun b => w.getD b false)) := by
  induction ls with
  | nil => intro W w _ _; rfl
  | cons p rest ih =>
    intro W w hw hp
    obtain ⟨hp1, hp2⟩ := hp p (by simp)
    simp only [chainsOut, chainsG, List.map_cons, List.foldl_append]
    set w1 := (chainG W p.1 p.2).foldl step w with hw1
    have l1 : w1.length = W + p.2.length := by rw [hw1, foldl_length, chainG_length, hw]
    have p1 : ∀ i < W, w1.getD i false = w.getD i false := by
      intro i hi; rw [hw1, foldl_prefix _ _ _ (by omega)]
    have hrest : ∀ q ∈ rest, q.1 < W + p.2.length ∧ ∀ b ∈ q.2, b < W + p.2.length := by
      intro q hq
      obtain ⟨h1, h2⟩ := hp q (by simp [hq])
      exact ⟨by omega, fun b hb => by have := h2 b hb; omega⟩
    have hout := chainOut_lt p.2 W p.1 hp1
    rw [foldl_prefix _ _ _ (by rw [l1]; exact hout), hw1, chain_sem p.2 W p.1 w hw hp1 hp2,
      ← hw1, ih (W + p.2.length) w1 l1 hrest]
    congr 1
    apply List.map_congr_left
    intro q hq
    obtain ⟨h1, h2⟩ := hp q (by simp [hq])
    rw [p1 _ h1, any_congr' q.2 _ (fun b => w.getD b false) (fun b hb => p1 b (h2 b hb))]

def thG (W t1 t2 : ℕ) : List ℕ → List Gate
  | [] => []
  | [z] => [⟨GateOp.and, [t1, z]⟩, ⟨GateOp.or, [t2, W]⟩]
  | z :: z' :: rest => [⟨GateOp.and, [t1, z]⟩, ⟨GateOp.or, [t2, W]⟩, ⟨GateOp.or, [t1, z]⟩] ++
      thG (W + 3) (W + 2) (W + 1) (z' :: rest)

def thOut (W t1 t2 : ℕ) : List ℕ → ℕ
  | [] => t2
  | [_] => W + 1
  | _ :: z' :: rest => thOut (W + 3) (W + 2) (W + 1) (z' :: rest)

def stp (p : Bool × Bool) (b : Bool) : Bool × Bool := (p.1 || b, p.2 || (p.1 && b))

theorem th_sem (zs : List ℕ) : ∀ (W t1 t2 : ℕ) (w : List Bool), w.length = W → t1 < W →
    t2 < W → (∀ z ∈ zs, z < W) →
    ((thG W t1 t2 zs).foldl step w).getD (thOut W t1 t2 zs) false =
      ((zs.map fun z => w.getD z false).foldl stp (w.getD t1 false, w.getD t2 false)).2 := by
  induction zs with
  | nil => intro W t1 t2 w _ _ _ _; simp [thG, thOut]
  | cons z tl ih =>
    intro W t1 t2 w hw h1 h2 hz
    have hz0 : z < W := hz z (by simp)
    cases tl with
    | nil =>
      simp only [thG, thOut, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil]
      have l1 : (step w ⟨GateOp.and, [t1, z]⟩).length = W + 1 := by rw [step_length, hw]
      rw [show W + 1 = (step w ⟨GateOp.and, [t1, z]⟩).length by rw [l1], step_new]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
        Bool.or_false]
      rw [step_prefix _ _ _ (by omega), show W = w.length by rw [hw], step_new]
      simp [GateOp.eval, stp]
    | cons z' rest =>
      simp only [thG, thOut, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set w1 := step w ⟨GateOp.and, [t1, z]⟩ with hw1
      set w2 := step w1 ⟨GateOp.or, [t2, W]⟩ with hw2
      set w3 := step w2 ⟨GateOp.or, [t1, z]⟩ with hw3
      have l1 : w1.length = W + 1 := by rw [hw1, step_length, hw]
      have l2 : w2.length = W + 2 := by rw [hw2, step_length, l1]
      have l3 : w3.length = W + 3 := by rw [hw3, step_length, l2]
      have p3 : ∀ i < W, w3.getD i false = w.getD i false := by
        intro i hi
        rw [hw3, step_prefix _ _ _ (by omega), hw2, step_prefix _ _ _ (by omega), hw1,
          step_prefix _ _ _ (by omega)]
      have v0 : w1.getD W false = (w.getD t1 false && w.getD z false) := by
        rw [hw1, show W = w.length by rw [hw], step_new]
        simp [GateOp.eval]
      have v1 : w3.getD (W + 1) false = (w.getD t2 false || (w.getD t1 false && w.getD z false)) := by
        rw [hw3, step_prefix _ _ _ (by omega), hw2, show W + 1 = w1.length by rw [l1], step_new]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
          Bool.or_false]
        rw [step_prefix _ _ _ (by omega), v0]
      have v2 : w3.getD (W + 2) false = (w.getD t1 false || w.getD z false) := by
        have e1 : w2.getD t1 false = w.getD t1 false := by
          rw [hw2, step_prefix _ _ _ (by rw [l1]; omega), hw1, step_prefix _ _ _ (by rw [hw]; omega)]
        have e2 : w2.getD z false = w.getD z false := by
          rw [hw2, step_prefix _ _ _ (by rw [l1]; omega), hw1, step_prefix _ _ _ (by rw [hw]; omega)]
        rw [hw3, show W + 2 = w2.length by rw [l2], step_new]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
          Bool.or_false]
        rw [e1, e2]
      rw [ih (W + 3) (W + 2) (W + 1) w3 l3 (by omega) (by omega)
        (fun y hy => by have := hz y (by simp [hy]); omega)]
      rw [v1, v2]
      have hm : ((z' :: rest).map fun y => w3.getD y false) =
          ((z' :: rest).map fun y => w.getD y false) := by
        apply List.map_congr_left
        intro y hy
        exact p3 y (hz y (by simp [hy]))
      rw [hm]
      simp only [List.map_cons, List.foldl_cons]
      rfl

theorem thG_length (zs : List ℕ) : ∀ (W t1 t2 : ℕ), (thG W t1 t2 zs).length = 3 * zs.length - 1 := by
  induction zs with
  | nil => intro W t1 t2; rfl
  | cons z tl ih =>
    intro W t1 t2
    cases tl with
    | nil => rfl
    | cons z' rest =>
      have h := ih (W + 3) (W + 2) (W + 1)
      simp only [List.length_cons] at h
      simp only [thG, List.length_append, h, List.length_cons, List.length_nil]
      omega

theorem thG_mem (zs : List ℕ) : ∀ (W t1 t2 : ℕ) (g : Gate), g ∈ thG W t1 t2 zs →
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction zs with
  | nil => intro W t1 t2 g hg; simp [thG] at hg
  | cons z tl ih =>
    intro W t1 t2 g hg
    cases tl with
    | nil =>
      simp only [thG, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl <;> simp
    | cons z' rest =>
      simp only [thG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (rfl | rfl | rfl) | hg
      · simp
      · simp
      · simp
      · exact ih _ _ _ _ hg

def t2G (W : ℕ) : List ℕ → List Gate
  | a :: b :: c :: rest => [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [a, b]⟩] ++ thG (W + 2) (W + 1) W (c :: rest)
  | [a, b] => [⟨GateOp.and, [a, b]⟩]
  | _ => []

def t2Out (W : ℕ) : List ℕ → ℕ
  | _ :: _ :: c :: rest => thOut (W + 2) (W + 1) W (c :: rest)
  | _ => W

theorem t2G_length (ws : List ℕ) (W : ℕ) (h : 2 ≤ ws.length) : (t2G W ws).length = 3 * ws.length - 5 := by
  match ws, h with
  | [a, b], _ => rfl
  | a :: b :: c :: rest, _ =>
    simp only [t2G, List.length_append, thG_length, List.length_cons, List.length_nil]
    omega

theorem t2G_mem (ws : List ℕ) (W : ℕ) (g : Gate) (hg : g ∈ t2G W ws) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  match ws, hg with
  | [a, b], hg =>
    simp only [t2G, List.mem_cons, List.not_mem_nil, or_false] at hg
    rw [hg]; simp
  | a :: b :: c :: rest, hg =>
    simp only [t2G, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (rfl | rfl) | hg
    · simp
    · simp
    · exact thG_mem _ _ _ _ _ hg

theorem thOut_eq (zs : List ℕ) : ∀ (W t1 t2 : ℕ), zs ≠ [] → thOut W t1 t2 zs + 2 = W + 3 * zs.length := by
  induction zs with
  | nil => intro W t1 t2 h; exact absurd rfl h
  | cons z tl ih =>
    intro W t1 t2 _
    cases tl with
    | nil => simp only [thOut, List.length_cons, List.length_nil] <;> omega
    | cons z' rest =>
      have := ih (W + 3) (W + 2) (W + 1) (by simp)
      simp only [thOut, List.length_cons] at this ⊢
      omega

theorem t2Out_lt (ws : List ℕ) (W : ℕ) (h : 2 ≤ ws.length) : t2Out W ws < W + (t2G W ws).length := by
  rcases ws with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp at h
  · simp at h
  · simp [t2Out, t2G]
  · have h1 := thOut_eq (c :: rest) (W + 2) (W + 1) W (by simp)
    have h3 : t2Out W (a :: b :: c :: rest) = thOut (W + 2) (W + 1) W (c :: rest) := rfl
    have h4 : (t2G W (a :: b :: c :: rest)).length = 2 + (thG (W + 2) (W + 1) W (c :: rest)).length := by
      simp [t2G] <;> omega
    rw [h3, h4, thG_length]
    simp only [List.length_cons] at h1 ⊢
    omega

theorem t2_sem (ws : List ℕ) (W : ℕ) (w : List Bool) (hw : w.length = W) (h : 2 ≤ ws.length)
    (hws : ∀ z ∈ ws, z < W) :
    ((t2G W ws).foldl step w).getD (t2Out W ws) false =
      ((ws.map fun z => w.getD z false).foldl stp (false, false)).2 := by
  match ws, h, hws with
  | [a, b], _, hws =>
    have ha := hws a (by simp)
    have hb := hws b (by simp)
    simp only [t2G, t2Out, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil]
    rw [show W = w.length by rw [hw], step_new]
    simp [GateOp.eval, stp]
  | a :: b :: c :: rest, _, hws =>
    have ha := hws a (by simp)
    have hb := hws b (by simp)
    simp only [t2G, t2Out, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set w1 := step w ⟨GateOp.and, [a, b]⟩ with hw1
    set w2 := step w1 ⟨GateOp.or, [a, b]⟩ with hw2
    have l1 : w1.length = W + 1 := by rw [hw1, step_length, hw]
    have l2 : w2.length = W + 2 := by rw [hw2, step_length, l1]
    have p2 : ∀ i < W, w2.getD i false = w.getD i false := by
      intro i hi
      rw [hw2, step_prefix _ _ _ (by omega), hw1, step_prefix _ _ _ (by omega)]
    have v0 : w2.getD W false = (w.getD a false && w.getD b false) := by
      rw [hw2, step_prefix _ _ _ (by omega), hw1, show W = w.length by rw [hw], step_new]
      simp [GateOp.eval]
    have v1 : w2.getD (W + 1) false = (w.getD a false || w.getD b false) := by
      rw [hw2, show W + 1 = w1.length by rw [l1], step_new]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
        Bool.or_false]
      rw [hw1, step_prefix _ _ _ (by omega), step_prefix _ _ _ (by omega)]
    rw [th_sem (c :: rest) (W + 2) (W + 1) W w2 l2 (by omega) (by omega)
      (fun y hy => by have := hws y (by simp [hy]); omega)]
    rw [v0, v1]
    have hm : ((c :: rest).map fun y => w2.getD y false) =
        ((c :: rest).map fun y => w.getD y false) := by
      apply List.map_congr_left
      intro y hy
      exact p2 y (hws y (by simp [hy]))
    rw [hm]
    simp only [List.map_cons, List.foldl_cons]
    congr 2
    all_goals simp [stp]

def zG (n : ℕ) : List Gate := (List.range n).map fun k => ⟨GateOp.or, [k, n + k]⟩

def T1 (u v k : ℕ) : Bool := decide (u < k ∨ v < k)
def T2 (u v k : ℕ) : Bool := decide (u < k ∧ v < k ∧ u ≠ v)
def zv (u v k : ℕ) : Bool := decide (k = u) || decide (k = v)

theorem stp_step (u v k : ℕ) : stp (T1 u v k, T2 u v k) (zv u v k) = (T1 u v (k + 1), T2 u v (k + 1)) := by
  unfold stp T1 T2 zv
  simp only [Prod.mk.injEq]
  constructor
  · rw [Bool.eq_iff_iff]; simp; omega
  · rw [Bool.eq_iff_iff]; simp; omega

theorem fold_range (u v : ℕ) (m : ℕ) : ∀ k, ((List.range' k m).map (zv u v)).foldl stp
    (T1 u v k, T2 u v k) = (T1 u v (k + m), T2 u v (k + m)) := by
  induction m with
  | zero => intro k; simp
  | succ m ih =>
    intro k
    rw [List.range'_succ, List.map_cons, List.foldl_cons, stp_step, ih (k + 1)]
    all_goals (congr 2 <;> omega)

theorem t2_range (u v m : ℕ) : (((List.range m).map (zv u v)).foldl stp (false, false)).2 =
    decide (u < m ∧ v < m ∧ u ≠ v) := by
  have h := fold_range u v m 0
  have e1 : T1 u v 0 = false := by simp [T1]
  have e2 : T2 u v 0 = false := by simp [T2]
  rw [e1, e2, Nat.zero_add] at h
  rw [List.range_eq_range', h]
  rfl

theorem oneEach_getD {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) ∧
    (oneEach u v).getD (n + i) false = decide (i = v.val) := by
  unfold oneEach
  constructor
  · rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]
    simp [Fin.ext_iff]
  · rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.add_sub_cancel_left,
      List.getD_eq_getElem _ _ (by simpa using hi)]
    simp [Fin.ext_iff]

theorem oneEach_length {n : ℕ} (u v : Fin n) : (oneEach u v).length = n + n := by
  simp [oneEach]

theorem zG_sem (n : ℕ) (u v : Fin n) (k : ℕ) (hk : k < n) :
    ((zG n).foldl step (oneEach u v)).getD (2 * n + k) false = zv u.val v.val k := by
  have hl := oneEach_length u v
  have hr : ∀ g ∈ zG n, ∀ i ∈ g.inputs, i < (oneEach u v).length := by
    intro g hg i hi
    simp only [zG, List.mem_map, List.mem_range] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega
  have := foldl_reads (zG n) (oneEach u v) hr k (by simp [zG]; exact hk)
  rw [show 2 * n + k = (oneEach u v).length + k by omega, this]
  have hg : (zG n).getD k dflt = ⟨GateOp.or, [k, n + k]⟩ := by
    rw [List.getD_eq_getElem _ _ (by simp [zG]; exact hk)]
    simp [zG]
  rw [hg]
  obtain ⟨e1, e2⟩ := oneEach_getD u v k hk
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
    Bool.or_false, e1, e2, zv]

theorem any_or' (l : List ℕ) (f g : ℕ → Bool) : l.any (fun k => f k || g k) = (l.any f || l.any g) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.any_cons, ih]
    cases f a <;> cases g a <;> simp

theorem rowA (t a c : ℕ) (hc : 0 < c) :
    (decide (a * c = t) || ((List.range' 1 (c - 1)).map fun b => a * c + b).any (fun k => decide (k = t))) =
      decide (a = t / c) := by
  rw [Bool.eq_iff_iff, Bool.or_eq_true, List.any_eq_true, decide_eq_true_iff, decide_eq_true_iff]
  constructor
  · rintro (h | ⟨k, hk, hkt⟩)
    · rw [← h, Nat.mul_div_cancel _ hc]
    · rw [List.mem_map] at hk
      obtain ⟨b, hb, rfl⟩ := hk
      rw [List.mem_range'_1] at hb
      rw [decide_eq_true_iff] at hkt
      rw [← hkt, Nat.add_comm, Nat.add_mul_div_right _ _ hc, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  · intro ht
    have hdm := Nat.div_add_mod t c
    have hm := Nat.mod_lt t hc
    rw [← ht] at hdm
    by_cases h0 : t % c = 0
    · left
      rw [h0, Nat.add_zero] at hdm
      rw [Nat.mul_comm]
      exact hdm
    · right
      refine ⟨a * c + t % c, ?_, ?_⟩
      · rw [List.mem_map]
        exact ⟨t % c, by rw [List.mem_range'_1]; omega, rfl⟩
      · rw [decide_eq_true_iff, Nat.mul_comm]
        exact hdm

theorem colA (t b r c : ℕ) (hc : 0 < c) (hb : b < c) (ht : t < r * c) :
    (decide (b = t) || ((List.range' 1 (r - 1)).map fun a => a * c + b).any (fun k => decide (k = t))) =
      decide (b = t % c) := by
  rw [Bool.eq_iff_iff, Bool.or_eq_true, List.any_eq_true, decide_eq_true_iff, decide_eq_true_iff]
  constructor
  · rintro (h | ⟨k, hk, hkt⟩)
    · rw [← h, Nat.mod_eq_of_lt hb]
    · rw [List.mem_map] at hk
      obtain ⟨a, ha, rfl⟩ := hk
      rw [decide_eq_true_iff] at hkt
      rw [← hkt, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  · intro htm
    have hdm := Nat.div_add_mod t c
    rw [← htm] at hdm
    by_cases h0 : t / c = 0
    · left
      rw [h0, Nat.mul_zero, Nat.zero_add] at hdm
      exact hdm
    · right
      have hlt : t / c < r := (Nat.div_lt_iff_lt_mul hc).mpr ht
      refine ⟨t / c * c + b, ?_, ?_⟩
      · rw [List.mem_map]
        exact ⟨t / c, (List.mem_range'_1).mpr ⟨Nat.pos_of_ne_zero h0, Nat.lt_of_lt_of_le hlt (by omega)⟩, rfl⟩
      · rw [decide_eq_true_iff, Nat.mul_comm]
        exact hdm

theorem row_any (u v a c : ℕ) (hc : 0 < c) :
    (zv u v (a * c) || ((List.range' 1 (c - 1)).map fun b => a * c + b).any (zv u v)) =
      zv (u / c) (v / c) a := by
  unfold zv
  rw [any_or', ← rowA u a c hc, ← rowA v a c hc]
  simp only [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

theorem col_any (u v b r c : ℕ) (hc : 0 < c) (hb : b < c) (hu : u < r * c) (hv : v < r * c) :
    (zv u v b || ((List.range' 1 (r - 1)).map fun a => a * c + b).any (zv u v)) =
      zv (u % c) (v % c) b := by
  unfold zv
  rw [any_or', ← colA u b r c hc hb hu, ← colA v b r c hc hb hv]
  simp only [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

theorem colA' (t b r c : ℕ) (hc : 0 < c) (hb : b < c) (hr : 1 ≤ r) (ht : t < r * c + 1) :
    (decide (b = t) || ((List.range' 1 (r - 1)).map fun a => a * c + b).any (fun k => decide (k = t))) =
      decide (b = if t < r * c then t % c else c) := by
  by_cases h : t < r * c
  · rw [if_pos h]
    exact colA t b r c hc hb h
  · rw [if_neg h]
    have htc : t = r * c := by omega
    subst htc
    have hcr : c ≤ r * c := Nat.le_mul_of_pos_left c (by omega)
    rw [Bool.eq_iff_iff, Bool.or_eq_true, List.any_eq_true, decide_eq_true_iff, decide_eq_true_iff]
    constructor
    · rintro (h1 | ⟨k, hk, hkt⟩)
      · omega
      · rw [List.mem_map] at hk
        obtain ⟨a, ha, rfl⟩ := hk
        rw [List.mem_range'_1] at ha
        rw [decide_eq_true_iff] at hkt
        have h2 : (a + 1) * c ≤ r * c := Nat.mul_le_mul_right c (by omega)
        rw [Nat.succ_mul] at h2
        omega
    · intro h1
      omega

theorem col_any' (u v b r c : ℕ) (hc : 0 < c) (hb : b < c) (hr : 1 ≤ r) (hu : u < r * c + 1) (hv : v < r * c + 1) :
    (zv u v b || ((List.range' 1 (r - 1)).map fun a => a * c + b).any (zv u v)) =
      zv (if u < r * c then u % c else c) (if v < r * c then v % c else c) b := by
  unfold zv
  rw [any_or', ← colA' u b r c hc hb hr hu, ← colA' v b r c hc hb hr hv]
  simp only [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

theorem lastA (t r c : ℕ) (hc : 0 < c) (ht : t < r * c + 1) : decide (r * c = t) = decide (r = t / c) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  constructor
  · intro h
    rw [← h, Nat.mul_div_cancel _ hc]
  · intro h
    by_contra hne
    have hlt : t < r * c := by omega
    have := (Nat.div_lt_iff_lt_mul hc).mpr hlt
    omega

def rowsL (r c : ℕ) : List (ℕ × List ℕ) :=
  (List.range r).map (fun a => (2 * (r * c + 1) + a * c, (List.range' 1 (c - 1)).map fun b => 2 * (r * c + 1) + (a * c + b))) ++
    [(2 * (r * c + 1) + r * c, [])]

def colsL (r c : ℕ) : List (ℕ × List ℕ) :=
  (List.range c).map fun b => (2 * (r * c + 1) + b, (List.range' 1 (r - 1)).map fun a => 2 * (r * c + 1) + (a * c + b))

def roOf (r c : ℕ) : List ℕ := chainsOut (3 * (r * c + 1)) (rowsL r c)
def coOf (r c : ℕ) : List ℕ := chainsOut (3 * (r * c + 1) + r * (c - 1)) (colsL r c)
def WRof (r c : ℕ) : ℕ := 3 * (r * c + 1) + r * (c - 1) + c * (r - 1)
def WCof (r c : ℕ) : ℕ := WRof r c + (t2G (WRof r c) (roOf r c)).length
def WFof (r c : ℕ) : ℕ := WCof r c + (t2G (WCof r c) (coOf r c)).length

def gridC (r c : ℕ) : Circuit :=
  ⟨zG (r * c + 1) ++ chainsG (3 * (r * c + 1)) (rowsL r c) ++ chainsG (3 * (r * c + 1) + r * (c - 1)) (colsL r c) ++
    t2G (WRof r c) (roOf r c) ++ t2G (WCof r c) (coOf r c) ++
    [⟨GateOp.or, [t2Out (WRof r c) (roOf r c), t2Out (WCof r c) (coOf r c)]⟩], WFof r c⟩

theorem idx_lt (a b r c : ℕ) (ha : a < r) (hb : b < c) : a * c + b < r * c := by
  have h1 : (a + 1) * c ≤ r * c := Nat.mul_le_mul_right c ha
  rw [Nat.succ_mul] at h1
  omega

theorem sum_range_const (r k : ℕ) (g : ℕ → ℕ) (h : ∀ a, g a = k) : ((List.range r).map g).sum = r * k := by
  induction r with
  | zero => simp
  | succ r ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp [h, Nat.succ_mul]

theorem rowsL_sum (r c : ℕ) : ((rowsL r c).map fun p => p.2.length).sum = r * (c - 1) := by
  rw [rowsL, List.map_append, List.sum_append, List.map_map]
  rw [sum_range_const r (c - 1) _ (fun a => by simp)]
  simp

theorem colsL_sum (r c : ℕ) : ((colsL r c).map fun p => p.2.length).sum = c * (r - 1) := by
  rw [colsL, List.map_map]
  exact sum_range_const c (r - 1) _ (fun a => by simp)

theorem chainsOut_length (ls : List (ℕ × List ℕ)) : ∀ (W : ℕ), (chainsOut W ls).length = ls.length := by
  induction ls with
  | nil => intro W; rfl
  | cons p rest ih => intro W; simp [chainsOut, ih]

theorem gridC_size (r c : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) :
    (gridC r c).size ≤ 3 * (r * c + 1) + 2 * (r + c) - 8 := by
  have hro : (roOf r c).length = r + 1 := by simp [roOf, chainsOut_length, rowsL]
  have hco : (coOf r c).length = c := by simp [coOf, chainsOut_length, colsL]
  have e1 := t2G_length (roOf r c) (WRof r c) (by omega)
  have e2 := t2G_length (coOf r c) (WCof r c) (by omega)
  rw [hro] at e1
  rw [hco] at e2
  simp only [gridC, Circuit.size, List.length_append, List.length_singleton, chainsG_length, rowsL_sum,
    colsL_sum, e1, e2, zG, List.length_map, List.length_range]
  have m1 : r * (c - 1) + r = r * c := by
    rw [← Nat.mul_succ]; congr 1; omega
  have m2 : c * (r - 1) + c = r * c := by
    rw [← Nat.mul_succ, Nat.mul_comm]; congr 1; omega
  omega

theorem gridC_mono (r c : ℕ) : Monotone2 (gridC r c) := by
  intro g hg
  simp only [gridC, List.mem_append, List.mem_singleton] at hg
  rcases hg with ((((hg | hg) | hg) | hg) | hg) | rfl
  · simp only [zG, List.mem_map, List.mem_range] at hg
    obtain ⟨a, _, rfl⟩ := hg
    simp
  · exact chainsG_mem _ _ _ hg
  · exact chainsG_mem _ _ _ hg
  · exact t2G_mem _ _ _ hg
  · exact t2G_mem _ _ _ hg
  · simp

theorem grid_rep (r c : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) :
    Represents (fun u v : Fin (r * c + 1) => decide (u ≠ v)) (gridC r c) := by
  intro u v
  have hc0 : 0 < c := by omega
  have hr1 : 1 ≤ r := by omega
  have hu := u.isLt
  have hv := v.isLt
  have hNr : r ≤ r * c := Nat.le_mul_of_pos_right r hc0
  have hNc : c ≤ r * c := Nat.le_mul_of_pos_left c (by omega)
  simp only [gridC, Circuit.eval, wires_eq, List.foldl_append, List.foldl_cons, List.foldl_nil]
  set w0 := oneEach u v with hw0
  set w1 := (zG (r * c + 1)).foldl step w0 with hw1
  set w2 := (chainsG (3 * (r * c + 1)) (rowsL r c)).foldl step w1 with hw2
  set w3 := (chainsG (3 * (r * c + 1) + r * (c - 1)) (colsL r c)).foldl step w2 with hw3
  set w4 := (t2G (WRof r c) (roOf r c)).foldl step w3 with hw4
  set w5 := (t2G (WCof r c) (coOf r c)).foldl step w4 with hw5
  have l0 : w0.length = (r * c + 1) + (r * c + 1) := oneEach_length u v
  have l1 : w1.length = 3 * (r * c + 1) := by rw [hw1, foldl_length, l0]; simp [zG]; omega
  have z1 : ∀ k < r * c + 1, w1.getD (2 * (r * c + 1) + k) false = zv u.val v.val k :=
    fun k hk => zG_sem _ u v k hk
  have hrows : ∀ p ∈ rowsL r c, p.1 < 3 * (r * c + 1) ∧ ∀ b ∈ p.2, b < 3 * (r * c + 1) := by
    intro p hp
    simp only [rowsL, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hp
    rcases hp with ⟨a, ha, rfl⟩ | rfl
    · have := idx_lt a 0 r c ha hc0
      refine ⟨by simp only; omega, fun b hb => ?_⟩
      simp only [List.mem_map, List.mem_range'_1] at hb
      obtain ⟨b', hb', rfl⟩ := hb
      have := idx_lt a b' r c ha (by omega)
      omega
    · exact ⟨by simp only; omega, fun b hb => by simp at hb⟩
  have l2 : w2.length = 3 * (r * c + 1) + r * (c - 1) := by
    rw [hw2, foldl_length, chainsG_length, rowsL_sum, l1]
  have p2 : ∀ i < 3 * (r * c + 1), w2.getD i false = w1.getD i false := by
    intro i hi; rw [hw2, foldl_prefix _ _ _ (by omega)]
  have hcols : ∀ p ∈ colsL r c, p.1 < 3 * (r * c + 1) + r * (c - 1) ∧
      ∀ b ∈ p.2, b < 3 * (r * c + 1) + r * (c - 1) := by
    intro p hp
    simp only [colsL, List.mem_map, List.mem_range] at hp
    obtain ⟨b, hb, rfl⟩ := hp
    have := idx_lt 0 b r c (by omega) hb
    refine ⟨by simp only; omega, fun a ha => ?_⟩
    simp only [List.mem_map, List.mem_range'_1] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    have := idx_lt a' b r c (by omega) hb
    omega
  have l3 : w3.length = WRof r c := by
    rw [hw3, foldl_length, chainsG_length, colsL_sum, l2]; rfl
  have p3 : ∀ i < 3 * (r * c + 1) + r * (c - 1), w3.getD i false = w2.getD i false := by
    intro i hi; rw [hw3, foldl_prefix _ _ _ (by omega)]
  have rv2 : (roOf r c).map (fun o => w2.getD o false) = (List.range (r + 1)).map (zv (u.val / c) (v.val / c)) := by
    rw [roOf, hw2, chains_sem (rowsL r c) _ w1 l1 hrows, rowsL, List.map_append, List.map_map,
      List.range_succ, List.map_append]
    congr 1
    · apply List.map_congr_left
      intro a ha
      rw [List.mem_range] at ha
      simp only [Function.comp]
      have h0 := idx_lt a 0 r c ha hc0
      rw [z1 (a * c) (by omega)]
      rw [← row_any u.val v.val a c hc0]
      congr 1
      rw [List.any_map, List.any_map]
      apply any_congr'
      intro b hb
      rw [List.mem_range'_1] at hb
      simp only [Function.comp]
      exact z1 (a * c + b) (by have := idx_lt a b r c ha (by omega); omega)
    · simp only [List.map_cons, List.map_nil, List.any_nil, Bool.or_false]
      rw [z1 (r * c) (by omega)]
      unfold zv
      rw [lastA u.val r c hc0 hu, lastA v.val r c hc0 hv]
  have rv3 : (coOf r c).map (fun o => w3.getD o false) =
      (List.range c).map (zv (if u.val < r * c then u.val % c else c) (if v.val < r * c then v.val % c else c)) := by
    rw [coOf, hw3, chains_sem (colsL r c) _ w2 l2 hcols, colsL, List.map_map]
    apply List.map_congr_left
    intro b hb
    rw [List.mem_range] at hb
    simp only [Function.comp]
    have h0 := idx_lt 0 b r c (by omega) hb
    rw [p2 _ (by omega), z1 b (by omega)]
    rw [← col_any' u.val v.val b r c hc0 hb hr1 hu hv]
    congr 1
    rw [List.any_map, List.any_map]
    apply any_congr'
    intro a ha
    rw [List.mem_range'_1] at ha
    simp only [Function.comp]
    have h1 := idx_lt a b r c (by omega) hb
    rw [p2 _ (by omega)]
    exact z1 (a * c + b) (by omega)
  have hro_len : (roOf r c).length = r + 1 := by simp [roOf, chainsOut_length, rowsL]
  have hco_len : (coOf r c).length = c := by simp [coOf, chainsOut_length, colsL]
  have hro_lt : ∀ o ∈ roOf r c, o < 3 * (r * c + 1) + r * (c - 1) := by
    intro o ho
    have := chainsOut_lt (rowsL r c) (3 * (r * c + 1)) (fun p hp => (hrows p hp).1) o ho
    rw [rowsL_sum] at this
    exact this
  have hco_lt : ∀ o ∈ coOf r c, o < WRof r c := by
    intro o ho
    have := chainsOut_lt (colsL r c) (3 * (r * c + 1) + r * (c - 1)) (fun p hp => (hcols p hp).1) o ho
    rw [colsL_sum] at this
    exact this
  have rv3' : (roOf r c).map (fun o => w3.getD o false) = (List.range (r + 1)).map (zv (u.val / c) (v.val / c)) := by
    rw [← rv2]
    apply List.map_congr_left
    intro o ho
    exact p3 o (hro_lt o ho)
  have hdivu : u.val / c < r + 1 := (Nat.div_lt_iff_lt_mul hc0).mpr (by rw [Nat.succ_mul]; omega)
  have hdivv : v.val / c < r + 1 := (Nat.div_lt_iff_lt_mul hc0).mpr (by rw [Nat.succ_mul]; omega)
  have v4 : w4.getD (t2Out (WRof r c) (roOf r c)) false = decide (u.val / c ≠ v.val / c) := by
    rw [hw4, t2_sem (roOf r c) (WRof r c) w3 l3 (by omega) (fun o ho => by have := hro_lt o ho; simp only [WRof]; omega),
      rv3', t2_range]
    simp [hdivu, hdivv]
  have l4 : w4.length = WCof r c := by rw [hw4, foldl_length, l3]; rfl
  have rv4 : (coOf r c).map (fun o => w4.getD o false) =
      (List.range c).map (zv (if u.val < r * c then u.val % c else c) (if v.val < r * c then v.val % c else c)) := by
    rw [← rv3]
    apply List.map_congr_left
    intro o ho
    rw [hw4, foldl_prefix _ _ _ (by rw [l3]; exact hco_lt o ho)]
  have v5 : w5.getD (t2Out (WCof r c) (coOf r c)) false =
      decide ((if u.val < r * c then u.val % c else c) < c ∧ (if v.val < r * c then v.val % c else c) < c ∧
        (if u.val < r * c then u.val % c else c) ≠ (if v.val < r * c then v.val % c else c)) := by
    rw [hw5, t2_sem (coOf r c) (WCof r c) w4 l4 (by omega) (fun o ho => by
      have := hco_lt o ho; simp only [WCof]; omega), rv4, t2_range]
  have v5' : w5.getD (t2Out (WRof r c) (roOf r c)) false = w4.getD (t2Out (WRof r c) (roOf r c)) false := by
    have := t2Out_lt (roOf r c) (WRof r c) (by omega)
    rw [hw5, foldl_prefix _ _ _ (by rw [l4]; exact this)]
  have l5 : w5.length = WFof r c := by rw [hw5, foldl_length, l4]; rfl
  rw [← l5, step_new]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
  rw [v5', v4, v5]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, ne_eq, Fin.ext_iff]
  have du := Nat.div_add_mod u.val c
  have dv := Nat.div_add_mod v.val c
  have hmu := Nat.mod_lt u.val hc0
  have hmv := Nat.mod_lt v.val hc0
  constructor
  · rintro (h | ⟨h1, h2, h3⟩) heq
    · exact h (by rw [heq])
    · exact h3 (by rw [heq])
  · intro h
    by_cases hd : u.val / c = v.val / c
    · right
      have hu' : u.val < r * c := by
        by_contra hcon
        have hue : u.val = r * c := by omega
        have h4 : u.val / c = r := by rw [hue, Nat.mul_div_cancel _ hc0]
        have hvlt : v.val < r * c := by
          by_contra hcon2
          apply h; omega
        have := (Nat.div_lt_iff_lt_mul hc0).mpr hvlt
        omega
      have hv' : v.val < r * c := by
        by_contra hcon
        have hve : v.val = r * c := by omega
        have h4 : v.val / c = r := by rw [hve, Nat.mul_div_cancel _ hc0]
        have := (Nat.div_lt_iff_lt_mul hc0).mpr hu'
        omega
      rw [if_pos hu', if_pos hv']
      refine ⟨hmu, hmv, fun hm => h ?_⟩
      rw [← du, ← dv, hd, hm]
    · left
      exact hd

end PEqualNP.Outside.L_meta_18427

open PEqualNP.Outside.L_meta_18427 in
theorem PEqualNP.Outside.L_meta_18427 : (∀ r c : ℕ, 2 ≤ r → 2 ≤ c → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin (r * c + 1) => decide (u ≠ v)) (3 * (r * c + 1) + 2 * (r + c) - 8)) := by
  intro r c hr hc
  exact ⟨gridC r c, gridC_mono r c, gridC_size r c hr hc, grid_rep r c hr hc⟩
