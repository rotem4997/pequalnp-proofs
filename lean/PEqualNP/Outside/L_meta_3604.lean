import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3604

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem getD_snoc (l : List Bool) (b : Bool) (t : ℕ) :
    (l ++ [b]).getD t false = if t = l.length then b else l.getD t false := by
  rcases lt_trichotomy t l.length with h | h | h
  · rw [if_neg (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

def Agr (a b : ℕ) (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, i ≠ a → i ≠ b → x.getD i false = y.getD i false

theorem agr_push {a b : ℕ} {x y : List Bool} (h : Agr a b x y) (v : Bool) :
    Agr a b (x ++ [v]) (y ++ [v]) := by
  refine ⟨by simp [h.1], fun i ha hb => ?_⟩
  rw [getD_snoc, getD_snoc, h.1, h.2 i ha hb]

theorem agr_run {a b : ℕ} (gs : List Gate) : ∀ x y : List Bool, Agr a b x y →
    (∀ g ∈ gs, a ∉ g.inputs ∧ b ∉ g.inputs) → Agr a b (run gs x) (run gs y) := by
  induction gs with
  | nil => exact fun x y h _ => h
  | cons g gs ih =>
    intro x y h hg
    obtain ⟨h1, h2⟩ := hg g (by simp)
    have e : (g.inputs.map fun i => x.getD i false) = g.inputs.map fun i => y.getD i false :=
      List.map_congr_left fun i hi => h.2 i (fun hc => h1 (hc ▸ hi)) (fun hc => h2 (hc ▸ hi))
    change Agr a b (run gs (x ++ [_])) (run gs (y ++ [_]))
    rw [e]
    exact ih _ _ (agr_push h _) fun g' hg' => hg g' (by simp [hg'])

theorem agr_mid {a b : ℕ} (pre post : List Gate) (g : Gate) (hg : g.inputs = [a, b])
    (x y : List Bool) (h : Agr a b x y) (ha : a < x.length) (hb : b < x.length)
    (hpre : ∀ g ∈ pre, a ∉ g.inputs ∧ b ∉ g.inputs)
    (hpost : ∀ g ∈ post, a ∉ g.inputs ∧ b ∉ g.inputs)
    (hv : g.op.eval [x.getD a false, x.getD b false] = g.op.eval [y.getD a false, y.getD b false]) :
    Agr a b (run (pre ++ g :: post) x) (run (pre ++ g :: post) y) := by
  have keep : ∀ (gs : List Gate) (z : List Bool) (i : ℕ), i < z.length →
      (run gs z).getD i false = z.getD i false := by
    intro gs
    induction gs with
    | nil => intros; rfl
    | cons g gs ih =>
      intro z i hi
      change (run gs (z ++ [_])).getD i false = _
      rw [ih _ _ (by simp; omega), getD_snoc, if_neg (by omega)]
  have e : ∀ z, run (pre ++ g :: post) z = run post (run pre z ++
      [g.op.eval (g.inputs.map fun i => (run pre z).getD i false)]) := by
    intro z; simp [run, List.foldl_append]
  rw [e, e]
  refine agr_run post _ _ ?_ hpost
  have e2 : g.op.eval (g.inputs.map fun i => (run pre x).getD i false) =
      g.op.eval (g.inputs.map fun i => (run pre y).getD i false) := by
    rw [hg]
    simp only [List.map_cons, List.map_nil]
    rw [keep pre x a ha, keep pre x b hb, keep pre y a (h.1 ▸ ha), keep pre y b (h.1 ▸ hb)]
    exact hv
  rw [e2]
  exact agr_push (agr_run pre x y h hpre) _

def ff (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
    x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def pt (m : ℕ) (i : Fin 9) : Bool := m.testBit i

def wit (a b : Fin 9) (o : Bool → Bool → Bool) (m k : ℕ) : Bool :=
  let z : Fin 9 → Bool := fun i => if i = a then k.testBit 0 else if i = b then k.testBit 1
    else pt m i
  ((pt m 0 || pt m 2) == (z 0 || z 2)) && (o (pt m a) (pt m b) == o (z a) (z b)) &&
    (ff (pt m) != ff z)

theorem wits : ∀ a b : Fin 9, (∃ m : Fin 512, ∃ k : Fin 4, wit a a (fun _ _ => true) m k = true) ∧
    (a ≠ b → (∃ m : Fin 512, ∃ k : Fin 4, wit a b (· && ·) m k = true) ∧
      ∃ m : Fin 512, ∃ k : Fin 4, wit a b (· || ·) m k = true) := by
  decide +kernel

def inl (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 2]

theorem inl_len (x : Fin 9 → Bool) : (inl x).length = 10 := by simp [inl]

theorem inl_get (x : Fin 9 → Bool) (i : Fin 9) : (inl x).getD i false = x i := by
  unfold inl
  rw [List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact i.2),
    List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.2), List.getElem_ofFn]

theorem inl_nine (x : Fin 9 → Bool) : (inl x).getD 9 false = (x 0 || x 2) := by
  have : (List.ofFn x).length = 9 := by simp
  unfold inl
  rw [getD_snoc, if_pos this.symm]

theorem inl_agr (a b : Fin 9) (x y : Fin 9 → Bool) (h : ∀ i, i ≠ a → i ≠ b → x i = y i)
    (h9 : (x 0 || x 2) = (y 0 || y 2)) : Agr a b (inl x) (inl y) := by
  refine ⟨by rw [inl_len, inl_len], fun i ha hb => ?_⟩
  rcases lt_trichotomy i 9 with h1 | h1 | h1
  · have e := inl_get x ⟨i, h1⟩
    have e' := inl_get y ⟨i, h1⟩
    rw [e, e']
    exact h _ (fun hc => ha (by rw [← hc])) (fun hc => hb (by rw [← hc]))
  · subst h1; rw [inl_nine, inl_nine, h9]
  · rw [List.getD_eq_default _ _ (by rw [inl_len]; omega),
      List.getD_eq_default _ _ (by rw [inl_len]; omega)]

theorem use (C : Circuit) (hout : 10 ≤ C.output) (hC : ∀ x, C.eval (inl x) = ff x) (a b : Fin 9)
    (o : Bool → Bool → Bool) (hw : ∃ m : Fin 512, ∃ k : Fin 4, wit a b o m k = true)
    (hagr : ∀ x y : Fin 9 → Bool, Agr a b (inl x) (inl y) → o (x a) (x b) = o (y a) (y b) →
      Agr a b (run C.gates (inl x)) (run C.gates (inl y))) : False := by
  obtain ⟨m, k, h⟩ := hw
  set z : Fin 9 → Bool := fun i => if i = a then (k : ℕ).testBit 0
    else if i = b then (k : ℕ).testBit 1 else pt m i with hz
  have h' : (((pt m 0 || pt m 2) == (z 0 || z 2)) && (o (pt m a) (pt m b) == o (z a) (z b)) &&
      (ff (pt m) != ff z)) = true := h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h'
  obtain ⟨⟨h1, h2⟩, h3⟩ := h'
  have h1' := eq_of_beq h1
  have h2' := eq_of_beq h2
  have hne : ff (pt m) ≠ ff z := by
    intro he
    rw [he] at h3
    simp at h3
  refine hne ?_
  rw [← hC, ← hC]
  have hA := hagr (pt m) z (inl_agr a b (pt m) z (fun i ha hb => by
    simp only [hz]; rw [if_neg ha, if_neg hb]) h1') h2'
  exact hA.2 _ (by have := a.2; omega) (by have := b.2; omega)

end PEqualNP.Outside.L_meta_3604

theorem PEqualNP.Outside.L_meta_3604 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (10 : ℕ) ≤ x1.output →     (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ))]) = (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) x3) →       have x4 : List ℕ := List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates;       (∀ (x5 : Fin (9 : ℕ)), ↑x5 ∈ x4) ∧ ∀ x5 ∈ x1.gates, ∀ (x7 x8 : Fin (9 : ℕ)), x7 ≠ x8 → x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x5.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5.inputs = [↑x7, ↑x8] → (2 : ℕ) ≤ List.count (↑x7) x4 ∨ (2 : ℕ) ≤ List.count (↑x8) x4 := by
  intro C hout hC
  have hC' : ∀ x, C.eval (PEqualNP.Outside.L_meta_3604.inl x) = PEqualNP.Outside.L_meta_3604.ff x := hC
  intro L
  have hL : L = List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs C.gates := rfl
  refine ⟨fun a => ?_, fun g hg a b hab hop hin => ?_⟩
  · by_contra hcon
    rw [hL, List.mem_flatMap] at hcon
    push Not at hcon
    exact PEqualNP.Outside.L_meta_3604.use C hout hC' a a (fun _ _ => true) (PEqualNP.Outside.L_meta_3604.wits a a).1 fun x y h _ =>
      PEqualNP.Outside.L_meta_3604.agr_run C.gates _ _ h fun g hg => ⟨hcon g hg, hcon g hg⟩
  · by_contra hcon
    rw [not_or, not_le, not_le, hL] at hcon
    obtain ⟨c1, c2⟩ := hcon
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
    have hab' : (a : ℕ) ≠ b := fun h => hab (Fin.ext h)
    have none : ∀ c : ℕ, c ∈ [(a : ℕ), (b : ℕ)] →
        List.count c (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs C.gates) < 2 →
        ∀ g' , (g' ∈ pre ∨ g' ∈ post) → c ∉ g'.inputs := by
      intro c hc hcount g' hg' hcg
      rw [hsplit, List.flatMap_append, List.flatMap_cons, List.count_append, List.count_append,
        hin] at hcount
      have h1 : 1 ≤ List.count c [(a : ℕ), (b : ℕ)] := List.one_le_count_iff.2 hc
      rcases hg' with h | h
      · have : 1 ≤ List.count c (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs pre) :=
          List.one_le_count_iff.2 (List.mem_flatMap.2 ⟨g', h, hcg⟩)
        omega
      · have : 1 ≤ List.count c (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs post) :=
          List.one_le_count_iff.2 (List.mem_flatMap.2 ⟨g', h, hcg⟩)
        omega
    have na := none a (by simp) c1
    have nb := none b (by simp) c2
    have mid : ∀ x y : Fin 9 → Bool, PEqualNP.Outside.L_meta_3604.Agr a b (PEqualNP.Outside.L_meta_3604.inl x) (PEqualNP.Outside.L_meta_3604.inl y) →
        g.op.eval [x a, x b] = g.op.eval [y a, y b] →
        PEqualNP.Outside.L_meta_3604.Agr a b (PEqualNP.Outside.L_meta_3604.run C.gates (PEqualNP.Outside.L_meta_3604.inl x)) (PEqualNP.Outside.L_meta_3604.run C.gates (PEqualNP.Outside.L_meta_3604.inl y)) := by
      intro x y h hv
      rw [hsplit]
      refine PEqualNP.Outside.L_meta_3604.agr_mid pre post g hin _ _ h (by rw [PEqualNP.Outside.L_meta_3604.inl_len]; omega)
        (by rw [PEqualNP.Outside.L_meta_3604.inl_len]; omega) (fun g' h => ⟨na g' (Or.inl h), nb g' (Or.inl h)⟩)
        (fun g' h => ⟨na g' (Or.inr h), nb g' (Or.inr h)⟩) ?_
      rw [PEqualNP.Outside.L_meta_3604.inl_get, PEqualNP.Outside.L_meta_3604.inl_get, PEqualNP.Outside.L_meta_3604.inl_get, PEqualNP.Outside.L_meta_3604.inl_get]
      exact hv
    obtain ⟨w1, w2⟩ := (PEqualNP.Outside.L_meta_3604.wits a b).2 hab
    rcases hop with ho | ho
    · refine PEqualNP.Outside.L_meta_3604.use C hout hC' a b (· && ·) w1 fun x y h hv => mid x y h ?_
      rw [ho]
      simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using hv
    · refine PEqualNP.Outside.L_meta_3604.use C hout hC' a b (· || ·) w2 fun x y h hv => mid x y h ?_
      rw [ho]
      simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using hv
