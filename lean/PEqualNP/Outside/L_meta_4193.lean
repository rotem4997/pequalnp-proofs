import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4193

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem run_nil (w : List Bool) : run [] w = w := rfl

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem run_append (gs hs : List Gate) (w : List Bool) : run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) : ∀ w : List Bool, (run gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [run]
  | cons g gs ih =>
    intro w
    rw [run_cons, ih]
    simp
    omega

theorem rd_old (W L : List Bool) (i : ℕ) (h : i < W.length) :
    (W ++ L).getD i false = W.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem rd_new (W L : List Bool) (t : ℕ) :
    (W ++ L).getD (W.length + t) false = L.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem run_old (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega)]
    exact rd_old _ _ _ h

def andBlock (B : ℕ) (a b : ℕ × ℕ × ℕ × ℕ) : List Gate :=
  [⟨GateOp.and, [a.1, b.1]⟩,
   ⟨GateOp.and, [a.2.1, b.1]⟩, ⟨GateOp.and, [a.1, b.2.1]⟩, ⟨GateOp.or, [B + 1, B + 2]⟩,
   ⟨GateOp.and, [a.2.2.1, b.1]⟩, ⟨GateOp.and, [a.1, b.2.2.1]⟩, ⟨GateOp.or, [B + 4, B + 5]⟩,
   ⟨GateOp.and, [a.2.1, b.2.2.1]⟩, ⟨GateOp.and, [a.2.2.1, b.2.1]⟩,
   ⟨GateOp.and, [a.2.2.2, b.1]⟩, ⟨GateOp.and, [a.1, b.2.2.2]⟩,
   ⟨GateOp.or, [B + 7, B + 8]⟩, ⟨GateOp.or, [B + 9, B + 10]⟩, ⟨GateOp.or, [B + 11, B + 12]⟩]

theorem andBlock_run (W : List Bool) (a b : ℕ × ℕ × ℕ × ℕ)
    (h1 : a.1 < W.length) (h2 : a.2.1 < W.length) (h3 : a.2.2.1 < W.length)
    (h4 : a.2.2.2 < W.length) (h5 : b.1 < W.length) (h6 : b.2.1 < W.length)
    (h7 : b.2.2.1 < W.length) (h8 : b.2.2.2 < W.length) :
    let V := run (andBlock W.length a b) W
    V.getD W.length false = (W.getD a.1 false && W.getD b.1 false) ∧
    V.getD (W.length + 3) false =
      ((W.getD a.2.1 false && W.getD b.1 false) || (W.getD a.1 false && W.getD b.2.1 false)) ∧
    V.getD (W.length + 6) false =
      ((W.getD a.2.2.1 false && W.getD b.1 false) || (W.getD a.1 false && W.getD b.2.2.1 false)) ∧
    V.getD (W.length + 13) false =
      (((W.getD a.2.1 false && W.getD b.2.2.1 false) || (W.getD a.2.2.1 false && W.getD b.2.1 false)) ||
       ((W.getD a.2.2.2 false && W.getD b.1 false) || (W.getD a.1 false && W.getD b.2.2.2 false))) := by
  obtain ⟨a1, a2, a3, a4⟩ := a
  obtain ⟨b1, b2, b3, b4⟩ := b
  simp only at h1 h2 h3 h4 h5 h6 h7 h8
  simp only [andBlock, run_cons, run_nil, List.append_assoc, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons,
    List.any_nil, id, Bool.and_true, Bool.or_false,
    rd_old _ _ _ h1, rd_old _ _ _ h2, rd_old _ _ _ h3, rd_old _ _ _ h4,
    rd_old _ _ _ h5, rd_old _ _ _ h6, rd_old _ _ _ h7, rd_old _ _ _ h8, rd_new]
  have e0 : ∀ L : List Bool, (W ++ L).getD W.length false = L.getD 0 false := fun L => rd_new W L 0
  simp only [e0]
  refine ⟨rfl, rfl, rfl, rfl⟩

abbrev T4 := Bool × Bool × Bool × Bool

def dflt : T4 := (false, false, false, false)

def unitA : T4 := (true, false, false, false)

def andT (a b : T4) : T4 :=
  (a.1 && b.1, (a.2.1 && b.1) || (a.1 && b.2.1), (a.2.2.1 && b.1) || (a.1 && b.2.2.1),
   ((a.2.1 && b.2.2.1) || (a.2.2.1 && b.2.1)) || ((a.2.2.2 && b.1) || (a.1 && b.2.2.2)))

def orT (a b : T4) : T4 :=
  (a.1 || b.1, a.2.1 || b.2.1, a.2.2.1 || b.2.2.1, a.2.2.2 || b.2.2.2)

def semStep (T : List T4) (g : Gate) : List T4 :=
  T ++ [match g.op with
    | GateOp.and => (g.inputs.map fun i => T.getD i dflt).foldl andT unitA
    | GateOp.or => (g.inputs.map fun i => T.getD i dflt).foldl orT dflt
    | _ => dflt]

def sem0 (n : ℕ) (X Y : List Bool) : List T4 :=
  (List.range n).map fun i => (false, X.getD i false, Y.getD i false, false)

def sem (n : ℕ) (X Y : List Bool) (gs : List Gate) : List T4 :=
  gs.foldl semStep (sem0 n X Y)

theorem sem_snoc (n : ℕ) (X Y : List Bool) (gs : List Gate) (g : Gate) :
    sem n X Y (gs ++ [g]) = semStep (sem n X Y gs) g := by
  simp [sem, List.foldl_append]

theorem sem_length (n : ℕ) (X Y : List Bool) (gs : List Gate) :
    (sem n X Y gs).length = n + gs.length := by
  induction gs using List.reverseRec with
  | nil => simp [sem, sem0]
  | append_singleton gs g ih =>
    rw [sem_snoc]
    simp [semStep, ih]
    omega

theorem run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs ++ [g]) w = run gs w ++ [g.op.eval (g.inputs.map fun i => (run gs w).getD i false)] := by
  rw [run_append]
  rfl

def Snd (n : ℕ) (X Y : List Bool) (t : T4) (F : List Bool → Bool) : Prop :=
  (t.1 = true → ∀ z : List Bool, z.length = n → F z = true) ∧
  (t.2.1 = true → ∃ u, X.getD u false = true ∧
    ∀ z : List Bool, z.length = n → z.getD u false = true → F z = true) ∧
  (t.2.2.1 = true → ∃ u, Y.getD u false = true ∧
    ∀ z : List Bool, z.length = n → z.getD u false = true → F z = true) ∧
  (t.2.2.2 = true → ∃ u v, X.getD u false = true ∧ Y.getD v false = true ∧
    ∀ z : List Bool, z.length = n → z.getD u false = true → z.getD v false = true → F z = true)

theorem snd_dflt (n : ℕ) (X Y : List Bool) (F : List Bool → Bool) : Snd n X Y dflt F := by
  simp [Snd, dflt]

theorem snd_unit (n : ℕ) (X Y : List Bool) : Snd n X Y unitA (fun _ => true) := by
  simp [Snd, unitA]

theorem snd_congr (n : ℕ) (X Y : List Bool) (t : T4) (F F' : List Bool → Bool)
    (h : Snd n X Y t F) (e : ∀ z : List Bool, z.length = n → F z = F' z) : Snd n X Y t F' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ht z hz
    rw [← e z hz]
    exact h1 ht z hz
  · intro ht
    obtain ⟨u, hu, hF⟩ := h2 ht
    exact ⟨u, hu, fun z hz hzu => by rw [← e z hz]; exact hF z hz hzu⟩
  · intro ht
    obtain ⟨u, hu, hF⟩ := h3 ht
    exact ⟨u, hu, fun z hz hzu => by rw [← e z hz]; exact hF z hz hzu⟩
  · intro ht
    obtain ⟨u, v, hu, hv, hF⟩ := h4 ht
    exact ⟨u, v, hu, hv, fun z hz hzu hzv => by rw [← e z hz]; exact hF z hz hzu hzv⟩

theorem snd_or (n : ℕ) (X Y : List Bool) (a b : T4) (Fa Fb : List Bool → Bool)
    (ha : Snd n X Y a Fa) (hb : Snd n X Y b Fb) :
    Snd n X Y (orT a b) (fun z => Fa z || Fb z) := by
  obtain ⟨a1, a2, a3, a4⟩ := ha
  obtain ⟨b1, b2, b3, b4⟩ := hb
  simp only [Snd, orT, Bool.or_eq_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (h | h)
    · exact fun z hz => Or.inl (a1 h z hz)
    · exact fun z hz => Or.inr (b1 h z hz)
  · rintro (h | h)
    · obtain ⟨u, hu, hF⟩ := a2 h
      exact ⟨u, hu, fun z hz hzu => Or.inl (hF z hz hzu)⟩
    · obtain ⟨u, hu, hF⟩ := b2 h
      exact ⟨u, hu, fun z hz hzu => Or.inr (hF z hz hzu)⟩
  · rintro (h | h)
    · obtain ⟨u, hu, hF⟩ := a3 h
      exact ⟨u, hu, fun z hz hzu => Or.inl (hF z hz hzu)⟩
    · obtain ⟨u, hu, hF⟩ := b3 h
      exact ⟨u, hu, fun z hz hzu => Or.inr (hF z hz hzu)⟩
  · rintro (h | h)
    · obtain ⟨u, v, hu, hv, hF⟩ := a4 h
      exact ⟨u, v, hu, hv, fun z hz hzu hzv => Or.inl (hF z hz hzu hzv)⟩
    · obtain ⟨u, v, hu, hv, hF⟩ := b4 h
      exact ⟨u, v, hu, hv, fun z hz hzu hzv => Or.inr (hF z hz hzu hzv)⟩

theorem snd_and (n : ℕ) (X Y : List Bool) (a b : T4) (Fa Fb : List Bool → Bool)
    (ha : Snd n X Y a Fa) (hb : Snd n X Y b Fb) :
    Snd n X Y (andT a b) (fun z => Fa z && Fb z) := by
  obtain ⟨a1, a2, a3, a4⟩ := ha
  obtain ⟨b1, b2, b3, b4⟩ := hb
  simp only [Snd, andT, Bool.or_eq_true, Bool.and_eq_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨h, k⟩
    exact fun z hz => ⟨a1 h z hz, b1 k z hz⟩
  · rintro (⟨h, k⟩ | ⟨h, k⟩)
    · obtain ⟨u, hu, hF⟩ := a2 h
      exact ⟨u, hu, fun z hz hzu => ⟨hF z hz hzu, b1 k z hz⟩⟩
    · obtain ⟨u, hu, hF⟩ := b2 k
      exact ⟨u, hu, fun z hz hzu => ⟨a1 h z hz, hF z hz hzu⟩⟩
  · rintro (⟨h, k⟩ | ⟨h, k⟩)
    · obtain ⟨u, hu, hF⟩ := a3 h
      exact ⟨u, hu, fun z hz hzu => ⟨hF z hz hzu, b1 k z hz⟩⟩
    · obtain ⟨u, hu, hF⟩ := b3 k
      exact ⟨u, hu, fun z hz hzu => ⟨a1 h z hz, hF z hz hzu⟩⟩
  · rintro ((⟨h, k⟩ | ⟨h, k⟩) | (⟨h, k⟩ | ⟨h, k⟩))
    · obtain ⟨u, hu, hF⟩ := a2 h
      obtain ⟨v, hv, hG⟩ := b3 k
      exact ⟨u, v, hu, hv, fun z hz hzu hzv => ⟨hF z hz hzu, hG z hz hzv⟩⟩
    · obtain ⟨v, hv, hF⟩ := a3 h
      obtain ⟨u, hu, hG⟩ := b2 k
      exact ⟨u, v, hu, hv, fun z hz hzu hzv => ⟨hF z hz hzv, hG z hz hzu⟩⟩
    · obtain ⟨u, v, hu, hv, hF⟩ := a4 h
      exact ⟨u, v, hu, hv, fun z hz hzu hzv => ⟨hF z hz hzu hzv, b1 k z hz⟩⟩
    · obtain ⟨u, v, hu, hv, hF⟩ := b4 k
      exact ⟨u, v, hu, hv, fun z hz hzu hzv => ⟨a1 h z hz, hF z hz hzu hzv⟩⟩

theorem snd_foldl_and (n : ℕ) (X Y : List Bool) (Tf : ℕ → T4) (Ff : ℕ → List Bool → Bool)
    (h : ∀ i, Snd n X Y (Tf i) (Ff i)) (l : List ℕ) :
    ∀ (acc : T4) (Facc : List Bool → Bool), Snd n X Y acc Facc →
      Snd n X Y ((l.map Tf).foldl andT acc)
        (fun z => Facc z && (l.map fun i => Ff i z).all id) := by
  induction l with
  | nil =>
    intro acc Facc hacc
    exact snd_congr n X Y _ _ _ hacc (fun z _ => by simp)
  | cons i l ih =>
    intro acc Facc hacc
    have := ih (andT acc (Tf i)) (fun z => Facc z && Ff i z) (snd_and n X Y _ _ _ _ hacc (h i))
    exact snd_congr n X Y _ _ _ this (fun z _ => by simp [Bool.and_assoc])

theorem snd_foldl_or (n : ℕ) (X Y : List Bool) (Tf : ℕ → T4) (Ff : ℕ → List Bool → Bool)
    (h : ∀ i, Snd n X Y (Tf i) (Ff i)) (l : List ℕ) :
    ∀ (acc : T4) (Facc : List Bool → Bool), Snd n X Y acc Facc →
      Snd n X Y ((l.map Tf).foldl orT acc)
        (fun z => Facc z || (l.map fun i => Ff i z).any id) := by
  induction l with
  | nil =>
    intro acc Facc hacc
    exact snd_congr n X Y _ _ _ hacc (fun z _ => by simp)
  | cons i l ih =>
    intro acc Facc hacc
    have := ih (orT acc (Tf i)) (fun z => Facc z || Ff i z) (snd_or n X Y _ _ _ _ hacc (h i))
    exact snd_congr n X Y _ _ _ this (fun z _ => by simp [Bool.or_assoc])

theorem semStep_old (T : List T4) (g : Gate) (w : ℕ) (hw : w < T.length) :
    (semStep T g).getD w dflt = T.getD w dflt := by
  unfold semStep
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hw]

theorem semStep_new (T : List T4) (g : Gate) :
    (semStep T g).getD T.length dflt =
      (match g.op with
        | GateOp.and => (g.inputs.map fun i => T.getD i dflt).foldl andT unitA
        | GateOp.or => (g.inputs.map fun i => T.getD i dflt).foldl orT dflt
        | _ => dflt) := by
  unfold semStep
  simp [List.getD_eq_getElem?_getD]

theorem semStep_big (T : List T4) (g : Gate) (w : ℕ) (hw : T.length < w) :
    (semStep T g).getD w dflt = dflt := by
  apply List.getD_eq_default
  unfold semStep
  simp
  omega

theorem run_new (gs : List Gate) (g : Gate) (z : List Bool) :
    (run (gs ++ [g]) z).getD (z.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (run gs z).getD i false) := by
  rw [run_snoc]
  have := rd_new (run gs z) [g.op.eval (g.inputs.map fun i => (run gs z).getD i false)] 0
  rw [run_length, Nat.add_zero] at this
  rw [this]
  rfl

theorem sem_sound (n : ℕ) (X Y : List Bool) (gs : List Gate) :
    ∀ w, Snd n X Y ((sem n X Y gs).getD w dflt) (fun z => (run gs z).getD w false) := by
  induction gs using List.reverseRec with
  | nil =>
    intro w
    by_cases hw : w < n
    · have e : (sem n X Y []).getD w dflt = (false, X.getD w false, Y.getD w false, false) := by
        simp [sem, sem0, List.getD_eq_getElem?_getD, hw]
      rw [e]
      refine ⟨by simp, ?_, ?_, by simp⟩
      · intro h
        exact ⟨w, h, fun z _ hz => hz⟩
      · intro h
        exact ⟨w, h, fun z _ hz => hz⟩
    · have e : (sem n X Y []).getD w dflt = dflt := by
        apply List.getD_eq_default
        simp [sem, sem0]
        omega
      rw [e]
      exact snd_dflt n X Y _
  | append_singleton gs g ih =>
    intro w
    have hlen := sem_length n X Y gs
    rw [sem_snoc]
    rcases Nat.lt_trichotomy w (n + gs.length) with hw | hw | hw
    · rw [semStep_old _ _ _ (by omega)]
      refine snd_congr n X Y _ _ _ (ih w) (fun z hz => ?_)
      rw [run_snoc]
      exact (rd_old _ _ _ (by rw [run_length]; omega)).symm
    · have e := semStep_new (sem n X Y gs) g
      rw [hlen, ← hw] at e
      rw [e]
      have key : ∀ z : List Bool, z.length = n → (run (gs ++ [g]) z).getD w false =
          g.op.eval (g.inputs.map fun i => (run gs z).getD i false) := by
        intro z hz
        have := run_new gs g z
        rw [hz, ← hw] at this
        exact this
      cases hop : g.op with
      | and =>
        refine snd_congr n X Y _ _ _
          (snd_foldl_and n X Y _ _ ih g.inputs unitA _ (snd_unit n X Y)) (fun z hz => ?_)
        rw [key z hz, hop]
        simp [GateOp.eval]
      | or =>
        refine snd_congr n X Y _ _ _
          (snd_foldl_or n X Y _ _ ih g.inputs dflt (fun _ => false) (snd_dflt n X Y _))
          (fun z hz => ?_)
        rw [key z hz, hop]
        simp [GateOp.eval]
      | not => exact snd_dflt n X Y _
      | mod m => exact snd_dflt n X Y _
      | maj => exact snd_dflt n X Y _
    · rw [semStep_big _ _ _ (by omega)]
      exact snd_dflt n X Y _

theorem mem_foldl_insertNew (L : List (List ℕ)) :
    ∀ (acc : List (List ℕ)) (c : List ℕ), c ∈ L.foldl insertNew acc ↔ c ∈ acc ∨ c ∈ L := by
  induction L with
  | nil => intro acc c; simp
  | cons v L ih =>
    intro acc c
    rw [List.foldl_cons, ih]
    unfold insertNew
    by_cases hv : v ∈ acc
    · rw [if_pos hv]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rintro (h | h)
        · exact Or.inl h
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inl hv
          · exact Or.inr h
    · rw [if_neg hv]
      simp only [List.mem_append, List.mem_singleton, List.mem_cons]
      tauto

theorem mem_andStep (k : ℕ) (A B : List (List ℕ)) (c : List ℕ) :
    c ∈ andStep k A B ↔ ∃ u ∈ A, ∃ v ∈ B, c = capAdd k u v := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp only [List.not_mem_nil, false_or, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨u, hu, v, hv, rfl⟩

def rvStep (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List (List ℕ)) :=
  R ++ [match g.op with
    | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
    | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep 1) [S.map fun _ => 0]
    | _ => []]

def rv (n : ℕ) (S : List ℕ) (gs : List Gate) : List (List (List ℕ)) :=
  gs.foldl (rvStep S) ((List.range n).map (leafVectors S 1))

theorem rv_eq (C : Circuit) (n : ℕ) (S : List ℕ) : readVectors C n S 1 = rv n S C.gates := rfl

theorem rv_snoc (n : ℕ) (S : List ℕ) (gs : List Gate) (g : Gate) :
    rv n S (gs ++ [g]) = rvStep S (rv n S gs) g := by
  simp [rv, List.foldl_append]

theorem rv_length (n : ℕ) (S : List ℕ) (gs : List Gate) : (rv n S gs).length = n + gs.length := by
  induction gs using List.reverseRec with
  | nil => simp [rv]
  | append_singleton gs g ih =>
    rw [rv_snoc]
    simp [rvStep, ih]
    omega

theorem rvStep_old (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) (w : ℕ) (hw : w < R.length) :
    (rvStep S R g).getD w [] = R.getD w [] := by
  unfold rvStep
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hw]

theorem rvStep_new (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) :
    (rvStep S R g).getD R.length [] =
      (match g.op with
        | GateOp.or =>
          (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
        | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep 1) [S.map fun _ => 0]
        | _ => []) := by
  unfold rvStep
  simp [List.getD_eq_getElem?_getD]

theorem rvStep_big (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) (w : ℕ) (hw : R.length < w) :
    (rvStep S R g).getD w [] = [] := by
  apply List.getD_eq_default
  unfold rvStep
  simp
  omega

def Cmp (X Y : List Bool) (a b : ℕ) (t : T4) (c : List ℕ) : Prop :=
  ∃ c0 c1 : ℕ, c = [c0, c1] ∧
    (c0 = 0 → c1 = 0 → t.1 = true) ∧
    (c0 = 1 → c1 = 0 →
      (X.getD a false = true → t.2.1 = true) ∧ (Y.getD a false = true → t.2.2.1 = true)) ∧
    (c0 = 0 → c1 = 1 →
      (X.getD b false = true → t.2.1 = true) ∧ (Y.getD b false = true → t.2.2.1 = true)) ∧
    (c0 = 1 → c1 = 1 →
      (X.getD a false = true ∧ Y.getD b false = true ∨
        X.getD b false = true ∧ Y.getD a false = true) → t.2.2.2 = true)

theorem cmp_orL (X Y : List Bool) (a b : ℕ) (t s : T4) (c : List ℕ) (h : Cmp X Y a b t c) :
    Cmp X Y a b (orT t s) c := by
  obtain ⟨c0, c1, rfl, h1, h2, h3, h4⟩ := h
  refine ⟨c0, c1, rfl, ?_, ?_, ?_, ?_⟩
  · intro e0 e1
    simp [orT, h1 e0 e1]
  · intro e0 e1
    exact ⟨fun hx => by simp [orT, (h2 e0 e1).1 hx], fun hy => by simp [orT, (h2 e0 e1).2 hy]⟩
  · intro e0 e1
    exact ⟨fun hx => by simp [orT, (h3 e0 e1).1 hx], fun hy => by simp [orT, (h3 e0 e1).2 hy]⟩
  · intro e0 e1 hxy
    simp [orT, h4 e0 e1 hxy]

theorem cmp_orR (X Y : List Bool) (a b : ℕ) (t s : T4) (c : List ℕ) (h : Cmp X Y a b t c) :
    Cmp X Y a b (orT s t) c := by
  obtain ⟨c0, c1, rfl, h1, h2, h3, h4⟩ := h
  refine ⟨c0, c1, rfl, ?_, ?_, ?_, ?_⟩
  · intro e0 e1
    simp [orT, h1 e0 e1]
  · intro e0 e1
    exact ⟨fun hx => by simp [orT, (h2 e0 e1).1 hx], fun hy => by simp [orT, (h2 e0 e1).2 hy]⟩
  · intro e0 e1
    exact ⟨fun hx => by simp [orT, (h3 e0 e1).1 hx], fun hy => by simp [orT, (h3 e0 e1).2 hy]⟩
  · intro e0 e1 hxy
    simp [orT, h4 e0 e1 hxy]

theorem capAdd_pair (u0 u1 v0 v1 : ℕ) :
    capAdd 1 [u0, u1] [v0, v1] = [min (u0 + v0) 2, min (u1 + v1) 2] := rfl

set_option maxHeartbeats 2000000 in
theorem cmp_and (X Y : List Bool) (a b : ℕ) (ta tb : T4) (u v : List ℕ)
    (hu : Cmp X Y a b ta u) (hv : Cmp X Y a b tb v) :
    Cmp X Y a b (andT ta tb) (capAdd 1 u v) := by
  obtain ⟨u0, u1, rfl, hu1, hu2, hu3, hu4⟩ := hu
  obtain ⟨v0, v1, rfl, hv1, hv2, hv3, hv4⟩ := hv
  rw [capAdd_pair]
  unfold Cmp
  refine ⟨_, _, rfl, ?_, ?_, ?_, ?_⟩
  · intro h0 h1
    have hz : u0 = 0 ∧ v0 = 0 ∧ u1 = 0 ∧ v1 = 0 := by omega
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hz
    simp [andT, hu1 rfl rfl, hv1 rfl rfl]
  · intro h0 h1
    have hz : u1 = 0 ∧ v1 = 0 := by omega
    obtain ⟨rfl, rfl⟩ := hz
    have hs : (u0 = 1 ∧ v0 = 0) ∨ (u0 = 0 ∧ v0 = 1) := by omega
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have ha := hu2 rfl rfl
      have hb := hv1 rfl rfl
      exact ⟨fun hx => by simp [andT, ha.1 hx, hb], fun hy => by simp [andT, ha.2 hy, hb]⟩
    · have ha := hu1 rfl rfl
      have hb := hv2 rfl rfl
      exact ⟨fun hx => by simp [andT, hb.1 hx, ha], fun hy => by simp [andT, hb.2 hy, ha]⟩
  · intro h0 h1
    have hz : u0 = 0 ∧ v0 = 0 := by omega
    obtain ⟨rfl, rfl⟩ := hz
    have hs : (u1 = 1 ∧ v1 = 0) ∨ (u1 = 0 ∧ v1 = 1) := by omega
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have ha := hu3 rfl rfl
      have hb := hv1 rfl rfl
      exact ⟨fun hx => by simp [andT, ha.1 hx, hb], fun hy => by simp [andT, ha.2 hy, hb]⟩
    · have ha := hu1 rfl rfl
      have hb := hv3 rfl rfl
      exact ⟨fun hx => by simp [andT, hb.1 hx, ha], fun hy => by simp [andT, hb.2 hy, ha]⟩
  · intro h0 h1 hxy
    have hs : (u0 = 1 ∧ v0 = 0) ∨ (u0 = 0 ∧ v0 = 1) := by omega
    have hr : (u1 = 1 ∧ v1 = 0) ∨ (u1 = 0 ∧ v1 = 1) := by omega
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [andT, hu4 rfl rfl hxy, hv1 rfl rfl]
    · rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · simp [andT, (hu2 rfl rfl).1 hx, (hv3 rfl rfl).2 hy]
      · simp [andT, (hu2 rfl rfl).2 hy, (hv3 rfl rfl).1 hx]
    · rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · simp [andT, (hu3 rfl rfl).2 hy, (hv2 rfl rfl).1 hx]
      · simp [andT, (hu3 rfl rfl).1 hx, (hv2 rfl rfl).2 hy]
    · simp [andT, hu1 rfl rfl, hv4 rfl rfl hxy]

theorem cmp_foldl_or (X Y : List Bool) (a b : ℕ) (Tf : ℕ → T4) (Rf : ℕ → List (List ℕ))
    (h : ∀ i, ∀ c ∈ Rf i, Cmp X Y a b (Tf i) c) (l : List ℕ) :
    ∀ (acc : T4) (accV : List (List ℕ)), (∀ c ∈ accV, Cmp X Y a b acc c) →
      ∀ c ∈ (l.map Rf).foldl (fun acc A => A.foldl insertNew acc) accV,
        Cmp X Y a b ((l.map Tf).foldl orT acc) c := by
  induction l with
  | nil =>
    intro acc accV hacc c hc
    exact hacc c hc
  | cons i l ih =>
    intro acc accV hacc c hc
    simp only [List.map_cons, List.foldl_cons] at hc ⊢
    refine ih (orT acc (Tf i)) _ ?_ c hc
    intro c' hc'
    rcases (mem_foldl_insertNew _ _ _).1 hc' with h' | h'
    · exact cmp_orL X Y a b _ _ _ (hacc c' h')
    · exact cmp_orR X Y a b _ _ _ (h i c' h')

theorem cmp_foldl_and (X Y : List Bool) (a b : ℕ) (Tf : ℕ → T4) (Rf : ℕ → List (List ℕ))
    (h : ∀ i, ∀ c ∈ Rf i, Cmp X Y a b (Tf i) c) (l : List ℕ) :
    ∀ (acc : T4) (accV : List (List ℕ)), (∀ c ∈ accV, Cmp X Y a b acc c) →
      ∀ c ∈ (l.map Rf).foldl (andStep 1) accV, Cmp X Y a b ((l.map Tf).foldl andT acc) c := by
  induction l with
  | nil =>
    intro acc accV hacc c hc
    exact hacc c hc
  | cons i l ih =>
    intro acc accV hacc c hc
    simp only [List.map_cons, List.foldl_cons] at hc ⊢
    refine ih (andT acc (Tf i)) _ ?_ c hc
    intro c' hc'
    obtain ⟨u, hu, v, hv, rfl⟩ := (mem_andStep _ _ _ _).1 hc'
    exact cmp_and X Y a b _ _ _ _ (hacc u hu) (h i v hv)

theorem sem_nil_lt (n : ℕ) (X Y : List Bool) (w : ℕ) (hw : w < n) :
    (sem n X Y []).getD w dflt = (false, X.getD w false, Y.getD w false, false) := by
  simp [sem, sem0, List.getD_eq_getElem?_getD, hw]

theorem sem_complete (n : ℕ) (X Y : List Bool) (a b : ℕ) (hab : a ≠ b) (gs : List Gate) :
    ∀ w, ∀ c ∈ (rv n [a, b] gs).getD w [], Cmp X Y a b ((sem n X Y gs).getD w dflt) c := by
  induction gs using List.reverseRec with
  | nil =>
    intro w c hc
    by_cases hw : w < n
    · have e : (rv n [a, b] []).getD w [] = leafVectors [a, b] 1 w := by
        simp [rv, List.getD_eq_getElem?_getD, hw]
      rw [e] at hc
      rw [sem_nil_lt n X Y w hw]
      unfold leafVectors at hc
      by_cases h1 : w = a
      · subst h1
        have hba : ¬ b = w := fun h => hab h.symm
        simp [hba] at hc
        subst hc
        exact ⟨1, 0, rfl, by simp, fun _ _ => ⟨fun hx => hx, fun hy => hy⟩, by simp, by simp⟩
      · by_cases h2 : w = b
        · subst h2
          have haw : ¬ a = w := fun h => h1 h.symm
          simp [haw, h1] at hc
          subst hc
          exact ⟨0, 1, rfl, by simp, by simp, fun _ _ => ⟨fun hx => hx, fun hy => hy⟩, by simp⟩
        · simp [h1, h2] at hc
    · have e : (rv n [a, b] []).getD w [] = [] := by
        apply List.getD_eq_default
        simp [rv]
        omega
      rw [e] at hc
      simp at hc
  | append_singleton gs g ih =>
    intro w c hc
    have hlen := sem_length n X Y gs
    have rlen := rv_length n [a, b] gs
    rw [rv_snoc] at hc
    rw [sem_snoc]
    rcases Nat.lt_trichotomy w (n + gs.length) with hw | hw | hw
    · rw [rvStep_old _ _ _ _ (by omega)] at hc
      rw [semStep_old _ _ _ (by omega)]
      exact ih w c hc
    · have e := semStep_new (sem n X Y gs) g
      rw [hlen, ← hw] at e
      have e' := rvStep_new [a, b] (rv n [a, b] gs) g
      rw [rlen, ← hw] at e'
      rw [e'] at hc
      rw [e]
      cases hop : g.op with
      | and =>
        rw [hop] at hc
        refine cmp_foldl_and X Y a b _ _ ih g.inputs unitA _ ?_ c hc
        intro c' hc'
        simp at hc'
        subst hc'
        exact ⟨0, 0, rfl, by simp [unitA], by simp, by simp, by simp⟩
      | or =>
        rw [hop] at hc
        refine cmp_foldl_or X Y a b _ _ ih g.inputs dflt _ ?_ c hc
        intro c' hc'
        simp at hc'
      | not =>
        rw [hop] at hc
        simp at hc
      | mod m =>
        rw [hop] at hc
        simp at hc
      | maj =>
        rw [hop] at hc
        simp at hc
    · rw [rvStep_big _ _ _ _ (by omega)] at hc
      simp at hc

abbrev I4 := ℕ × ℕ × ℕ × ℕ

def rdT (W : List Bool) (I : I4) : T4 :=
  (W.getD I.1 false, W.getD I.2.1 false, W.getD I.2.2.1 false, W.getD I.2.2.2 false)

def okI (W : List Bool) (I : I4) : Prop :=
  I.1 < W.length ∧ I.2.1 < W.length ∧ I.2.2.1 < W.length ∧ I.2.2.2 < W.length

def smallBlock (op : GateOp) (L : List I4) : List Gate :=
  [⟨op, L.map fun t => t.1⟩, ⟨GateOp.or, L.map fun t => t.2.1⟩,
   ⟨GateOp.or, L.map fun t => t.2.2.1⟩, ⟨GateOp.or, L.map fun t => t.2.2.2⟩]

def dGates (z B : ℕ) (op : GateOp) (L : List I4) : List Gate × I4 :=
  match op with
  | GateOp.and =>
    match L with
    | [a, b] => (andBlock B a b, (B, B + 3, B + 6, B + 13))
    | _ => (smallBlock GateOp.and L, (B, B + 1, B + 2, B + 3))
  | GateOp.or => (smallBlock GateOp.or L, (B, B + 1, B + 2, B + 3))
  | _ => ([], (z, z, z, z))

theorem map_rd (W E : List Bool) (L : List I4) (pr : I4 → ℕ) (h : ∀ t ∈ L, pr t < W.length) :
    (L.map pr).map (fun i => (W ++ E).getD i false) = L.map (fun t => W.getD (pr t) false) := by
  rw [List.map_map]
  exact List.map_congr_left (fun t ht => rd_old _ _ _ (h t ht))

theorem smallBlock_run (W : List Bool) (op : GateOp) (L : List I4) (h : ∀ t ∈ L, okI W t) :
    run (smallBlock op L) W = W ++ [op.eval (L.map fun t => W.getD t.1 false),
      (L.map fun t => W.getD t.2.1 false).any id,
      (L.map fun t => W.getD t.2.2.1 false).any id,
      (L.map fun t => W.getD t.2.2.2 false).any id] := by
  have e1 := map_rd W [] L (fun t => t.1) (fun t ht => (h t ht).1)
  have e2 := fun E => map_rd W E L (fun t => t.2.1) (fun t ht => (h t ht).2.1)
  have e3 := fun E => map_rd W E L (fun t => t.2.2.1) (fun t ht => (h t ht).2.2.1)
  have e4 := fun E => map_rd W E L (fun t => t.2.2.2) (fun t ht => (h t ht).2.2.2)
  rw [List.append_nil] at e1
  simp only [smallBlock, run_cons, run_nil, List.append_assoc, List.cons_append, List.nil_append,
    GateOp.eval, e1, e2, e3, e4]

theorem getD_at (W : List Bool) (E : List Bool) (t : ℕ) :
    (W ++ E).getD (W.length + t) false = E.getD t false := rd_new W E t

theorem foldl_orT (l : List T4) : ∀ acc : T4, l.foldl orT acc =
    (acc.1 || (l.map fun t => t.1).any id, acc.2.1 || (l.map fun t => t.2.1).any id,
     acc.2.2.1 || (l.map fun t => t.2.2.1).any id,
     acc.2.2.2 || (l.map fun t => t.2.2.2).any id) := by
  induction l with
  | nil => intro acc; simp
  | cons t l ih =>
    intro acc
    rw [List.foldl_cons, ih]
    simp [orT, Bool.or_assoc]

theorem andT_unitA (t : T4) : andT unitA t = t := by
  obtain ⟨o, p, q, m⟩ := t
  simp [andT, unitA]

theorem block_and (z : ℕ) (W : List Bool) (L : List I4) (hL : L.length ≤ 2)
    (h : ∀ t ∈ L, okI W t) :
    okI (run (dGates z W.length GateOp.and L).1 W) (dGates z W.length GateOp.and L).2 ∧
    rdT (run (dGates z W.length GateOp.and L).1 W) (dGates z W.length GateOp.and L).2 =
      (L.map (rdT W)).foldl andT unitA := by
  have e0 : ∀ E : List Bool, (W ++ E).getD W.length false = E.getD 0 false := fun E => rd_new W E 0
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, L⟩⟩⟩
  · have hr := smallBlock_run W GateOp.and [] (by simp)
    simp only [dGates]
    rw [hr]
    refine ⟨⟨by simp, by simp, by simp, by simp⟩, ?_⟩
    simp [rdT, e0, getD_at, GateOp.eval, unitA]
  · have hr := smallBlock_run W GateOp.and [a] h
    simp only [dGates]
    rw [hr]
    refine ⟨⟨by simp, by simp, by simp, by simp⟩, ?_⟩
    simp [rdT, e0, getD_at, GateOp.eval, andT_unitA]
  · have ha := h a (by simp)
    have hb := h b (by simp)
    have hr := andBlock_run W a b ha.1 ha.2.1 ha.2.2.1 ha.2.2.2 hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
    simp only [dGates]
    obtain ⟨r1, r2, r3, r4⟩ := hr
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [run_length]; simp [andBlock]
    · rw [run_length]; simp [andBlock]
    · rw [run_length]; simp [andBlock]
    · rw [run_length]; simp [andBlock]
    · show rdT _ _ = andT (andT unitA (rdT W a)) (rdT W b)
      rw [andT_unitA]
      simp only [rdT, r1, r2, r3, r4, andT]
  · simp at hL

theorem block_or (z : ℕ) (W : List Bool) (L : List I4) (h : ∀ t ∈ L, okI W t) :
    okI (run (dGates z W.length GateOp.or L).1 W) (dGates z W.length GateOp.or L).2 ∧
    rdT (run (dGates z W.length GateOp.or L).1 W) (dGates z W.length GateOp.or L).2 =
      (L.map (rdT W)).foldl orT dflt := by
  have e0 : ∀ E : List Bool, (W ++ E).getD W.length false = E.getD 0 false := fun E => rd_new W E 0
  have hr := smallBlock_run W GateOp.or L h
  simp only [dGates]
  rw [hr]
  refine ⟨⟨by simp, by simp, by simp, by simp⟩, ?_⟩
  rw [foldl_orT]
  simp [rdT, e0, getD_at, GateOp.eval, dflt, List.map_map, Function.comp_def]

abbrev zI (n : ℕ) : I4 := (2 * n, 2 * n, 2 * n, 2 * n)

def dStep (n : ℕ) (st : List Gate × List I4) (g : Gate) : List Gate × List I4 :=
  (st.1 ++ (dGates (2 * n) (2 * n + st.1.length) g.op
      (g.inputs.map fun i => st.2.getD i (zI n))).1,
   st.2 ++ [(dGates (2 * n) (2 * n + st.1.length) g.op
      (g.inputs.map fun i => st.2.getD i (zI n))).2])

def dInit (n : ℕ) : List Gate × List I4 :=
  ([⟨GateOp.or, []⟩], (List.range n).map fun i => (2 * n, i, n + i, 2 * n))

def dBuild (n : ℕ) (gs : List Gate) : List Gate × List I4 := gs.foldl (dStep n) (dInit n)

theorem dBuild_snoc (n : ℕ) (gs : List Gate) (g : Gate) :
    dBuild n (gs ++ [g]) = dStep n (dBuild n gs) g := by
  simp [dBuild, List.foldl_append]

theorem dBuild_idx_length (n : ℕ) (gs : List Gate) : (dBuild n gs).2.length = n + gs.length := by
  induction gs using List.reverseRec with
  | nil => simp [dBuild, dInit]
  | append_singleton gs g ih =>
    rw [dBuild_snoc]
    simp [dStep, ih]
    omega

theorem dGates_len (z B : ℕ) (op : GateOp) (L : List I4) : (dGates z B op L).1.length ≤ 14 := by
  unfold dGates
  split
  · split
    · simp [andBlock]
    · simp [smallBlock]
  · simp [smallBlock]
  · simp

theorem dGates_mono (z B : ℕ) (op : GateOp) (L : List I4) (hL : L.length ≤ 2) :
    ∀ g ∈ (dGates z B op L).1,
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  unfold dGates
  split
  · split
    · intro g hg
      simp only [andBlock, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp
    · intro g hg
      simp only [smallBlock, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> simp [hL]
  · intro g hg
    simp only [smallBlock, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp [hL]
  · simp

theorem dBuild_len (n : ℕ) (gs : List Gate) : (dBuild n gs).1.length ≤ 1 + 14 * gs.length := by
  induction gs using List.reverseRec with
  | nil => simp [dBuild, dInit]
  | append_singleton gs g ih =>
    rw [dBuild_snoc]
    have := dGates_len (2 * n) (2 * n + (dBuild n gs).1.length) g.op
      (g.inputs.map fun i => (dBuild n gs).2.getD i (zI n))
    simp only [dStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem dBuild_mono (n : ℕ) (gs : List Gate) :
    (∀ g ∈ gs, g.inputs.length ≤ 2) → ∀ g ∈ (dBuild n gs).1,
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction gs using List.reverseRec with
  | nil =>
    intro _ g hg
    simp [dBuild, dInit] at hg
    subst hg
    simp
  | append_singleton gs g ih =>
    intro hm g' hg'
    rw [dBuild_snoc] at hg'
    simp only [dStep, List.mem_append] at hg'
    rcases hg' with h | h
    · exact ih (fun g'' hg'' => hm g'' (by simp [hg''])) g' h
    · exact dGates_mono _ _ _ _ (by simpa using hm g (by simp)) g' h

def Link (n : ℕ) (X Y : List Bool) (gs : List Gate) : Prop :=
  2 * n < (run (dBuild n gs).1 (X ++ Y)).length ∧
  (run (dBuild n gs).1 (X ++ Y)).getD (2 * n) false = false ∧
  ∀ w, okI (run (dBuild n gs).1 (X ++ Y)) ((dBuild n gs).2.getD w (zI n)) ∧
    rdT (run (dBuild n gs).1 (X ++ Y)) ((dBuild n gs).2.getD w (zI n)) =
      (sem n X Y gs).getD w dflt

theorem link_nil (n : ℕ) (X Y : List Bool) (hX : X.length = n) (hY : Y.length = n) :
    Link n X Y [] := by
  have hW : run (dBuild n []).1 (X ++ Y) = (X ++ Y) ++ [false] := rfl
  have hXY : (X ++ Y).length = 2 * n := by simp [hX, hY]; omega
  have z0 : ((X ++ Y) ++ [false]).getD (2 * n) false = false := by
    have := rd_new (X ++ Y) [false] 0
    rw [hXY, Nat.add_zero] at this
    rw [this]
    rfl
  unfold Link
  rw [hW]
  refine ⟨by simp [hX, hY]; omega, z0, ?_⟩
  intro w
  by_cases hw : w < n
  · have e : (dBuild n []).2.getD w (zI n) = (2 * n, w, n + w, 2 * n) := by
      simp [dBuild, dInit, List.getD_eq_getElem?_getD, hw]
    rw [e, sem_nil_lt n X Y w hw]
    have v2 : ((X ++ Y) ++ [false]).getD w false = X.getD w false := by
      rw [rd_old _ _ _ (by omega), rd_old _ _ _ (by omega)]
    have v3 : ((X ++ Y) ++ [false]).getD (n + w) false = Y.getD w false := by
      rw [rd_old _ _ _ (by omega)]
      have := rd_new X Y w
      rw [hX] at this
      exact this
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hX, hY]; omega
    · simp [hX, hY]; omega
    · simp [hX, hY]; omega
    · simp [hX, hY]; omega
    · simp only [rdT, z0, v2, v3]
  · have e : (dBuild n []).2.getD w (zI n) = zI n := by
      apply List.getD_eq_default
      simp [dBuild, dInit]
      omega
    have e2 : (sem n X Y []).getD w dflt = dflt := by
      apply List.getD_eq_default
      simp [sem, sem0]
      omega
    rw [e, e2]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hX, hY]; omega
    · simp [hX, hY]; omega
    · simp [hX, hY]; omega
    · simp [hX, hY]; omega
    · simp only [rdT, z0, dflt]

theorem link (n : ℕ) (X Y : List Bool) (hX : X.length = n) (hY : Y.length = n) (gs : List Gate) :
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      Link n X Y gs := by
  induction gs using List.reverseRec with
  | nil => intro _; exact link_nil n X Y hX hY
  | append_singleton gs g ih =>
    intro hm
    have hmg := hm g (by simp)
    obtain ⟨h1, h2, h3⟩ := ih (fun g' hg' => hm g' (by simp [hg']))
    have hWlen : (run (dBuild n gs).1 (X ++ Y)).length = 2 * n + (dBuild n gs).1.length := by
      rw [run_length]
      simp [hX, hY]
      omega
    have hok : ∀ t ∈ g.inputs.map (fun i => (dBuild n gs).2.getD i (zI n)),
        okI (run (dBuild n gs).1 (X ++ Y)) t := by
      intro t ht
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 ht
      exact (h3 i).1
    have bsa := block_and (2 * n) (run (dBuild n gs).1 (X ++ Y)) _ (by simpa using hmg.2) hok
    have bso := block_or (2 * n) (run (dBuild n gs).1 (X ++ Y)) _ hok
    rw [hWlen] at bsa bso
    have hrun : run (dBuild n (gs ++ [g])).1 (X ++ Y) =
        run (dGates (2 * n) (2 * n + (dBuild n gs).1.length) g.op
          (g.inputs.map fun i => (dBuild n gs).2.getD i (zI n))).1
          (run (dBuild n gs).1 (X ++ Y)) := by
      rw [dBuild_snoc]
      exact run_append _ _ _
    have hidx : (dBuild n (gs ++ [g])).2 = (dBuild n gs).2 ++
        [(dGates (2 * n) (2 * n + (dBuild n gs).1.length) g.op
          (g.inputs.map fun i => (dBuild n gs).2.getD i (zI n))).2] := by
      rw [dBuild_snoc]
      rfl
    have hprefix : ∀ i, i < (run (dBuild n gs).1 (X ++ Y)).length →
        (run (dBuild n (gs ++ [g])).1 (X ++ Y)).getD i false =
          (run (dBuild n gs).1 (X ++ Y)).getD i false := by
      intro i hi
      rw [hrun]
      exact run_old _ _ _ hi
    have hlen' : (run (dBuild n gs).1 (X ++ Y)).length ≤
        (run (dBuild n (gs ++ [g])).1 (X ++ Y)).length := by
      rw [hrun]
      simp only [run_length]
      omega
    have ilen := dBuild_idx_length n gs
    have slen := sem_length n X Y gs
    have hsem := sem_snoc n X Y gs g
    refine ⟨by omega, by rw [hprefix _ h1]; exact h2, ?_⟩
    intro w
    rcases Nat.lt_trichotomy w (n + gs.length) with hw | hw | hw
    · have e : (dBuild n (gs ++ [g])).2.getD w (zI n) = (dBuild n gs).2.getD w (zI n) := by
        rw [hidx]
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (ilen ▸ hw)]
      rw [e, hsem, semStep_old _ _ _ (by omega)]
      obtain ⟨⟨o1, o2, o3, o4⟩, hr⟩ := h3 w
      refine ⟨⟨by omega, by omega, by omega, by omega⟩, ?_⟩
      rw [← hr]
      unfold rdT
      rw [hprefix _ o1, hprefix _ o2, hprefix _ o3, hprefix _ o4]
    · have e : (dBuild n (gs ++ [g])).2.getD w (zI n) =
          (dGates (2 * n) (2 * n + (dBuild n gs).1.length) g.op
            (g.inputs.map fun i => (dBuild n gs).2.getD i (zI n))).2 := by
        rw [hidx, hw, ← ilen]
        simp [List.getD_eq_getElem?_getD]
      have e2 := semStep_new (sem n X Y gs) g
      rw [slen, ← hw] at e2
      have emap : (g.inputs.map fun i => (dBuild n gs).2.getD i (zI n)).map
          (rdT (run (dBuild n gs).1 (X ++ Y))) =
          g.inputs.map fun i => (sem n X Y gs).getD i dflt := by
        rw [List.map_map]
        exact List.map_congr_left (fun i _ => (h3 i).2)
      rw [e, hsem, e2, hrun]
      rcases hmg.1 with hop | hop
      · rw [hop]
        refine ⟨bsa.1, ?_⟩
        rw [bsa.2, emap]
      · rw [hop]
        refine ⟨bso.1, ?_⟩
        rw [bso.2, emap]
    · have e : (dBuild n (gs ++ [g])).2.getD w (zI n) = zI n := by
        apply List.getD_eq_default
        rw [hidx]
        simp [ilen]
        omega
      rw [e, hsem, semStep_big _ _ _ (by omega)]
      have hz : 2 * n < (run (dBuild n (gs ++ [g])).1 (X ++ Y)).length := by omega
      refine ⟨⟨hz, hz, hz, hz⟩, ?_⟩
      simp only [rdT, hprefix _ h1, h2, dflt]

theorem ofFn_getD (n : ℕ) (x : Fin n → Bool) (u : Fin n) :
    (List.ofFn x).getD u.val false = x u := by
  simp [List.getD_eq_getElem?_getD]

theorem ofFn_getD_true (n : ℕ) (x : Fin n → Bool) (w : ℕ)
    (h : (List.ofFn x).getD w false = true) : ∃ u : Fin n, u.val = w ∧ x u = true := by
  by_cases hw : w < n
  · exact ⟨⟨w, hw⟩, rfl, by rw [← h]; exact (ofFn_getD n x ⟨w, hw⟩).symm⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)] at h
    cases h

theorem setList_pair (n : ℕ) (u v : Fin n) (huv : u ≠ v) :
    ∃ a b : ℕ, a ≠ b ∧ setList ({u, v} : Finset (Fin n)) = [a, b] ∧
      ((a = u.val ∧ b = v.val) ∨ (a = v.val ∧ b = u.val)) := by
  have hnd : ((List.finRange n).filter fun i => decide (i ∈ ({u, v} : Finset (Fin n)))).Nodup :=
    (List.nodup_finRange n).filter _
  have hmem : ∀ i : Fin n,
      i ∈ ((List.finRange n).filter fun i => decide (i ∈ ({u, v} : Finset (Fin n)))) ↔
        (i = u ∨ i = v) := by
    intro i
    simp [List.mem_filter]
  have hlen : ((List.finRange n).filter fun i => decide (i ∈ ({u, v} : Finset (Fin n)))).length
      = 2 := by
    rw [← List.toFinset_card_of_nodup hnd]
    have e : ((List.finRange n).filter fun i => decide (i ∈ ({u, v} : Finset (Fin n)))).toFinset
        = ({u, v} : Finset (Fin n)) := by
      ext i
      simp
    rw [e]
    exact Finset.card_pair huv
  obtain ⟨p, q, hl⟩ := List.length_eq_two.1 hlen
  have hp := (hmem p).1 (by rw [hl]; simp)
  have hq := (hmem q).1 (by rw [hl]; simp)
  rw [hl] at hnd
  have hpq : p ≠ q := by
    intro h
    simp [h] at hnd
  refine ⟨p.val, q.val, fun h => hpq (Fin.ext h), ?_, ?_⟩
  · unfold setList
    rw [hl]
    rfl
  · rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact absurd rfl hpq
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hpq

set_option maxHeartbeats 1000000 in
theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hC : Monotone2 C) (hR : IsReadK n C 1)
    (hf : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
      decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 ≤ 14 * (C.size + 1) ∧
      ∀ x y : Fin n → Bool, D.eval (List.ofFn x ++ List.ofFn y) =
        decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ y v = true) := by
  refine ⟨⟨(dBuild n C.gates).1, ((dBuild n C.gates).2.getD C.output (zI n)).2.2.2⟩, ?_, ?_, ?_⟩
  · intro g hg
    exact dBuild_mono n C.gates (fun g' hg' => (hC g' hg').2) g hg
  · have := dBuild_len n C.gates
    show (dBuild n C.gates).1.length + 1 ≤ 14 * (C.gates.length + 1)
    omega
  · intro x y
    have hm : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      obtain ⟨h1, h2⟩ := hC g hg
      exact ⟨by simpa using h1, h2⟩
    have lk := link n (List.ofFn x) (List.ofFn y) (by simp) (by simp) C.gates hm
    have hval : (⟨(dBuild n C.gates).1,
        ((dBuild n C.gates).2.getD C.output (zI n)).2.2.2⟩ : Circuit).eval
          (List.ofFn x ++ List.ofFn y) =
        ((sem n (List.ofFn x) (List.ofFn y) C.gates).getD C.output dflt).2.2.2 :=
      congrArg (fun t : T4 => t.2.2.2) (lk.2.2 C.output).2
    rw [hval]
    have snd := sem_sound n (List.ofFn x) (List.ofFn y) C.gates C.output
    have cmpC := fun (a b : ℕ) (hab : a ≠ b) (c : List ℕ) =>
      sem_complete n (List.ofFn x) (List.ofFn y) a b hab C.gates C.output c
    generalize (sem n (List.ofFn x) (List.ofFn y) C.gates).getD C.output dflt = t at snd cmpC ⊢
    obtain ⟨s1, s2, s3, s4⟩ := snd
    have noConst : ¬ ∀ z : List Bool, z.length = n → C.eval z = true := by
      intro h
      have h0 := h (List.ofFn fun _ : Fin n => false) (by simp)
      rw [hf] at h0
      simp at h0
    have noSingle : ∀ w : Fin n,
        ¬ ∀ z : List Bool, z.length = n → z.getD w.val false = true → C.eval z = true := by
      intro w h
      have h0 := h (List.ofFn fun i : Fin n => decide (i = w)) (by simp)
        (by rw [ofFn_getD]; simp)
      rw [hf] at h0
      simp only [decide_eq_true_eq] at h0
      obtain ⟨p, q, hpq, rfl, rfl⟩ := h0
      exact G.irrefl hpq
    have n1 : ¬ t.1 = true := fun h => noConst (s1 h)
    have n2 : ¬ t.2.1 = true := by
      intro h
      obtain ⟨w', hw', hz⟩ := s2 h
      obtain ⟨w, rfl, _⟩ := ofFn_getD_true n x w' hw'
      exact noSingle w hz
    have n3 : ¬ t.2.2.1 = true := by
      intro h
      obtain ⟨w', hw', hz⟩ := s3 h
      obtain ⟨w, rfl, _⟩ := ofFn_getD_true n y w' hw'
      exact noSingle w hz
    apply Bool.eq_iff_iff.2
    rw [decide_eq_true_iff]
    constructor
    · intro ht
      obtain ⟨u', v', hu', hv', hz⟩ := s4 ht
      obtain ⟨u, rfl, hxu⟩ := ofFn_getD_true n x u' hu'
      obtain ⟨v, rfl, hyv⟩ := ofFn_getD_true n y v' hv'
      have h0 : C.eval (List.ofFn fun i : Fin n => decide (i = u ∨ i = v)) = true :=
        hz _ (by simp) (by rw [ofFn_getD]; simp) (by rw [ofFn_getD]; simp)
      rw [hf] at h0
      simp only [decide_eq_true_eq] at h0
      obtain ⟨p, q, hpq, hp, hq⟩ := h0
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
      · exact absurd hpq G.irrefl
      · exact ⟨_, _, hpq, hxu, hyv⟩
      · exact ⟨_, _, hpq.symm, hxu, hyv⟩
      · exact absurd hpq G.irrefl
    · rintro ⟨u, v, huv, hxu, hyv⟩
      have hne : u ≠ v := G.ne_of_adj huv
      obtain ⟨a, b, hab, hS, hcase⟩ := setList_pair n u v hne
      have hprime : IsPrimeImplicant n C ({u, v} : Finset (Fin n)) := by
        constructor
        · show C.eval (List.ofFn (setInput ({u, v} : Finset (Fin n)))) = true
          rw [hf]
          simp only [decide_eq_true_eq]
          exact ⟨u, v, huv, by simp [setInput], by simp [setInput]⟩
        · intro T hT
          show C.eval (List.ofFn (setInput T)) = false
          rw [hf, decide_eq_false_iff_not]
          rintro ⟨p, q, hpq, hp, hq⟩
          have hT' := Finset.mem_ssubsets.1 hT
          have hp' : p ∈ T := by simpa [setInput] using hp
          have hq' : q ∈ T := by simpa [setInput] using hq
          have hpS := hT'.1 hp'
          have hqS := hT'.1 hq'
          simp only [Finset.mem_insert, Finset.mem_singleton] at hpS hqS
          have hpq' := G.ne_of_adj hpq
          apply hT'.2
          intro s hs
          simp only [Finset.mem_insert, Finset.mem_singleton] at hs
          rcases hs with hs | hs <;> rcases hpS with hpS | hpS <;> rcases hqS with hqS | hqS <;>
            first
              | exact absurd (hpS.trans hqS.symm) hpq'
              | exact (hs.trans hpS.symm) ▸ hp'
              | exact (hs.trans hqS.symm) ▸ hq'
      have hread := hR _ hprime
      unfold readsAtMost at hread
      rw [rv_eq, hS] at hread
      obtain ⟨c, hc, hall⟩ := List.any_eq_true.1 hread
      obtain ⟨c0, c1, rfl, k1, k2, k3, k4⟩ := cmpC a b hab c hc
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
        decide_eq_true_eq] at hall
      obtain ⟨hc0, hc1⟩ := hall
      have hxa : a = u.val → (List.ofFn x).getD a false = true := fun h => by
        rw [h, ofFn_getD]; exact hxu
      have hxb : b = u.val → (List.ofFn x).getD b false = true := fun h => by
        rw [h, ofFn_getD]; exact hxu
      have hya : a = v.val → (List.ofFn y).getD a false = true := fun h => by
        rw [h, ofFn_getD]; exact hyv
      have hyb : b = v.val → (List.ofFn y).getD b false = true := fun h => by
        rw [h, ofFn_getD]; exact hyv
      have h0 : c0 = 0 ∨ c0 = 1 := by omega
      have h1 : c1 = 0 ∨ c1 = 1 := by omega
      rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl
      · exact absurd (k1 rfl rfl) n1
      · rcases hcase with ⟨_, hb⟩ | ⟨_, hb⟩
        · exact absurd ((k3 rfl rfl).2 (hyb hb)) n3
        · exact absurd ((k3 rfl rfl).1 (hxb hb)) n2
      · rcases hcase with ⟨ha, _⟩ | ⟨ha, _⟩
        · exact absurd ((k2 rfl rfl).1 (hxa ha)) n2
        · exact absurd ((k2 rfl rfl).2 (hya ha)) n3
      · rcases hcase with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact k4 rfl rfl (Or.inl ⟨hxa ha, hyb hb⟩)
        · exact k4 rfl rfl (Or.inr ⟨hxb hb, hya ha⟩)

end PEqualNP.Outside.L_meta_4193

theorem PEqualNP.Outside.L_meta_4193 : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.ReadK.IsReadK x2 x5 (1 : ℕ) → (∀ (x8 : Fin x2 → Bool), x5.eval (List.ofFn x8) = Decidable.decide (∃ (x9 : Fin x2) (x10 : Fin x2), x3.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 ∧ x9.size + (1 : ℕ) ≤ x1 * (x5.size + (1 : ℕ)) ∧ ∀ (x10 x11 : Fin x2 → Bool), x9.eval (List.ofFn x10 ++ List.ofFn x11) = Decidable.decide (∃ (x12 : Fin x2) (x13 : Fin x2), x3.Adj x12 x13 ∧ x10 x12 = Bool.true ∧ x11 x13 = Bool.true) :=
  ⟨14, fun n G inst C hC hR hf => @PEqualNP.Outside.L_meta_4193.main n G inst C hC hR hf⟩
