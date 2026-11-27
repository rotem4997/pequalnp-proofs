import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.SyntacticMultilinear

namespace PEqualNP.Outside.L_meta_6055

-- An eight-gate witness on the sixteen inputs with one point and one line on.
def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [2, 3]⟩,
    ⟨.and, [11, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

lemma upper : RepSizeAtMost (fun u v : Fin 4 => (5068 : ℕ).testBit (4 * u.val + v.val)) 8 := by
  refine ⟨witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

-- Each of the eight raw inputs must occur in the support of the output.
def graph5068 (u v : Fin 4) : Bool := (5068 : ℕ).testBit (4 * u.val + v.val)

theorem rowWitness : ∀ i : Fin 8, ∃ u v u' v' : Fin 4,
    graph5068 u v = true ∧ graph5068 u' v' = false ∧
    ∀ k : Fin 8, k ≠ i → (oneEach u v).getD k false = true →
      (oneEach u' v').getD k false = true := by decide

def appendValue (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun k => w.getD k false))]

def outsideRel (i : Fin 8) (s : List (Finset (Fin 8))) (x y : List Bool) : Prop :=
  x.length = s.length ∧ y.length = s.length ∧
    ∀ k, i ∉ s.getD k ∅ → x.getD k false = true → y.getD k false = true

theorem outsideStep (i : Fin 8) (s : List (Finset (Fin 8))) (x y : List Bool) (g : Gate)
    (h : outsideRel i s x y) (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    outsideRel i (supportStep s g) (appendValue x g) (appendValue y g) := by
  obtain ⟨hx, hy, h⟩ := h
  let U := g.inputs.foldr (fun k t => s.getD k ∅ ∪ t) ∅
  have sub (ks : List ℕ) (k : ℕ) (hk : k ∈ ks) :
      s.getD k ∅ ⊆ ks.foldr (fun l t => s.getD l ∅ ∪ t) ∅ := by
    induction ks with
    | nil => simp at hk
    | cons l ks ih =>
      rcases List.mem_cons.mp hk with rfl | hmem
      · exact Finset.subset_union_left
      · exact Finset.Subset.trans (ih hmem) Finset.subset_union_right
  have gateImp (hi : i ∉ U) : g.op.eval (g.inputs.map (fun k => x.getD k false)) = true →
      g.op.eval (g.inputs.map (fun k => y.getD k false)) = true := by
    have f (k : ℕ) (hk : k ∈ g.inputs) := h k (fun hm => hi (sub g.inputs k hk hm))
    rcases hg with hop | hop
    · rw [hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
      rintro all _ ⟨k, hk, rfl⟩
      exact f k hk (all _ ⟨k,hk,rfl⟩)
    · change g.op = GateOp.or at hop
      rw [hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
      rintro ⟨_,⟨k,hk,rfl⟩,hval⟩
      exact ⟨_, ⟨k,hk,rfl⟩, f k hk hval⟩
  refine ⟨by simp [appendValue, supportStep, hx], by simp [appendValue, supportStep, hy], ?_⟩
  intro k
  change i ∉ (s ++ [U]).getD k ∅ → (x ++ [_]).getD k false = true → (y ++ [_]).getD k false = true
  by_cases hk : k < s.length
  · rw [List.getD_append _ _ _ _ hk, List.getD_append _ _ _ _ (by omega : k < x.length),
        List.getD_append _ _ _ _ (by omega : k < y.length)]
    exact h k
  · rw [List.getD_append_right _ _ _ _ (by omega : s.length ≤ k),
        List.getD_append_right _ _ _ _ (by omega : x.length ≤ k),
        List.getD_append_right _ _ _ _ (by omega : y.length ≤ k), hx, hy]
    cases k - s.length with
    | zero => exact gateImp
    | succ d => simp

theorem outsideFold (i : Fin 8) (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (s : List (Finset (Fin 8))) (x y : List Bool) (h : outsideRel i s x y) :
    outsideRel i (gs.foldl supportStep s) (gs.foldl appendValue x) (gs.foldl appendValue y) := by
  induction gs generalizing s x y with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun k hk => hm k (List.mem_cons_of_mem _ hk)) _ _ _ (outsideStep i s x y g h (hm _ List.mem_cons_self))

theorem necessaryInputs (C : Circuit) (hm : Monotone2 C) (hc : Represents graph5068 C) :
    support 8 C C.output = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  obtain ⟨u,v,u',v',hp,hn,hw⟩ := rowWitness i
  let s := List.ofFn fun j : Fin 8 => ({j} : Finset (Fin 8))
  let x := oneEach u v
  let y := oneEach u' v'
  have init : outsideRel i s x y := by
    refine ⟨by simp [x, s, oneEach], by simp [y, s, oneEach], ?_⟩
    intro k hi
    by_cases hk : k < 8
    · apply hw ⟨k,hk⟩
      intro eq
      apply hi
      have base : ∀ j : Fin 8, s.getD j ∅ = {j} := by decide
      simpa only [base ⟨k,hk⟩, Finset.mem_singleton] using eq.symm
    · have allLen : x.length = 8 := by simp [x, oneEach]
      rw [List.getD_eq_default x false (by omega : x.length ≤ k)]
      simp
  by_contra h
  have out := (outsideFold i C.gates (fun g hg => (hm g hg).1) s x y init).2.2 C.output h
  change C.eval x = true → C.eval y = true at out
  have pos := out ((hc u v).trans hp)
  exact Bool.noConfusion (pos.symm.trans ((hc u' v').trans hn))

-- A backwards pass counts the distinct live wires. Reaching eight inputs in
-- seven binary gates forces every expansion to split into two disjoint parts.
def sup (gs : List Gate) (i : ℕ) : Finset (Fin 8) :=
  support 8 ⟨gs,0⟩ i

def tbl (gs : List Gate) (i : ℕ) (u v : Fin 4) : Bool :=
  ((⟨gs,0⟩ : Circuit).wires (oneEach u v)).getD i false

def ft (gs : List Gate) (A : Finset ℕ) : Finset (Fin 8) :=
  A.biUnion (sup gs)

def sameBool (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma oneEach_len (u v : Fin 4) : (oneEach u v).length = 8 := by simp [oneEach]

lemma len_fold {α : Type} (f : List α → Gate → List α)
    (hh : ∀ w g, (f w g).length = w.length + 1) (gs : List Gate) (w : List α) :
    (gs.foldl f w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih, hh, List.length_cons]; omega

lemma snoc_getd {α : Type} (w : List α) (z d : α) (i : ℕ) :
    (w ++ [z]).getD i d = if i = w.length then z else w.getD i d := by
  by_cases h : i < w.length
  · rw [List.getD_append _ _ _ _ h, ite_eq_right (Nat.ne_of_lt h)]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    split_ifs with he
    · simp [he]
    · rw [List.getD_eq_default w d (by omega)]
      cases t : i - w.length with
      | zero => omega
      | succ => simp

lemma foldSupport (l : List ℕ) (f : ℕ → Finset (Fin 8)) :
    l.foldr (fun w acc => f w ∪ acc) ∅ = l.toFinset.biUnion f := by
  induction l with
  | nil => simp
  | cons w l ih => simp [ih, Finset.biUnion_insert]

lemma sup_snoc (gs : List Gate) (g : Gate) (i : ℕ) :
    sup (gs ++ [g]) i = if i = 8 + gs.length then g.inputs.toFinset.biUnion (sup gs) else sup gs i := by
  let s := gs.foldl supportStep (List.ofFn fun i : Fin 8 => ({i} : Finset (Fin 8)))
  have hl : s.length = 8 + gs.length := by
    dsimp [s]
    rw [len_fold _ (by intros; simp [supportStep]), List.length_ofFn]
  change (((gs ++ [g]).foldl supportStep _).getD i ∅) = _
  rw [List.foldl_append]
  change (s ++ [_]).getD i ∅ = _
  rw [snoc_getd, hl]
  split_ifs
  · exact foldSupport _ _
  · rfl

lemma tbl_snoc (gs : List Gate) (g : Gate) (i : ℕ) (u v : Fin 4) :
    tbl (gs ++ [g]) i u v = if i = 8 + gs.length then
      g.op.eval (g.inputs.map (fun w => tbl gs w u v)) else tbl gs i u v := by
  let s := gs.foldl sameBool (oneEach u v)
  have hl : s.length = 8 + gs.length := by
    dsimp [s]; rw [len_fold _ (by intros; simp [sameBool]), oneEach_len]
  change (((gs ++ [g]).foldl sameBool _).getD i false) = _
  rw [List.foldl_append]
  change (s ++ [_]).getD i false = _
  rw [snoc_getd, hl]
  rfl

lemma sup_nil (i : ℕ) : sup [] i = if h : i < 8 then {⟨i,h⟩} else ∅ := by
  change (List.ofFn fun j : Fin 8 => ({j} : Finset (Fin 8))).getD i ∅ = _
  split_ifs with h
  · interval_cases i <;> rfl
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt h)]

lemma ft_nil (A : Finset ℕ) : (ft [] A).image Fin.val = A.filter (· < 8) := by
  ext i
  simp only [Finset.mem_image, ft, Finset.mem_biUnion, sup_nil, Finset.mem_filter]
  constructor
  · rintro ⟨k,⟨j,hj,hk⟩,rfl⟩
    split_ifs at hk with hjb
    · obtain rfl := Finset.mem_singleton.mp hk
      exact ⟨hj,hjb⟩
    · simp at hk
  · rintro ⟨hi,hb⟩
    exact ⟨⟨i,hb⟩,⟨i,hi,by simp [hb]⟩,rfl⟩

lemma ft_count_nil (A : Finset ℕ) :
    (ft [] A).card = (A.filter (· < 8)).card := by
  rw [← ft_nil, Finset.card_image_of_injective _ Fin.val_injective]

lemma ft_old (gs : List Gate) (g : Gate) (A : Finset ℕ) (hh : 8+gs.length ∉ A) :
    ft (gs ++ [g]) A = ft gs A := by
  apply Finset.biUnion_congr rfl
  intro i hi
  rw [sup_snoc, ite_eq_right (by rintro rfl; exact hh hi)]

lemma ft_hit (gs : List Gate) (g : Gate) (A : Finset ℕ) (hh : 8+gs.length ∈ A) :
    ft (gs ++ [g]) A = ft gs (A.erase (8+gs.length) ∪ g.inputs.toFinset) := by
  let w := 8+gs.length
  let T := A.erase w
  have e : ft (gs ++ [g]) A = sup (gs ++ [g]) w ∪ ft (gs ++ [g]) T := by
    conv_lhs => rw [← Finset.insert_erase hh]
    exact Finset.biUnion_insert
  rw [e, ft_old _ _ _ (Finset.notMem_erase _ _), sup_snoc, ite_eq_left rfl]
  ext k
  simp only [ft, Finset.mem_union, Finset.mem_biUnion]
  change ((_ ∨ ∃ i ∈ T, _) ↔ ∃ i, (i ∈ T ∨ _) ∧ _)
  aesop

lemma pair_shape (g : Gate) (hl : g.inputs.length ≤ 2) (hc : 2 ≤ g.inputs.toFinset.card) :
    ∃ i j, g.inputs = [i,j] ∧ i ≠ j := by
  have hb := List.toFinset_card_le g.inputs
  rcases h : g.inputs with _ | ⟨i, l⟩
  · simp [h] at hc
  rcases l with _ | ⟨j, l⟩
  · simp [h] at hc
  rcases l with _ | ⟨u, l⟩
  · refine ⟨i,j,rfl,?_⟩
    rintro rfl
    simp [h] at hc
  · simp [h] at hl

def forest (P : Finset (Fin 8) → (Fin 4 → Fin 4 → Bool) → Prop) (gs : List Gate) (A : Finset ℕ) : Prop :=
  (∀ i ∈ A, P (sup gs i) (tbl gs i)) ∧
  (∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (sup gs i) (sup gs j))

lemma tree_frontier (P : Finset (Fin 8) → (Fin 4 → Fin 4 → Bool) → Prop)
    (atom : ∀ i : Fin 8, P {i} (fun u v => (oneEach u v).getD i.val false))
    (meet : ∀ {s t f h}, P s f → P t h → Disjoint s t →
      P (s ∪ t) (fun u v => f u v && h u v))
    (join : ∀ {s t f h}, P s f → P t h → Disjoint s t →
      P (s ∪ t) (fun u v => f u v || h u v))
    (gs : List Gate) (hm : Monotone2 ⟨gs,0⟩) (A : Finset ℕ) :
    (ft gs A).card ≤ A.card + gs.length ∧
      (A.card + gs.length ≤ (ft gs A).card → forest P gs A) := by
  induction gs using List.reverseRecOn generalizing A with
  | nil =>
    have hle := Finset.card_filter_le A (· < 8)
    refine ⟨by simpa [ft_count_nil] using hle, ?_⟩
    intro he
    have eq : A.filter (· < 8) = A := Finset.eq_of_subset_of_card_le
      (Finset.filter_subset _ _) (by simpa [ft_count_nil] using he)
    have hb (i : ℕ) (hi : i ∈ A) : i < 8 := by
      have hi' : i ∈ A.filter (fun j => j < 8) := eq.symm ▸ hi
      exact (Finset.mem_filter.mp hi').2
    constructor
    · intro i hi
      rw [sup_nil, dite_eq_left (hb i hi)]
      exact atom ⟨i,hb i hi⟩
    · intro i hi j hj hne
      rw [sup_nil, sup_nil, dite_eq_left (hb i hi), dite_eq_left (hb j hj), Finset.disjoint_singleton]
      exact fun eq => hne (congrArg Fin.val eq)
  | append_singleton gs g ih =>
    let w := 8 + gs.length
    have hm' : Monotone2 ⟨gs,0⟩ := fun a ha => hm a (List.mem_append_left _ ha)
    have hg := hm g (List.mem_append_right _ (List.mem_singleton_self _))
    by_cases hw : w ∈ A
    · let T := A.erase w
      let B := T ∪ g.inputs.toFinset
      have hft : ft (gs++[g]) A = ft gs B := ft_hit _ _ _ hw
      have hT : T.card + 1 = A.card := Finset.card_erase_add_one hw
      have hB : B.card ≤ T.card + g.inputs.toFinset.card := Finset.card_union_le _ _
      have hI := List.toFinset_card_le g.inputs
      obtain ⟨bound, make⟩ := ih hm' B
      rw [hft, List.length_append, List.length_singleton]
      have hglen := hg.2
      refine ⟨by omega, ?_⟩
      intro eq
      obtain ⟨old,disj⟩ := make (by omega)
      have hdis : Disjoint T g.inputs.toFinset :=
        Finset.card_union_eq_card_add_card.mp (by change B.card = _; omega)
      obtain ⟨i,j,hin,hij⟩ := pair_shape _ hglen (by omega)
      have hi : i ∈ g.inputs.toFinset := by simp [hin]
      have hj : j ∈ g.inputs.toFinset := by simp [hin]
      have im : i ∈ B := Finset.mem_union_right _ hi
      have jm : j ∈ B := Finset.mem_union_right _ hj
      have splits : sup (gs++[g]) w = sup gs i ∪ sup gs j := by
        simp [sup_snoc, w, hin, Finset.biUnion_insert]
      have prev (k : ℕ) (hk : k ≠ w) : sup (gs++[g]) k = sup gs k := by rw [sup_snoc]; exact ite_eq_right hk
      have evalPrev (k : ℕ) (hk : k ≠ w) : tbl (gs++[g]) k = tbl gs k := by
        funext u v
        exact (tbl_snoc _ _ _ _ _).trans (ite_eq_right hk)
      have crossOld (k : ℕ) (hk : k ∈ T) : Disjoint (sup gs i ∪ sup gs j) (sup gs k) := by
        have km : k ∈ B := Finset.mem_union_left _ hk
        have hn := Finset.disjoint_left.mp hdis hk
        exact Finset.disjoint_union_left.mpr
          ⟨disj i im k km (by rintro rfl; exact hn hi), disj j jm k km (by rintro rfl; exact hn hj)⟩
      constructor
      · intro k hk
        by_cases he : k = w
        · subst k
          rw [splits]
          rcases hg.1 with hop | hop
          · have ev : tbl (gs++[g]) w = (fun u v => tbl gs i u v && tbl gs j u v) := by
              funext u v; simp [tbl_snoc, w, hin, hop, GateOp.eval]
            rw [ev]
            exact meet (old i im) (old j jm) (disj i im j jm hij)
          · change g.op = GateOp.or at hop
            have ev : tbl (gs++[g]) w = (fun u v => tbl gs i u v || tbl gs j u v) := by
              funext u v; simp [tbl_snoc, w, hin, hop, GateOp.eval]
            rw [ev]
            exact join (old i im) (old j jm) (disj i im j jm hij)
        · rw [prev _ he, evalPrev _ he]
          exact old k (Finset.mem_union_left _ (Finset.mem_erase_of_ne_of_mem he hk))
      · intro k hk l hl hkl
        by_cases he : k = w
        · subst k
          rw [splits, prev _ hkl.symm]
          exact crossOld l (Finset.mem_erase_of_ne_of_mem hkl.symm hl)
        · rw [prev _ he]
          by_cases hf : l = w
          · subst l
            rw [splits]
            exact (crossOld k (Finset.mem_erase_of_ne_of_mem he hk)).symm
          · rw [prev _ hf]
            exact disj _ (Finset.mem_union_left _ (Finset.mem_erase_of_ne_of_mem he hk))
              _ (Finset.mem_union_left _ (Finset.mem_erase_of_ne_of_mem hf hl)) hkl
    · obtain ⟨bound, _⟩ := ih hm' A
      rw [ft_old _ _ _ hw, List.length_append, List.length_singleton]
      exact ⟨by omega, fun h => False.elim (by omega)⟩

lemma readOnce_of_full (P : Finset (Fin 8) → (Fin 4 → Fin 4 → Bool) → Prop)
    (atom : ∀ i : Fin 8, P {i} (fun u v => (oneEach u v).getD i.val false))
    (meet : ∀ {s t f h}, P s f → P t h → Disjoint s t →
      P (s ∪ t) (fun u v => f u v && h u v))
    (join : ∀ {s t f h}, P s f → P t h → Disjoint s t →
      P (s ∪ t) (fun u v => f u v || h u v))
    (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 7)
    (full : support 8 C C.output = Finset.univ) :
    P Finset.univ (fun u v => C.eval (oneEach u v)) := by
  have ht : ft C.gates {C.output} = Finset.univ := by
    rw [show ft C.gates {C.output} = sup C.gates C.output by simp [ft]]
    exact full
  obtain ⟨_, make⟩ := tree_frontier P atom meet join C.gates hm {C.output}
  have hh : ({C.output} : Finset ℕ).card + C.gates.length ≤
      (ft C.gates {C.output}).card := by
    rw [ht]; simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_fin]
    change C.gates.length ≤ 7 at hs
    omega
  have h := (make hh).1 C.output (Finset.mem_singleton_self _)
  change P (support 8 C C.output) (fun u v => C.eval (oneEach u v)) at h
  rwa [full] at h

-- On each candidate set of leaves the child function must be monotone.
-- Test the possible root partitions on the promised rows, then repeat on
-- the four-input component forced by the unique surviving disjunction.
abbrev Row := Fin 4 × Fin 4
abbrev Inputs := Finset (Fin 8)
abbrev Table4 := Fin 4 → Fin 4 → Bool

inductive IsRO : Inputs → Table4 → Prop where
  | atom (i : Fin 8) : IsRO {i} (fun u v => (oneEach u v).getD i.val false)
  | meet {s t : Inputs} {f g : Table4} (h1 : IsRO s f) (h2 : IsRO t g) (hd : Disjoint s t) :
      IsRO (s ∪ t) (fun u v => f u v && g u v)
  | join {s t : Inputs} {f g : Table4} (h1 : IsRO s f) (h2 : IsRO t g) (hd : Disjoint s t) :
      IsRO (s ∪ t) (fun u v => f u v || g u v)

abbrev leafLE (s : Inputs) (p q : Row) : Prop :=
  (p.1 = q.1 ∨ Fin.castAdd 4 p.1 ∉ s) ∧ (p.2 = q.2 ∨ Fin.natAdd 4 p.2 ∉ s)

def rowMono (s : Inputs) (f : Table4) : Prop :=
  ∀ p q : Row, leafLE s p q → f p.1 p.2 = true → f q.1 q.2 = true

lemma leafLE_weaken {s t : Inputs} (h : s ⊆ t) {p q : Row} (he : leafLE t p q) : leafLE s p q :=
  ⟨he.1.imp_right (fun hn x => hn (h x)), he.2.imp_right (fun hn x => hn (h x))⟩

lemma IsRO.mono {s : Inputs} {f : Table4} (h : IsRO s f) : rowMono s f := by
  induction h with
  | atom i =>
    have all : ∀ (i : Fin 8) (p q : Row), leafLE {i} p q →
        (oneEach p.1 p.2).getD i.val false = true →
        (oneEach q.1 q.2).getD i.val false = true := by decide
    exact all i
  | meet _ _ _ h1 h2 =>
    intro p q hle hp
    exact Bool.and_eq_true_iff.mpr
      ⟨h1 p q (leafLE_weaken Finset.subset_union_left hle) (Bool.and_eq_true_iff.mp hp).1,
       h2 p q (leafLE_weaken Finset.subset_union_right hle) (Bool.and_eq_true_iff.mp hp).2⟩
  | join _ _ _ h1 h2 =>
    intro p q hle hp
    exact Bool.or_eq_true_iff.mpr ((Bool.or_eq_true_iff.mp hp).imp
      (h1 p q (leafLE_weaken Finset.subset_union_left hle))
      (h2 p q (leafLE_weaken Finset.subset_union_right hle)))

lemma IsRO.hasInput {s : Inputs} {f : Table4} (h : IsRO s f) : s.Nonempty := by
  induction h with
  | atom i => exact ⟨i, Finset.mem_singleton_self i⟩
  | meet _ _ _ h1 _ => exact h1.mono Finset.subset_union_left
  | join _ _ _ h1 _ => exact h1.mono Finset.subset_union_left

abbrev hit (f : Table4) (s : Inputs) (p : Row) : Prop :=
  ∀ q : Row, f q.1 q.2 = false → ¬leafLE s p q

abbrev miss (f : Table4) (s : Inputs) (p : Row) : Prop :=
  ∀ q : Row, f q.1 q.2 = true → ¬leafLE s q p

abbrev orSplit (f : Table4) (s t : Inputs) : Prop :=
  ∀ p : Row, f p.1 p.2 = true → hit f s p ∨ hit f t p

abbrev andSplit (f : Table4) (s t : Inputs) : Prop :=
  ∀ p : Row, f p.1 p.2 = false → miss f s p ∨ miss f t p

local instance (f : Table4) (s : Inputs) (p : Row) : Decidable (hit f s p) := by unfold hit; infer_instance
local instance (f : Table4) (s : Inputs) (p : Row) : Decidable (miss f s p) := by unfold miss; infer_instance
local instance (f : Table4) (s t : Inputs) : Decidable (orSplit f s t) := by unfold orSplit; infer_instance
local instance (f : Table4) (s t : Inputs) : Decidable (andSplit f s t) := by unfold andSplit; infer_instance

lemma hit_of_le {f g : Table4} {s : Inputs} (hmono : rowMono s f)
    (hle : ∀ u v, f u v = true → g u v = true) (p : Row) (hp : f p.1 p.2 = true) :
    hit g s p := by
  intro q hq hcmp
  have := hle q.1 q.2 (hmono p q hcmp hp)
  simp_all

lemma splitJoin {f g : Table4} {s t : Inputs} (hf : rowMono s f) (hg : rowMono t g) :
    orSplit (fun u v => f u v || g u v) s t := by
  intro p hp
  rcases Bool.or_eq_true_iff.mp hp with h | h
  · exact Or.inl (hit_of_le hf (fun u v hx => by simp [hx]) p h)
  · exact Or.inr (hit_of_le hg (fun u v hx => by simp [hx]) p h)

lemma splitMeet {f g : Table4} {s t : Inputs} (hf : rowMono s f) (hg : rowMono t g) :
    andSplit (fun u v => f u v && g u v) s t := by
  intro p hp
  by_cases h : f p.1 p.2 = true
  · right
    intro q hq hcmp
    have ht := hg q p hcmp (Bool.and_eq_true_iff.mp hq).2
    simp [h, ht] at hp
  · left
    intro q hq hcmp
    exact h (hf q p hcmp (Bool.and_eq_true_iff.mp hq).1)

def tableOf (n : ℕ) : Table4 := fun u v => n.testBit (4*u.val + v.val)
def s60 : Inputs := {2, 3, 4, 5}
def s195 : Inputs := {0, 1, 6, 7}

set_option maxHeartbeats 2000000 in
lemma onlyFullSplit : ∀ s : Inputs, s.Nonempty → (Finset.univ \ s).Nonempty →
    ¬ andSplit (tableOf 5068) s (Finset.univ \ s) ∧
      (orSplit (tableOf 5068) s (Finset.univ \ s) →
        (s = s60 ∧ Finset.univ \ s = s195) ∨ (s = s195 ∧ Finset.univ \ s = s60)) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
lemma noSmallSplit : ∀ s : Inputs, s ⊆ s60 → s.Nonempty → (s60 \ s).Nonempty →
    ¬ andSplit (tableOf 4864) s (s60 \ s) ∧ ¬ orSplit (tableOf 4864) s (s60 \ s) := by
  decide +kernel

lemma partitionCaps : ∀ p : Row,
    (tableOf 4864 p.1 p.2 = true →
      tableOf 5068 p.1 p.2 = true ∧ ¬ hit (tableOf 5068) s195 p) ∧
    (tableOf 4864 p.1 p.2 = false →
      tableOf 5068 p.1 p.2 = false ∨ ¬ hit (tableOf 5068) s60 p) := by decide

lemma restOfUnion (s t a : Inputs) (dis : Disjoint s t) (h : s ∪ t = a) : a \ s = t := by
  rw [← h]
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_union]
  exact ⟨fun h => h.1.resolve_left h.2, fun hi => ⟨Or.inr hi, fun hs => Finset.disjoint_left.mp dis hs hi⟩⟩

lemma smallImpossible {s : Inputs} {f : Table4} (h : IsRO s f) (hs : s = s60)
    (he : f = tableOf 4864) : False := by
  cases h with
  | atom i =>
    have imp : ∀ i : Fin 8, ({i} : Inputs) ≠ s60 := by decide
    exact imp i hs
  | @meet a b f g ha hb hd =>
    have rst := restOfUnion a b s60 hd hs
    have sub : a ⊆ s60 := hs ▸ Finset.subset_union_left
    have cert := noSmallSplit a sub ha.hasInput (rst ▸ hb.hasInput)
    rw [rst] at cert
    exact cert.1 (he ▸ splitMeet ha.mono hb.mono)
  | @join a b f g ha hb hd =>
    have rst := restOfUnion a b s60 hd hs
    have sub : a ⊆ s60 := hs ▸ Finset.subset_union_left
    have cert := noSmallSplit a sub ha.hasInput (rst ▸ hb.hasInput)
    rw [rst] at cert
    exact cert.2 (he ▸ splitJoin ha.mono hb.mono)

lemma smallComponent {f g : Table4} (hf : rowMono s60 f) (hg : rowMono s195 g)
    (he : (fun u v => f u v || g u v) = tableOf 5068) : f = tableOf 4864 := by
  have fle : ∀ u v, f u v = true → tableOf 5068 u v = true := by
    intro u v h
    rw [← he]
    simp [h]
  have gle : ∀ u v, g u v = true → tableOf 5068 u v = true := by
    intro u v h
    rw [← he]
    simp [h]
  funext u v
  have caps := partitionCaps (u, v)
  cases h : tableOf 4864 u v with
  | false =>
    apply Bool.eq_false_iff.mpr
    intro hp
    rcases caps.2 h with hno | hno
    · have ht := fle u v hp
      exact Bool.noConfusion (hno.symm.trans ht)
    · exact hno (hit_of_le hf fle (u,v) hp)
  | true =>
    rcases caps.1 h with ⟨ht, hno⟩
    rw [← he] at ht
    rcases Bool.or_eq_true_iff.mp ht with hp | hp
    · exact hp
    · exact False.elim (hno (hit_of_le hg gle (u,v) hp))

lemma fullImpossible {s : Inputs} {f : Table4} (h : IsRO s f) (hs : s = Finset.univ)
    (he : f = tableOf 5068) : False := by
  cases h with
  | atom i =>
    have imp : ∀ i : Fin 8, ({i} : Inputs) ≠ Finset.univ := by decide
    exact imp i hs
  | @meet a b f g ha hb hd =>
    have rst := restOfUnion a b Finset.univ hd hs
    have cert := onlyFullSplit a ha.hasInput (rst ▸ hb.hasInput)
    rw [rst] at cert
    exact cert.1 (he ▸ splitMeet ha.mono hb.mono)
  | @join a b f g ha hb hd =>
    have rst := restOfUnion a b Finset.univ hd hs
    have cert := onlyFullSplit a ha.hasInput (rst ▸ hb.hasInput)
    rw [rst] at cert
    rcases cert.2 (he ▸ splitJoin ha.mono hb.mono) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact smallImpossible ha rfl (smallComponent ha.mono hb.mono he)
    · have rev : (fun u v => g u v || f u v) = tableOf 5068 := by
        simpa only [Bool.or_comm] using he
      exact smallImpossible hb rfl (smallComponent hb.mono ha.mono rev)

lemma notRO : ¬ IsRO Finset.univ (fun u v : Fin 4 => (5068 : ℕ).testBit (4*u.val+v.val)) :=
  fun h => fullImpossible h rfl rfl

end PEqualNP.Outside.L_meta_6055

theorem PEqualNP.Outside.L_meta_6055 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (5068 : ℕ).testBit (4 * u.val + v.val)) 8 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (5068 : ℕ).testBit (4 * u.val + v.val)) 7 := by
  refine ⟨PEqualNP.Outside.L_meta_6055.upper, ?_⟩
  rintro ⟨C, hm, hs, hr⟩
  have full := PEqualNP.Outside.L_meta_6055.necessaryInputs C hm hr
  have tree := PEqualNP.Outside.L_meta_6055.readOnce_of_full
    PEqualNP.Outside.L_meta_6055.IsRO PEqualNP.Outside.L_meta_6055.IsRO.atom
    PEqualNP.Outside.L_meta_6055.IsRO.meet PEqualNP.Outside.L_meta_6055.IsRO.join C hm hs full
  have correctness : (fun u v => C.eval (oneEach u v)) = PEqualNP.Outside.L_meta_6055.graph5068 :=
    funext fun u => funext fun v => hr u v
  rw [correctness] at tree
  exact PEqualNP.Outside.L_meta_6055.notRO tree
