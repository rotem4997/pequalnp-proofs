import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SDiff
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10057_aux.Packing
abbrev V := Fin 78
abbrev I := Fin 17
def path : I → Fin 4 → V := ![![14,66,1,52],
    ![15,67,2,53],
    ![16,43,30,56],
    ![17,44,31,57],
    ![20,72,7,58],
    ![21,73,8,59],
    ![22,49,36,62],
    ![23,50,37,63],
    ![26,39,25,77],
    ![27,40,13,65],
    ![28,54,3,68],
    ![29,55,4,69],
    ![32,45,18,70],
    ![33,46,19,71],
    ![34,60,9,74],
    ![35,61,10,75],
    ![38,51,24,76]]
def color (v : V) : Bool := decide (v.val < 39)
def single (a b : ℕ) : Bool := decide (a<26 ∧ (b=(a % 13+1)%13 ∨ b=26+a % 13))
def original (a b : Fin 39) : Bool := decide (∃ i : Fin 13,
  ((a.val = i.val ∨ a.val = 13+i.val) ∧ (b.val = (i.val+1)%13 ∨ b.val = 26+i.val)) ∨
  ((b.val = i.val ∨ b.val = 13+i.val) ∧ (a.val = (i.val+1)%13 ∨ a.val = 26+i.val)))
def edge (a b : V) : Bool := if color a = color b then false else
  single (a.val % 39) (b.val % 39) || single (b.val % 39) (a.val % 39)
set_option maxRecDepth 10000 in
theorem graph_exact : ∀ a b : Fin 39, original a b = (single a.val b.val || single b.val a.val) := by decide +kernel
set_option maxRecDepth 10000 in
theorem paths_valid : ∀ i : I,
  path i 0 ≠ path i 2 ∧ path i 1 ≠ path i 3 ∧
  color (path i 0) = color (path i 2) ∧ color (path i 1) = color (path i 3) ∧
  color (path i 0) ≠ color (path i 1) ∧
  edge (path i 0) (path i 1) = true ∧ edge (path i 2) (path i 1) = true ∧
  edge (path i 2) (path i 3) = true ∧ edge (path i 0) (path i 3) = false := by decide +kernel
def separated (i j : I) : Prop := ∀ a b : Fin 4, color (path i a) = color (path j b) →
    ∃ c : Fin 4,
      edge (path i a) (path i c) ≠ edge (path j b) (path i c) ∨
      edge (path i a) (path j c) ≠ edge (path j b) (path j c)
instance (i j : I) : Decidable (separated i j) := by unfold separated; infer_instance
set_option maxRecDepth 10000 in
private theorem sep_0 : ∀ j : I, (0 : I) ≠ j → separated 0 j := by decide +kernel
set_option maxRecDepth 10000 in
private theorem sep_1 : ∀ j : I, (1 : I) ≠ j → separated 1 j := by decide +kernel
set_option maxRecDepth 10000 in
private theorem sep_2 : ∀ j : I, (2 : I) ≠ j → separated 2 j := by decide +kernel
set_option maxRecDepth 10000 in
private theorem sep_3 : ∀ j : I, (3 : I) ≠ j → separated 3 j := by decide +kernel
set_option maxRecDepth 10000 in
private theorem sep_4 : ∀ j : I, (4 : I) ≠ j → separated 4 j := by decide +kernel
set_option maxRecDepth 10000 in
private theorem sep_5 : ∀ j : I, (5 : I) ≠ j → separated 5 j := by decide +kernel
set_option maxRecDepth 10000 in
private theorem sep_6 : ∀ j : I, (6 : I) ≠ j → separated 6 j := by decide +kernel
set_option maxRecDepth 10000 in
private theorem sep_7 : ∀ j : I, (7 : I) ≠ j → separated 7 j := by decide +kernel
set_option maxRecDepth 10000 in
private theorem sep_8 : ∀ j : I, (8 : I) ≠ j → separated 8 j := by decide +kernel
set_option maxRecDepth 10000 in
private theorem sep_9 : ∀ j : I, (9 : I) ≠ j → separated 9 j := by decide +kernel
set_option maxRecDepth 10000 in
private theorem sep_10 : ∀ j : I, (10 : I) ≠ j → separated 10 j := by decide +kernel
set_option maxRecDepth 10000 in
private theorem sep_11 : ∀ j : I, (11 : I) ≠ j → separated 11 j := by decide +kernel
set_option maxRecDepth 10000 in
private theorem sep_12 : ∀ j : I, (12 : I) ≠ j → separated 12 j := by decide +kernel
set_option maxRecDepth 10000 in
private theorem sep_13 : ∀ j : I, (13 : I) ≠ j → separated 13 j := by decide +kernel
set_option maxRecDepth 10000 in
private theorem sep_14 : ∀ j : I, (14 : I) ≠ j → separated 14 j := by decide +kernel
set_option maxRecDepth 10000 in
private theorem sep_15 : ∀ j : I, (15 : I) ≠ j → separated 15 j := by decide +kernel
set_option maxRecDepth 10000 in
private theorem sep_16 : ∀ j : I, (16 : I) ≠ j → separated 16 j := by decide +kernel
theorem separated_all (i j : I) (ne : i ≠ j) : separated i j := by
  fin_cases i
  · exact sep_0 _ ne
  · exact sep_1 _ ne
  · exact sep_2 _ ne
  · exact sep_3 _ ne
  · exact sep_4 _ ne
  · exact sep_5 _ ne
  · exact sep_6 _ ne
  · exact sep_7 _ ne
  · exact sep_8 _ ne
  · exact sep_9 _ ne
  · exact sep_10 _ ne
  · exact sep_11 _ ne
  · exact sep_12 _ ne
  · exact sep_13 _ ne
  · exact sep_14 _ ne
  · exact sep_15 _ ne
  · exact sep_16 _ ne

end PEqualNP.Outside.L_meta_10057_aux.Packing

namespace PEqualNP.Outside.L_meta_10057_aux.Packing
def intact (W : Finset V) : Finset I := Finset.univ.filter fun i => ∀ a, path i a ∈ W
def hit (S W : Finset V) (b : Bool) : Finset I :=
  (intact W).filter fun i => ∃ a, path i a ∈ S ∧ color (path i a) = b
def twins (S W : Finset V) : Prop := ∀ u ∈ S, ∀ v ∈ S, color u = color v →
  ∀ z ∈ W, edge u z = edge v z
lemma at_most_one (S W : Finset V) (b : Bool) (good : twins S W) : (hit S W b).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra ne
  obtain ⟨iW,a,ha,ca⟩ := Finset.mem_filter.mp hi
  obtain ⟨jW,b',hb,cb⟩ := Finset.mem_filter.mp hj
  have ci := (Finset.mem_filter.mp iW).2
  have cj := (Finset.mem_filter.mp jW).2
  obtain ⟨v,d⟩ := separated_all i j ne a b' (ca.trans cb.symm)
  rcases d with l|r
  · exact l (good _ ha _ hb (ca.trans cb.symm) _ (ci v))
  · exact r (good _ ha _ hb (ca.trans cb.symm) _ (cj v))
lemma step (S W : Finset V) (good : twins S W) :
    (intact W).card ≤ (intact (W \ S)).card + 2 := by
  have sub : intact W ⊆ intact (W \ S) ∪ (hit S W true ∪ hit S W false) := by
    intro i hi
    by_cases stays : i ∈ intact (W \ S)
    · exact Finset.mem_union_left _ stays
    · apply Finset.mem_union_right
      have hW := (Finset.mem_filter.mp hi).2
      have hS : ∃ a, path i a ∈ S := by
        by_contra! empty
        apply stays
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun a => Finset.mem_sdiff.mpr ⟨hW a,empty a⟩⟩
      obtain ⟨a,ha⟩ := hS
      cases eq : color (path i a)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi,a,ha,eq⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi,a,ha,eq⟩)
  have c := Finset.card_le_card sub
  have g := Finset.card_union_le (intact (W \ S)) (hit S W true ∪ hit S W false)
  have h := Finset.card_union_le (hit S W true) (hit S W false)
  have x := at_most_one S W true good
  have y := at_most_one S W false good
  omega
def untouched (S W : Finset V) := ∀ i ∈ intact W, ∀ a, path i a ∉ S
lemma no_step (S W : Finset V) (h : untouched S W) : intact W ⊆ intact (W \ S) := by
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun a =>
    Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hi).2 a,h _ hi _⟩⟩
lemma step_general (S W : Finset V) (h : twins S W ∨ untouched S W) :
    (intact W).card ≤ (intact (W \ S)).card + 2 := by
  rcases h with a|b
  · exact step _ _ a
  · have le := Finset.card_le_card (no_step S W b)
    omega
def Removable : ℕ → Finset V → Prop
  | 0,W => (intact W).card = 0
  | k+1,W => (intact W).card = 0 ∨ ∃ S, (twins S W ∨ untouched S W) ∧ Removable k (W \ S)
theorem packing_bound {k W} (h : Removable k W) : (intact W).card ≤ 2*k := by
  induction k generalizing W with
  | zero => simpa [Removable] using h.le
  | succ k ih =>
    rcases h with empty|⟨S,permitted,rest⟩
    · omega
    · have a := step_general S W permitted
      have b := ih rest
      omega
theorem at_least_nine {k} (h : Removable k Finset.univ) : 9 ≤ k := by
  have cards : (intact Finset.univ).card = 17 := by simp [intact]
  have n := packing_bound h
  omega
end PEqualNP.Outside.L_meta_10057_aux.Packing

namespace PEqualNP.Outside.L_meta_10057_aux.Cycle

inductive Tree (V : Type) where
  | input : V → Tree V
  | all : Tree V → Tree V → Tree V
  | any : Tree V → Tree V → Tree V

namespace Tree
variable {V : Type} [DecidableEq V]

def leaves : Tree V → Finset V
  | .input u => {u}
  | .all a b | .any a b => a.leaves ∪ b.leaves

def linear : Tree V → Prop
  | .input _ => True
  | .all a b | .any a b => a.linear ∧ b.linear ∧ Disjoint a.leaves b.leaves

def eval (A : Finset V) : Tree V → Bool
  | .input u => decide (u∈A)
  | .all a b => eval A a && eval A b
  | .any a b => eval A a || eval A b

lemma eval_congr (T : Tree V) (A B : Finset V)
    (h : ∀ w ∈ T.leaves, w∈A ↔ w∈B) : T.eval A = T.eval B := by
  induction T with
  | input u => simpa [leaves,eval] using h u (by simp [leaves])
  | all l r il ir =>
    simp only [eval]
    rw [il (fun w hw => h w (by simp [leaves,hw])),
        ir (fun w hw => h w (by simp [leaves,hw]))]
  | any l r il ir =>
    simp only [eval]
    rw [il (fun w hw => h w (by simp [leaves,hw])),
        ir (fun w hw => h w (by simp [leaves,hw]))]

lemma eval_empty (T : Tree V) : T.eval ∅ = false := by
  induction T with
  | input u => simp [eval]
  | all a b ha hb => simp [eval,ha,hb]
  | any a b ha hb => simp [eval,ha,hb]

lemma pair_missing (T : Tree V) (a b : V) (ha : a∉T.leaves) :
    T.eval {a,b} = T.eval {b} := by
  apply eval_congr
  intro v hv
  have ne : v≠a := fun h => ha (h ▸ hv)
  simp [ne]

lemma pair_swap (T : Tree V) (a b : V) :
    T.eval {a,b} = T.eval {b,a} := by rw [Finset.pair_comm]

lemma pair_present (T : Tree V) (a b : V) (yes : T.eval {a,b} = true) :
    a∈T.leaves ∨ b∈T.leaves := by
  by_contra no
  push Not at no
  have e : T.eval {a,b} = T.eval ∅ := by
    apply eval_congr
    intro v hv
    have na : v≠a := fun h => no.1 (h ▸ hv)
    have nb : v≠b := fun h => no.2 (h ▸ hv)
    simp [na,nb]
  rw [e,eval_empty] at yes
  contradiction

lemma pair_needs_both (T : Tree V) (zero : ∀ a, T.eval {a} = false)
    (a b : V) (yes : T.eval {a,b} = true) : a∈T.leaves ∧ b∈T.leaves := by
  constructor
  · by_contra no
    rw [pair_missing T a b no,zero] at yes
    contradiction
  · by_contra no
    rw [pair_swap, pair_missing T b a no,zero] at yes
    contradiction

lemma both_cross (L R : Tree V) (dis : Disjoint L.leaves R.leaves)
    (a b : V) (left : L.eval {a,b}=true) (right : R.eval {a,b}=true) :
    (a∈L.leaves ∧ b∈R.leaves) ∨ (a∈R.leaves ∧ b∈L.leaves) := by
  have nd := Finset.disjoint_left.mp dis
  rcases pair_present L a b left with La | Lb
  · rcases pair_present R a b right with Ra | Rb
    · exact (nd La Ra).elim
    · exact Or.inl ⟨La,Rb⟩
  · rcases pair_present R a b right with Ra | Rb
    · exact Or.inr ⟨Ra,Lb⟩
    · exact (nd Lb Rb).elim

lemma or_truth {a b : Bool} : (a || b)=true ↔ a=true ∨ b=true := by
  cases a <;> cases b <;> decide

lemma and_truth {a b : Bool} : (a && b)=true ↔ a=true ∧ b=true := by
  cases a <;> cases b <;> decide

theorem linear_no_induced_path (T : Tree V) (linearT : T.linear)
    (zero : ∀ i, T.eval {i}=false) (a b c d : V)
    (ab : T.eval {a,b}=true) (bc : T.eval {b,c}=true) (cd : T.eval {c,d}=true)
    (ad : T.eval {a,d}=false) : False := by
  induction T with
  | input u =>
    have bad := (pair_needs_both (.input u) zero a b ab).1
    have e : a=u := by simpa [leaves] using bad
    subst a
    have h := zero u
    simp [eval] at h
  | any L R ihL ihR =>
    obtain ⟨linearL,linearR,dis⟩ := linearT
    have nd := Finset.disjoint_left.mp dis
    have parts (A : Finset V) (h : (L.eval A || R.eval A)=false) :
        L.eval A=false ∧ R.eval A=false := by
      cases ea : L.eval A <;> cases eb : R.eval A <;> simp_all
    have noL (w : V) : L.eval {w}=false := (parts {w} (zero w)).1
    have noR (w : V) : R.eval {w}=false := (parts {w} (zero w)).2
    have negL : L.eval {a,d}=false := (parts {a,d} ad).1
    have negR : R.eval {a,d}=false := (parts {a,d} ad).2
    change (L.eval {a,b} || R.eval {a,b})=true at ab
    change (L.eval {b,c} || R.eval {b,c})=true at bc
    change (L.eval {c,d} || R.eval {c,d})=true at cd
    rcases or_truth.mp ab with lab | rab
    · have bl := (pair_needs_both L noL a b lab).2
      have lbc : L.eval {b,c}=true := (or_truth.mp bc).resolve_right
        (fun h => nd bl (pair_needs_both R noR b c h).1)
      have cl := (pair_needs_both L noL b c lbc).2
      have lcd : L.eval {c,d}=true := (or_truth.mp cd).resolve_right
        (fun h => nd cl (pair_needs_both R noR c d h).1)
      exact ihL linearL noL lab lbc lcd negL
    · have br := (pair_needs_both R noR a b rab).2
      have rbc : R.eval {b,c}=true := (or_truth.mp bc).resolve_left
        (fun h => nd (pair_needs_both L noL b c h).1 br)
      have cr := (pair_needs_both R noR b c rbc).2
      have rcd : R.eval {c,d}=true := (or_truth.mp cd).resolve_left
        (fun h => nd (pair_needs_both L noL c d h).1 cr)
      exact ihR linearR noR rab rbc rcd negR
  | all L R ihL ihR =>
    obtain ⟨linearL,linearR,dis⟩ := linearT
    have nd := Finset.disjoint_left.mp dis
    change (L.eval {a,b} && R.eval {a,b})=true at ab
    change (L.eval {b,c} && R.eval {b,c})=true at bc
    change (L.eval {c,d} && R.eval {c,d})=true at cd
    change (L.eval {a,d} && R.eval {a,d})=false at ad
    obtain ⟨al,ar⟩ := and_truth.mp ab
    obtain ⟨bl,br⟩ := and_truth.mp bc
    obtain ⟨cl,cr⟩ := and_truth.mp cd
    rcases both_cross L R dis a b al ar with ⟨aL,bR⟩ | ⟨aR,bL⟩
    · have cL := ((both_cross L R dis b c bl br).resolve_left (fun h => nd h.1 bR)).2
      have dR := ((both_cross L R dis c d cl cr).resolve_right (fun h => nd cL h.1)).2
      have ansL : L.eval {a}=true := by rwa [pair_swap, pair_missing L b a (fun h => nd h bR)] at al
      have ansR : R.eval {d}=true := by rwa [pair_missing R c d (nd cL)] at cr
      rw [pair_swap L a d,pair_missing L d a (fun h => nd h dR),pair_missing R a d (nd aL),
        ansL,ansR] at ad
      contradiction
    · have cR := ((both_cross L R dis b c bl br).resolve_right (fun h => nd bL h.1)).2
      have dL := ((both_cross L R dis c d cl cr).resolve_left (fun h => nd h.1 cR)).2
      have ansR : R.eval {a}=true := by rwa [pair_swap,pair_missing R b a (nd bL)] at ar
      have ansL : L.eval {d}=true := by rwa [pair_missing L c d (fun h => nd h cR)] at cl
      rw [pair_missing L a d (fun h => nd h aR),pair_swap R a d,pair_missing R d a (nd dL),
        ansR,ansL] at ad
      contradiction
end Tree
end PEqualNP.Outside.L_meta_10057_aux.Cycle

namespace PEqualNP.Outside.L_meta_10057_aux.Cycle

variable {V : Type} [DecidableEq V]

def folded (S : Finset V) (h : Finset V → Bool) (g : Finset V → Bool → Bool)
    (A : Finset V) : Bool := g (A \ S) (h (A ∩ S))

lemma split_cross (S : Finset V) (u v : V) (uS : u ∈ S) (vS : v ∉ S) :
    ({u,v} : Finset V) \ S = {v} ∧ ({u,v} : Finset V) ∩ S = {u} := by
  constructor <;> ext i
  all_goals
    by_cases eu : i=u
    · subst i
      have ne : u ≠ v := fun eq => vS (eq ▸ uS)
      simp [uS,ne]
    · by_cases ev : i=v
      · subst i
        simp [vS,eu]
      · simp [eu,ev]

lemma split_outside (S : Finset V) (v : V) (vS : v ∉ S) :
    ({v} : Finset V) \ S = {v} ∧ ({v} : Finset V) ∩ S = ∅ := by
  constructor <;> ext i
  all_goals
    by_cases eq : i=v
    · subst i; simp [vS]
    · simp [eq]

lemma split_inside (S A : Finset V) (inside : A ⊆ S) : A \ S = ∅ ∧ A ∩ S = A := by
  constructor <;> ext i
  all_goals
    by_cases h : i ∈ A
    · simp [h,inside h]
    · simp [h]

lemma cross_values (S : Finset V) (h : Finset V → Bool) (g : Finset V → Bool → Bool)
    (mono : ∀ A B, A ⊆ B → h A = true → h B = true)
    (single : ∀ a, folded S h g {a} = false)
    (u v : V) (uS : u∈S) (vS : v∉S) (hit : folded S h g {u,v} = true) :
    h ∅ = false ∧ h {u} = true := by
  obtain ⟨a,b⟩ := split_cross S u v uS vS
  obtain ⟨c,d⟩ := split_outside S v vS
  have neg := single v
  unfold folded at hit neg
  rw [a,b] at hit
  rw [c,d] at neg
  have diff : h {u} ≠ h ∅ := by
    intro eq
    rw [eq,neg] at hit
    contradiction
  cases z : h ∅
  · refine ⟨rfl,?_⟩
    cases p : h {u}
    · exact False.elim (diff (p.trans z.symm))
    · rfl
  · exact False.elim (diff ((mono ∅ {u} (Finset.empty_subset _) z).trans z.symm))

theorem exclusive_independent (G : SimpleGraph V) (S : Finset V)
    (h : Finset V → Bool) (g : Finset V → Bool → Bool)
    (mono : ∀ A B, A ⊆ B → h A = true → h B = true)
    (outer : ∀ A, g A false = true → g A true = true)
    (single : ∀ a, folded S h g {a} = false)
    (positive : ∀ a b, G.Adj a b → folded S h g {a,b} = true)
    (cross : ∃ a∈S, ∃ b∉S, G.Adj a b) :
    (∀ a∈S, ∀ b∈S, ¬ G.Adj a b) := by
  obtain ⟨u,uS,v,vS,edge⟩ := cross
  obtain ⟨zero,one⟩ := cross_values S h g mono single u v uS vS (positive u v edge)
  have forbidden : g ∅ true = false := by
    have sub : ({u} : Finset V) ⊆ S := by simpa using uS
    have m := single u
    obtain ⟨a,b⟩ := split_inside S {u} sub
    unfold folded at m
    rwa [a,b,one] at m
  have independent : ∀ a∈S, ∀ b∈S, ¬ G.Adj a b := by
    intro a aS b bS adj
    have sub : ({a,b} : Finset V) ⊆ S := by
      intro k hk
      rw [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact aS
      · exact bS
    have pp := positive a b adj
    obtain ⟨c,d⟩ := split_inside S {a,b} sub
    unfold folded at pp
    rw [c,d] at pp
    cases hh : h {a,b}
    · rw [hh] at pp
      have impossible := outer ∅ pp
      rw [forbidden] at impossible
      contradiction
    · rw [hh,forbidden] at pp
      contradiction
  exact independent

theorem exclusive_support_or (G : SimpleGraph V) (S : Finset V)
    (h : Finset V → Bool) (g : Finset V → Bool → Bool)
    (mono : ∀ A B, A ⊆ B → h A = true → h B = true)
    (outer : ∀ A, g A false = true → g A true = true)
    (single : ∀ a, folded S h g {a} = false)
    (positive : ∀ a b, G.Adj a b → folded S h g {a,b} = true)
    (incident : ∀ a ∈ S, ∃ b, G.Adj a b)
    (cross : ∃ a∈S, ∃ b∉S, G.Adj a b) :
    (∀ a∈S, ∀ b∈S, ¬ G.Adj a b) ∧
      (∀ A ⊆ S, h A = decide A.Nonempty) := by
  obtain ⟨u,uS,v,vS,edge⟩ := cross
  obtain ⟨zero,one⟩ := cross_values S h g mono single u v uS vS (positive u v edge)
  have forbidden : g ∅ true = false := by
    have sub : ({u} : Finset V) ⊆ S := by simpa using uS
    have m := single u
    obtain ⟨a,b⟩ := split_inside S {u} sub
    unfold folded at m
    rwa [a,b,one] at m
  have independent : ∀ a∈S, ∀ b∈S, ¬ G.Adj a b := by
    intro a aS b bS adj
    have sub : ({a,b} : Finset V) ⊆ S := by
      intro k hk
      rw [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact aS
      · exact bS
    have pp := positive a b adj
    obtain ⟨c,d⟩ := split_inside S {a,b} sub
    unfold folded at pp
    rw [c,d] at pp
    cases hh : h {a,b}
    · rw [hh] at pp
      have impossible := outer ∅ pp
      rw [forbidden] at impossible
      contradiction
    · rw [hh,forbidden] at pp
      contradiction
  refine ⟨independent,?_⟩
  intro A incl
  by_cases ne : A.Nonempty
  · obtain ⟨a,ha⟩ := ne
    obtain ⟨b,adj⟩ := incident a (incl ha)
    have bS : b∉S := fun bs => independent a (incl ha) b bs adj
    have oneA := (cross_values S h g mono single a b (incl ha) bS (positive a b adj)).2
    rw [decide_eq_true (show A.Nonempty from ⟨a,ha⟩)]
    exact mono {a} A (by simpa) oneA
  · rw [Finset.not_nonempty_iff_eq_empty.mp ne,zero]
    simp
end PEqualNP.Outside.L_meta_10057_aux.Cycle

namespace PEqualNP.Outside.L_meta_10057_aux.Cycle
variable {V : Type} [DecidableEq V]

def Path4 (G : SimpleGraph V) (a b c d : V) : Prop :=
  G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ ¬ G.Adj a d

lemma opposite_ends (G : SimpleGraph V) (colour : V → Bool)
    (bip : ∀ a b, G.Adj a b → colour a ≠ colour b)
    {a b c d : V} (p : Path4 G a b c d) : colour a ≠ colour d := by
  have ab := bip a b p.1
  have bc := bip b c p.2.1
  have cd := bip c d p.2.2.1
  cases ea : colour a <;> cases eb : colour b <;>
    cases ec : colour c <;> cases ed : colour d <;> simp_all

lemma exclusive_no_cross {G : SimpleGraph V} [DecidableRel G.Adj]
    (colour : V → Bool) (bip : ∀ a b, G.Adj a b → colour a ≠ colour b)
    (S : Finset V) (h : Finset V → Bool) (g : Finset V → Bool → Bool)
    (zer : folded S h g ∅=false) (single : ∀ a, folded S h g {a}=false)
    (correct : ∀ a b, colour a ≠ colour b → folded S h g {a,b}=decide (G.Adj a b))
    (T : Tree V) (linear : T.linear) (deps : T.leaves ⊆ S)
    (core : ∀ A ⊆ S, h A=T.eval A)
    (noCross : ∀ a∈S, ∀ b∉S, ¬ G.Adj a b)
    {a b c d : V} (p : Path4 G a b c d) :
    a∉S ∧ b∉S ∧ c∉S ∧ d∉S := by
  have reach {u v : V} (adj : G.Adj u v) (mem : u∈S) : v∈S :=
    by by_contra no; exact noCross u mem v no adj
  have noA : a∉S := by
    intro aS
    have bS := reach p.1 aS
    have cS := reach p.2.1 bS
    have dS := reach p.2.2.1 cS
    have collapse (A : Finset V) (subset : A ⊆ S) :
        folded S h g A = g ∅ (T.eval A) := by
      obtain ⟨outside,inside⟩ := split_inside S A subset
      unfold folded
      rw [outside,inside,core A subset]
    have pair_sub {u v : V} (hu : u ∈ S) (hv : v ∈ S) :
        ({u,v} : Finset V) ⊆ S := by
      intro w hw
      rw [Finset.mem_insert,Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hu
      · exact hv
    have g0 : g ∅ false = false := by
      rwa [collapse ∅ (Finset.empty_subset _),Tree.eval_empty] at zer
    have g1 : g ∅ true = true := by
      have hit := correct a b (bip a b p.1)
      rw [collapse {a,b} (pair_sub aS bS), decide_eq_true p.1] at hit
      cases ev : T.eval {a,b}
      · rw [ev,g0] at hit
        contradiction
      · exact ev ▸ hit
    have go (A : Finset V) (sub : A ⊆ S) : folded S h g A = T.eval A := by
      rw [collapse A sub]
      cases e : T.eval A <;> assumption
    have one (u : V) : T.eval {u}=false := by
      by_cases mem : u∈S
      · rw [← go {u} (by simpa using mem)]
        exact single u
      · rw [← Tree.eval_empty T]
        apply Tree.eval_congr
        intro w hw
        have ne : w≠u := fun eq => mem (eq ▸ deps hw)
        simp [ne]
    have ab : T.eval {a,b}=true := by
      rw [← go {a,b} (pair_sub aS bS), correct a b (bip a b p.1),decide_eq_true p.1]
    have bc : T.eval {b,c}=true := by
      rw [← go {b,c} (pair_sub bS cS), correct b c (bip b c p.2.1),decide_eq_true p.2.1]
    have cd : T.eval {c,d}=true := by
      rw [← go {c,d} (pair_sub cS dS), correct c d (bip c d p.2.2.1),decide_eq_true p.2.2.1]
    have ad : T.eval {a,d}=false := by
      rw [← go {a,d} (pair_sub aS dS), correct a d (opposite_ends G colour bip p),
        decide_eq_false p.2.2.2]
    exact Tree.linear_no_induced_path T linear one a b c d ab bc cd ad
  have noB : b∉S := fun inB => noA (reach p.1.symm inB)
  have noC : c∉S := fun inC => noB (reach p.2.1.symm inC)
  have noD : d∉S := fun inD => noC (reach p.2.2.1.symm inD)
  exact ⟨noA,noB,noC,noD⟩

theorem exclusive_cut_twins {G : SimpleGraph V} [DecidableRel G.Adj]
    (colour : V → Bool) (bip : ∀ a b, G.Adj a b → colour a ≠ colour b)
    (S : Finset V) (h : Finset V → Bool) (g : Finset V → Bool → Bool)
    (mono : ∀ A B, A ⊆ B → h A = true → h B = true)
    (outer : ∀ A, g A false = true → g A true = true)
    (single : ∀ a, folded S h g {a}=false)
    (correct : ∀ a b, colour a ≠ colour b → folded S h g {a,b}=decide (G.Adj a b))
    (incident : ∀ a∈S, ∃ b, G.Adj a b) (cross : ∃ a∈S, ∃ b∉S, G.Adj a b) :
    (∀ a∈S, ∀ b∈S, ¬ G.Adj a b) ∧
      (∀ u∈S, ∀ v∈S, colour u=colour v → ∀ w, G.Adj u w ↔ G.Adj v w) := by
  have positive (a b : V) (adj : G.Adj a b) : folded S h g {a,b}=true := by
    rw [correct a b (bip a b adj),decide_eq_true adj]
  obtain ⟨indep,core⟩ := exclusive_support_or G S h g mono outer single positive incident cross
  refine ⟨indep,?_⟩
  intro u uS v vS same w
  by_cases inS : w ∈ S
  · exact (iff_of_false (indep u uS w inS) (indep v vS w inS))
  by_cases eq : colour u = colour w
  · exact iff_of_false (fun adj => (bip u w adj) eq) (fun adj => (bip v w adj) (same.symm.trans eq))
  have val (a : V) (aS : a∈S) : folded S h g {a,w}=g {w} true := by
    obtain ⟨x,y⟩ := split_cross S a w aS inS
    unfold folded
    rw [x,y,core {a} (by simpa using aS)]
    simp
  have sameBool : decide (G.Adj u w) = decide (G.Adj v w) := by
    rw [← correct u w eq,← correct v w (fun e => eq (same.trans e)),val u uS,val v vS]
  constructor
  · intro h
    apply of_decide_eq_true
    rwa [← sameBool, decide_eq_true h]
  · intro h
    apply of_decide_eq_true
    rwa [sameBool, decide_eq_true h]

theorem exclusive_cut_twins_incident {G : SimpleGraph V} [DecidableRel G.Adj]
    (colour : V → Bool) (bip : ∀ a b, G.Adj a b → colour a ≠ colour b)
    (S : Finset V) (h : Finset V → Bool) (g : Finset V → Bool → Bool)
    (mono : ∀ A B, A ⊆ B → h A = true → h B = true)
    (outer : ∀ A, g A false = true → g A true = true)
    (single : ∀ a, folded S h g {a}=false)
    (correct : ∀ a b, colour a ≠ colour b → folded S h g {a,b}=decide (G.Adj a b))
    (cross : ∃ a∈S, ∃ b∉S, G.Adj a b) :
    (∀ a∈S, ∀ b∈S, ¬ G.Adj a b) ∧
      (∀ u∈S, ∀ v∈S, (∃ q, G.Adj u q) → (∃ q, G.Adj v q) →
        colour u=colour v → ∀ w, G.Adj u w ↔ G.Adj v w) := by
  have positive (a b : V) (adj : G.Adj a b) : folded S h g {a,b}=true := by
    rw [correct a b (bip a b adj),decide_eq_true adj]
  have indep := exclusive_independent G S h g mono outer single positive cross
  refine ⟨indep,?_⟩
  intro u uS v vS uActive vActive same w
  by_cases inS : w ∈ S
  · exact (iff_of_false (indep u uS w inS) (indep v vS w inS))
  by_cases eq : colour u = colour w
  · exact iff_of_false (fun adj => (bip u w adj) eq) (fun adj => (bip v w adj) (same.symm.trans eq))
  have val (a : V) (aS : a∈S) (active : ∃ q, G.Adj a q) :
      folded S h g {a,w}=g {w} true := by
    obtain ⟨q,hq⟩ := active
    have qout : q∉S := fun qs => indep a aS q qs hq
    have yes := (cross_values S h g mono single a q aS qout (positive a q hq)).2
    obtain ⟨x,y⟩ := split_cross S a w aS inS
    unfold folded
    rw [x,y,yes]
  have sameBool : decide (G.Adj u w) = decide (G.Adj v w) := by
    rw [← correct u w eq,← correct v w (fun e => eq (same.trans e)),val u uS uActive,val v vS vActive]
  constructor
  · intro h
    apply of_decide_eq_true
    rwa [← sameBool, decide_eq_true h]
  · intro h
    apply of_decide_eq_true
    rwa [sameBool, decide_eq_true h]
end PEqualNP.Outside.L_meta_10057_aux.Cycle

namespace PEqualNP.Outside.L_meta_10057_aux.Packing
open PEqualNP.Outside.L_meta_10057_aux.Cycle
theorem edge_symm (a b : V) : edge a b = edge b a := by
  unfold edge
  by_cases eq : color a = color b
  · simp [eq]
  · simp [eq,Ne.symm eq,Bool.or_comm]
def graphOn (W : Finset V) : SimpleGraph V where
  Adj a b := a∈W ∧ b∈W ∧ edge a b=true
  symm := ⟨fun a b h => ⟨h.2.1,h.1,(edge_symm _ _).symm ▸ h.2.2⟩⟩
  loopless := ⟨fun v h => by simpa [edge] using h.2.2⟩
instance (W : Finset V) : DecidableRel (graphOn W).Adj :=
  fun a b => inferInstanceAs (Decidable (a∈W ∧ b∈W ∧ edge a b=true))
theorem bip (W : Finset V) (a b : V) (h : (graphOn W).Adj a b) : color a ≠ color b := by
  intro eq
  simpa [edge,eq] using h.2.2
theorem path_in (W : Finset V) (i : I) (hi : i∈intact W) :
    Path4 (graphOn W) (path i 0) (path i 1) (path i 2) (path i 3) := by
  obtain ⟨_,_,_,_,_,e1,e2,e3,n4⟩ := paths_valid i
  have mem := (Finset.mem_filter.mp hi).2
  exact ⟨⟨mem 0,mem 1,e1⟩,⟨mem 1,mem 2,(edge_symm _ _).symm ▸ e2⟩,
    ⟨mem 2,mem 3,e3⟩,fun h => Bool.false_ne_true (n4.symm.trans h.2.2)⟩
def Describes (W : Finset V) (f : Finset V → Bool) := (∀ a, f {a}=false) ∧
  ∀ a b, color a ≠ color b → f {a,b} = decide ((graphOn W).Adj a b)
theorem linear_empty (W : Finset V) (T : PEqualNP.Outside.L_meta_10057_aux.Cycle.Tree V) (lin : T.linear) (h : Describes W T.eval) :
    (intact W).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨ab,bc,cd,ad⟩ := path_in W i hi
  have yes (a b : V) (e : (graphOn W).Adj a b) : T.eval {a,b}=true := by
    exact (h.2 a b (bip _ _ _ e)).trans (decide_eq_true e)
  have no : T.eval {path i 0,path i 3}=false := by
    exact (h.2 _ _ (opposite_ends _ _ (bip W) (path_in W i hi))).trans (decide_eq_false ad)
  exact PEqualNP.Outside.L_meta_10057_aux.Cycle.Tree.linear_no_induced_path T lin h.1 _ _ _ _ (yes _ _ ab) (yes _ _ bc) (yes _ _ cd) no
theorem restrict_describes {W S : Finset V} {f : Finset V → Bool}
    (h : Describes W f) (zero : f ∅=false) : Describes (W \ S) (fun A => f (A \ S)) := by
  have one (a : V) : ({a} : Finset V) \ S = if a∈S then ∅ else {a} := by
    ext v
    by_cases ha : a∈S <;> by_cases eq : v=a <;> simp_all
  have two (a b : V) : ({a,b} : Finset V) \ S = (({a} : Finset V) \ S) ∪ (({b} : Finset V) \ S) := by
    ext v
    simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton,Finset.mem_union]
    tauto
  constructor
  · intro a
    change f (({a} : Finset V) \ S) = false
    rw [one]
    split <;> first | exact zero | exact h.1 _
  · intro a b diff
    change f (({a,b} : Finset V) \ S) = _
    rw [two,one,one]
    by_cases aS : a∈S <;> by_cases bS : b∈S
    · simp [aS,bS,zero,graphOn]
    · simp [aS,bS,h.1,graphOn]
    · simp [aS,bS,h.1,graphOn]
    · by_cases aw : a∈W <;> by_cases bw : b∈W <;> cases ev : edge a b <;> simpa [aS,bS,aw,bw,ev,graphOn] using h.2 a b diff
end PEqualNP.Outside.L_meta_10057_aux.Packing

namespace PEqualNP.Outside.L_meta_10057_aux.Packing
open PEqualNP.Outside.L_meta_10057_aux.Cycle
theorem path_neighbor (W : Finset V) (i : I) (hi : i∈intact W) (v : Fin 4) :
    ∃ z, (graphOn W).Adj (path i v) z := by
  obtain ⟨ab,bc,cd,_⟩ := path_in W i hi
  fin_cases v
  · exact ⟨_,ab⟩
  · exact ⟨_,bc⟩
  · exact ⟨_,cd⟩
  · exact ⟨_,cd.symm⟩
def withNeighbors (W S : Finset V) : Finset V := S.filter fun v => ∃ z, (graphOn W).Adj v z
lemma untouched_isolated (W S : Finset V) : intact (W \ withNeighbors W S) = intact (W \ S) := by
  ext i
  constructor
  · intro hi
    have all := (Finset.mem_filter.mp hi).2
    have orig : i∈intact W := Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun v => (Finset.mem_sdiff.mp (all v)).1⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,fun v => Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp (all v)).1,?_⟩⟩
    intro mem
    exact (Finset.mem_sdiff.mp (all v)).2 (Finset.mem_filter.mpr ⟨mem,path_neighbor W i orig v⟩)
  · intro hi
    have all := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun v => Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp (all v)).1,
      fun mem => (Finset.mem_sdiff.mp (all v)).2 (Finset.mem_filter.mp mem).1⟩⟩
theorem exclusive_cost (W S : Finset V) (h : Finset V → Bool) (g : Finset V → Bool → Bool)
    (desc : Describes W (folded S h g)) (zero : folded S h g ∅ = false)
    (mono : ∀ A B, A⊆B → h A=true → h B=true) (outer : ∀ A, g A false=true → g A true=true)
    (T : PEqualNP.Outside.L_meta_10057_aux.Cycle.Tree V) (lin : T.linear) (deps : T.leaves⊆S)
    (core : ∀ A⊆S, h A=T.eval A) : (intact W).card ≤ (intact (W \ S)).card + 2 := by
  by_cases cross : ∃ a∈S, ∃ b∉S, (graphOn W).Adj a b
  · have reduced := (exclusive_cut_twins_incident color (bip W) S h g mono outer desc.1 desc.2 cross).2
    have good : twins (withNeighbors W S) W := by
      intro u hu v hv same z hz
      obtain ⟨us,pu,eu⟩ := Finset.mem_filter.mp hu
      obtain ⟨vs,pv,ev⟩ := Finset.mem_filter.mp hv
      have equiv := reduced u us v vs ⟨pu,eu⟩ ⟨pv,ev⟩ same z
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro ok
        exact (equiv.mp ⟨eu.1,hz,ok⟩).2.2
      · intro ok
        exact (equiv.mpr ⟨ev.1,hz,ok⟩).2.2
    simpa only [untouched_isolated] using step (withNeighbors W S) W good
  · push_neg at cross
    have clean : untouched S W := by
      intro i hi v
      have p := exclusive_no_cross color (bip W) S h g zero desc.1 desc.2 T lin deps core cross (path_in W i hi)
      fin_cases v
      · exact p.1
      · exact p.2.1
      · exact p.2.2.1
      · exact p.2.2.2
    exact step_general S W (Or.inr clean)
end PEqualNP.Outside.L_meta_10057_aux.Packing

namespace PEqualNP.Outside.L_meta_10057_aux

open Finset

abbrev Parents (N : ℕ) := Fin N → List (Fin N)

def fanout {N : ℕ} (P : Parents N) (w : Fin N) : ℕ := ∑ j, (P j).count w

def slots {N : ℕ} (P : Parents N) : ℕ := ∑ j, (P j).length

def excess {N : ℕ} (P : Parents N) : ℕ := ∑ w, (fanout P w - 1)

private theorem sum_counts {N : ℕ} (L : List (Fin N)) :
    (∑ w, L.count w) = L.length := by
  induction L with
  | nil => simp
  | cons a l ih =>
    have ck (w : Fin N) : (a :: l).count w = l.count w + if w = a then 1 else 0 := by
      by_cases h : w = a
      · subst w
        simp
      · simp [h, Ne.symm h]
    simp [ck, Finset.sum_add_distrib, ih]

theorem sum_fanout {N : ℕ} (P : Parents N) : (∑ w, fanout P w) = slots P := by
  unfold fanout slots
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => sum_counts (P j))

private theorem count_sub {N : ℕ} (w : Fin N) {a b : List (Fin N)}
    (h : a.Sublist b) : a.count w ≤ b.count w := by
  induction h with
  | slnil => simp
  | cons a h ih =>
    rw [List.count_cons]
    omega
  | cons_cons a h ih =>
    rw [List.count_cons,List.count_cons]
    omega

theorem fanout_mono {N : ℕ} {P Q : Parents N}
    (sub : ∀ v, (Q v).Sublist (P v)) (w : Fin N) : fanout Q w ≤ fanout P w :=
  Finset.sum_le_sum fun j _ => count_sub w (sub j)

theorem excess_strict {N : ℕ} {P Q : Parents N}
    (sub : ∀ v, (Q v).Sublist (P v)) (pivot : Fin N)
    (repeated : 2 ≤ fanout P pivot) (gone : fanout Q pivot = 0) : excess Q < excess P := by
  unfold excess
  apply Finset.sum_lt_sum
  · intro w _
    exact Nat.sub_le_sub_right (fanout_mono sub w) 1
  · exact ⟨pivot, Finset.mem_univ _, by omega⟩

/-- Delete references to false or dead wires. Retaining unary positions as indexed nodes
ensures all lists of incoming references are sublists of their previous values. -/
def filtered {N : ℕ} (P : Parents N) (keep : Fin N → Bool) : Parents N :=
  fun v => if keep v then (P v).filter keep else []

theorem filtered_sub {N : ℕ} (P : Parents N) (keep : Fin N → Bool) (v : Fin N) :
    (filtered P keep v).Sublist (P v) := by
  unfold filtered
  split
  · exact List.filter_sublist
  · exact List.nil_sublist _

theorem no_fanout_after_filter {N : ℕ} (P : Parents N) (keep : Fin N → Bool)
    (w : Fin N) (gone : keep w = false) : fanout (filtered P keep) w = 0 := by
  unfold fanout
  apply Finset.sum_eq_zero
  intro j _
  apply Nat.eq_zero_of_not_pos
  intro pos
  have mem := List.count_pos_iff.mp pos
  unfold filtered at mem
  split at mem
  · have h := (List.mem_filter.mp mem).2
    simp [gone] at h
  · cases mem

theorem excess_decreases_on_pin {N : ℕ} (P : Parents N) (keep : Fin N → Bool)
    (pivot : Fin N) (repeated : 2 ≤ fanout P pivot) (gone : keep pivot = false) :
    excess (filtered P keep) < excess P :=
  excess_strict (filtered_sub P keep) pivot repeated (no_fanout_after_filter P keep pivot gone)

theorem excess_eq_slots {N : ℕ} (P : Parents N) (output : Fin N)
    (reads : ∀ w ≠ output, 1 ≤ fanout P w) (out : fanout P output = 0) :
    excess P + (N-1) = slots P := by
  let e (w : Fin N) := if w = output then 0 else 1
  have sumE : (∑ w, e w) = N-1 := by
    have split := Finset.sum_erase_add (Finset.univ : Finset (Fin N)) e (Finset.mem_univ output)
    have a : (∑ w ∈ (Finset.univ : Finset (Fin N)).erase output, e w) =
        ((Finset.univ : Finset (Fin N)).erase output).card := by
      calc
        _ = ∑ _w ∈ (Finset.univ : Finset (Fin N)).erase output, (1 : ℕ) :=
          Finset.sum_congr rfl (fun w m => by simp [e, (Finset.mem_erase.mp m).1])
        _ = _ := by simp
    rw [a, Finset.card_erase_of_mem (Finset.mem_univ output)] at split
    simpa [e] using split.symm
  calc
    excess P + (N-1) = (∑ w, ((fanout P w - 1) + e w)) := by
      simp only [excess, Finset.sum_add_distrib, sumE]
    _ = ∑ w, fanout P w := by
      apply Finset.sum_congr rfl
      intro w _
      by_cases h : w=output
      · subst w
        simp [out,e]
      · have hr := reads w h
        simp only [e, if_neg h]
        omega
    _ = slots P := sum_fanout P

theorem initial_excess_le_seven {g : ℕ} (P : Parents (78+g)) (output : Fin (78+g))
    (reads : ∀ w ≠ output, 1 ≤ fanout P w) (out : fanout P output = 0)
    (arity : slots P ≤ 2*g) (small : g ≤ 84) : excess P ≤ 7 := by
  have balance := excess_eq_slots P output reads out
  omega

inductive InCone {N : ℕ} (P : Parents N) : Fin N → Fin N → Prop
  | self (v) : InCone P v v
  | step {u v w} : u ∈ P v → InCone P v w → InCone P u w

theorem cone_order {N : ℕ} {P : Parents N}
    (back : ∀ v u, u ∈ P v → u < v) {u v : Fin N} (h : InCone P u v) : u ≤ v := by
  induction h with
  | self => exact le_rfl
  | step mem _ ih => exact (back _ _ mem).le.trans ih

theorem exists_cone_reader {N : ℕ} {P : Parents N} {u v : Fin N}
    (h : InCone P u v) (hne : u ≠ v) : ∃ r, u ∈ P r ∧ InCone P r v := by
  cases h with
  | self => exact (hne rfl).elim
  | step mem path => exact ⟨_,mem,path⟩

theorem unique_reader {N : ℕ} (P : Parents N) {u a b : Fin N} (single : fanout P u ≤ 1)
    (ha : u ∈ P a) (hb : u ∈ P b) : a = b := by
  by_contra hne
  have sub : ({a,b} : Finset (Fin N)) ⊆ Finset.univ := by simp
  have fees := Finset.sum_le_sum_of_subset_of_nonneg sub
    (fun (j : Fin N) _ _ => Nat.zero_le ((P j).count u))
  simp [hne, fanout] at fees single
  have a_pos := List.count_pos_iff.mpr ha
  have b_pos := List.count_pos_iff.mpr hb
  omega

/-- Every nonpivot ancestor of the earliest multiply-read wire has its unique reader
inside the same cone. With live trimming, its raw ancestors are exclusive to that cone. -/
theorem earliest_cone_closed {N : ℕ} (P : Parents N) (pivot u r : Fin N)
    (back : ∀ v i, i ∈ P v → i < v)
    (early : ∀ i < pivot, fanout P i ≤ 1)
    (path : InCone P u pivot) (notPivot : u ≠ pivot) (reads : u ∈ P r) :
    InCone P r pivot := by
  have lt := lt_of_le_of_ne (cone_order back path) notPivot
  obtain ⟨s,mem,rest⟩ := exists_cone_reader path notPivot
  exact (unique_reader P (early _ lt) mem reads) ▸ rest

theorem pinned_cone_zero {N : ℕ} (P : Parents N) (pivot : Fin N) (val : Fin N → Bool)
    (back : ∀ v u, u ∈ P v → u < v)
    (pin : ∀ v, InCone P v pivot → P v = [] → val v = false)
    (zero : ∀ v, P v ≠ [] → (∀ u ∈ P v, val u = false) → val v = false) :
    val pivot = false := by
  have h : ∀ v, InCone P v pivot → val v = false := by
    intro v
    induction v using WellFoundedLT.induction with
    | ind v ih =>
      intro path
      by_cases h : P v = []
      · exact pin v path h
      · exact zero v h (fun u m => ih u (back v u m) (.step m path))
  exact h pivot (.self pivot)

theorem pinned_support_excess_drops {N : ℕ} (P : Parents N) (pivot : Fin N)
    (val : Fin N → Bool) (repeated : 2 ≤ fanout P pivot)
    (back : ∀ v u, u ∈ P v → u < v)
    (pin : ∀ v, InCone P v pivot → P v = [] → val v = false)
    (zero : ∀ v, P v ≠ [] → (∀ u ∈ P v, val u = false) → val v = false) :
    excess (filtered P val) < excess P :=
  excess_decreases_on_pin P val pivot repeated (pinned_cone_zero P pivot val back pin zero)

end PEqualNP.Outside.L_meta_10057_aux

namespace PEqualNP.Outside.L_meta_10057_aux

open Finset

theorem no_repeats_iff_zero {N : ℕ} (P : Parents N) :
    excess P = 0 ↔ ∀ w, fanout P w ≤ 1 := by
  unfold excess
  constructor
  · intro no w
    have single : fanout P w - 1 ≤ (∑ v, (fanout P v - 1)) :=
      Finset.single_le_sum (f:=fun v => fanout P v - 1)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
    omega
  · intro h
    apply Finset.sum_eq_zero
    intro w _
    have small := h w
    omega

theorem earliest_repeat_exists {N : ℕ} (P : Parents N) (positive : 0 < excess P) :
    ∃ pivot, 2 ≤ fanout P pivot ∧ ∀ i < pivot, fanout P i ≤ 1 := by
  classical
  let R : Finset (Fin N) := Finset.univ.filter (fun i => 2 ≤ fanout P i)
  have nonempty : R.Nonempty := by
    by_contra no
    have empty : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp no
    have h (i : Fin N) : fanout P i ≤ 1 := by
      by_contra more
      have mem : i ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      rw [empty] at mem
      exact (Finset.notMem_empty i) mem
    exact (Nat.ne_of_gt positive) ((no_repeats_iff_zero P).mpr h)
  let p := R.min' nonempty
  refine ⟨p, (Finset.mem_filter.mp (Finset.min'_mem R nonempty)).2, ?_⟩
  intro i hi
  by_contra h
  have m : i ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
  exact (not_le_of_gt hi) (Finset.min'_le R i m)

theorem filtered_back {N : ℕ} (P : Parents N) (keep : Fin N → Bool)
    (back : ∀ j u, u ∈ P j → u < j) :
    ∀ j u, u ∈ filtered P keep j → u < j :=
  fun j u hu => back j u ((filtered_sub P keep j).subset hu)

theorem only_pivot_exits {N : ℕ} (P : Parents N) (pivot u r : Fin N)
    (back : ∀ v i, i ∈ P v → i < v)
    (early : ∀ i < pivot, fanout P i ≤ 1)
    (path : InCone P u pivot) (reads : u ∈ P r)
    (outside : ¬InCone P r pivot) : u = pivot := by
  by_contra notPivot
  exact outside (earliest_cone_closed P pivot u r back early path notPivot reads)

/-- Two operand cones of a gate cannot overlap if every wire before that gate
has at most one reader slot. -/
theorem one_reader_unique_last {N : ℕ} (P : Parents N) (root : Fin N)
    (back : ∀ v i, i ∈ P v → i < v) (before : ∀ i < root, fanout P i ≤ 1)
    {u a b : Fin N} (ma : a ∈ P root) (mb : b ∈ P root)
    (ua : InCone P u a) (ub : InCone P u b) : a=b := by
  induction ua with
  | self v =>
    by_contra ne
    obtain ⟨s,mem,rest⟩ := exists_cone_reader ub ne
    have eq := unique_reader P (before v (back root v ma)) mem ma
    have h := cone_order back rest
    rw [eq] at h
    exact (not_le_of_gt (back root b mb)) h
  | @step v r a vm ra ih =>
    have vr := back r v vm
    have ar := back root a ma
    have sr : r < root := (cone_order back ra).trans_lt ar
    by_cases ne : v = b
    · subst b
      have eq := unique_reader P (before v (vr.trans sr)) vm mb
      rw [eq] at sr
      exact (lt_irrefl _ sr).elim
    · obtain ⟨s,mem,rest⟩ := exists_cone_reader ub ne
      have eq := unique_reader P (before v (vr.trans sr)) mem vm
      exact ih ma (eq ▸ rest)

end PEqualNP.Outside.L_meta_10057_aux

namespace PEqualNP.Outside.L_meta_10057_aux

open PEqualNP.Outside.L_meta_10057_aux.Cycle

inductive Node (V : Type) (N : ℕ) where
  | zero
  | input (x : V)
  | copy (a : Fin N)
  | all (a b : Fin N)
  | any (a b : Fin N)

def Node.wires {V N} : Node V N → List (Fin N)
  | .zero | .input _ => []
  | .copy a => [a]
  | .all a b | .any a b => [a,b]

structure Dag (V : Type) (N : ℕ) where
  code : Fin N → Node V N
  back : ∀ j i, i ∈ (code j).wires → i < j
  inputs_unique : ∀ i j (x : V), code i = .input x → code j = .input x → i=j

namespace Dag
variable {V : Type} {N : ℕ}

def parents (D : Dag V N) : Parents N := fun i => (D.code i).wires

theorem edgeCopy (D : Dag V N) {w a : Fin N} (edge : D.code w = .copy a) :
    a ∈ D.parents w := by simp [parents, edge, Node.wires]

theorem edgeAll (D : Dag V N) {w a b : Fin N} (edge : D.code w = .all a b) :
    a ∈ D.parents w ∧ b ∈ D.parents w := by simp [parents, edge, Node.wires]

theorem edgeAny (D : Dag V N) {w a b : Fin N} (edge : D.code w = .any a b) :
    a ∈ D.parents w ∧ b ∈ D.parents w := by simp [parents, edge, Node.wires]

def eval (D : Dag V N) (raw : V → Bool) (patch : Fin N → Option Bool) (w : Fin N) : Bool :=
  match patch w with
  | some b => b
  | none =>
    match h : D.code w with
    | .zero => false
    | .input x => raw x
    | .copy a => eval D raw patch a
    | .all a b => eval D raw patch a && eval D raw patch b
    | .any a b => eval D raw patch a || eval D raw patch b
termination_by w.val
decreasing_by
  · exact D.back w _ (D.edgeCopy h)
  · exact D.back w _ (D.edgeAll h).1
  · exact D.back w _ (D.edgeAll h).2
  · exact D.back w _ (D.edgeAny h).1
  · exact D.back w _ (D.edgeAny h).2

def blank (_ : Fin N) : Option Bool := none

def stamp (p : Fin N) (b : Bool) (w : Fin N) : Option Bool :=
  if w=p then some b else none

def value [DecidableEq V] (D : Dag V N) (A : Finset V) (w : Fin N) : Bool :=
  D.eval (fun x => decide (x∈A)) blank w

theorem eval_in_cone (D : Dag V N) (u : Fin N) (raw1 raw2 : V → Bool)
    (patch1 patch2 : Fin N → Option Bool)
    (sameRaw : ∀ w x, InCone D.parents w u → D.code w = .input x → raw1 x = raw2 x)
    (samePatch : ∀ w, InCone D.parents w u → patch1 w = patch2 w) :
    D.eval raw1 patch1 u = D.eval raw2 patch2 u := by
  have go (w : Fin N) (inside : InCone D.parents w u) :
      D.eval raw1 patch1 w = D.eval raw2 patch2 w := by
    induction w using WellFoundedLT.induction with
    | ind w ih =>
      rw [eval,eval,samePatch w inside]
      cases patched : patch2 w
      · cases h : D.code w with
        | zero => rfl
        | input x => exact sameRaw w x inside h
        | copy a =>
          have m := D.edgeCopy h
          exact ih a (D.back w a m) (.step m inside)
        | all a b =>
          obtain ⟨ma,mb⟩ := D.edgeAll h
          change (D.eval raw1 patch1 a && D.eval raw1 patch1 b) =
            (D.eval raw2 patch2 a && D.eval raw2 patch2 b)
          rw [ih a (D.back w a ma) (.step ma inside), ih b (D.back w b mb) (.step mb inside)]
        | any a b =>
          obtain ⟨ma,mb⟩ := D.edgeAny h
          change (D.eval raw1 patch1 a || D.eval raw1 patch1 b) =
            (D.eval raw2 patch2 a || D.eval raw2 patch2 b)
          rw [ih a (D.back w a ma) (.step ma inside), ih b (D.back w b mb) (.step mb inside)]
      · rfl
  exact go u (.self u)

def PatchLE (a b : Option Bool) : Prop :=
  match a,b with
  | none, none => True
  | some x, some y => x = true → y = true
  | _, _ => False

theorem eval_mono (D : Dag V N) (raw1 raw2 : V→Bool) (patch1 patch2 : Fin N→Option Bool)
    (rle : ∀ x, raw1 x=true → raw2 x=true) (ple : ∀ j, PatchLE (patch1 j) (patch2 j))
    (w : Fin N) : D.eval raw1 patch1 w = true → D.eval raw2 patch2 w = true := by
  induction w using WellFoundedLT.induction with
  | ind w ih =>
    rw [eval,eval]
    have t := ple w
    cases h1 : patch1 w <;> cases h2 : patch2 w
    · cases h : D.code w with
      | zero => simp
      | input x => exact rle x
      | copy a => exact ih a (D.back w a (D.edgeCopy h))
      | all a b =>
        obtain ⟨ma,mb⟩ := D.edgeAll h
        intro x
        exact Tree.and_truth.mpr
          ⟨ih a (D.back w a ma) (Tree.and_truth.mp x).1,
            ih b (D.back w b mb) (Tree.and_truth.mp x).2⟩
      | any a b =>
        obtain ⟨ma,mb⟩ := D.edgeAny h
        intro x
        exact Tree.or_truth.mpr
          ((Tree.or_truth.mp x).imp (ih a (D.back w a ma)) (ih b (D.back w b mb)))
    · simp [PatchLE,h1,h2] at t
    · simp [PatchLE,h1,h2] at t
    · simpa [PatchLE,h1,h2] using t

theorem value_mono [DecidableEq V] (D : Dag V N) (w : Fin N) :
    ∀ A B : Finset V, A ⊆ B → D.value A w = true → D.value B w = true := by
  intro A B sub
  apply D.eval_mono
  · intro x hx
    exact decide_eq_true (sub (of_decide_eq_true hx))
  · intro j
    trivial

noncomputable def support [DecidableEq V] (D : Dag V N) (p : Fin N) : Finset V := by
  classical
  exact Finset.univ.biUnion (fun j =>
    if InCone D.parents j p then match D.code j with
      | .input x => {x}
      | _ => ∅
    else ∅)

theorem support_iff [DecidableEq V] (D : Dag V N) (p : Fin N) (x : V) :
    x ∈ D.support p ↔ ∃ j, InCone D.parents j p ∧ D.code j = .input x := by
  classical
  unfold support
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j,h⟩
    by_cases m : InCone D.parents j p
    · simp only [if_pos m] at h
      cases code : D.code j <;> simp [code] at h
      rename_i y
      obtain rfl : x=y := h
      exact ⟨j,m,code⟩
    · simp [m] at h
  · rintro ⟨j,m,h⟩
    exact ⟨j, by simp [m,h]⟩

theorem value_support [DecidableEq V] (D : Dag V N) (p : Fin N) (A : Finset V) :
    D.value A p = D.value (A ∩ D.support p) p := by
  unfold value
  apply D.eval_in_cone p
  · intro j x mem r
    simp [(D.support_iff p x).mpr ⟨j,mem,r⟩]
  · intro _ _
    rfl

end Dag
end PEqualNP.Outside.L_meta_10057_aux

namespace PEqualNP.Outside.L_meta_10057_aux
open Finset
variable {V : Type} [DecidableEq V] [Fintype V] {N : ℕ}
namespace Node
def keepCode (S : Finset V) (keep : Fin N → Bool) : Node V N → Node V N
  | .zero => .zero
  | .input v => if v∈S then .zero else .input v
  | .copy a => if keep a then .copy a else .zero
  | .all a b => if keep a && keep b then .all a b else .zero
  | .any a b => if keep a then (if keep b then .any a b else .copy a) else
       (if keep b then .copy b else .zero)
theorem wires_sub (S : Finset V) (keep : Fin N → Bool) (c : Node V N) :
    ((keepCode S keep c).wires).Sublist c.wires := by
  cases c <;> simp only [keepCode] <;> (try split_ifs) <;> simp [wires]
theorem retained_wire (S : Finset V) (keep : Fin N → Bool) (c : Node V N) (w : Fin N) :
    w ∈ (keepCode S keep c).wires → keep w = true := by
  cases c <;> simp only [keepCode] <;> (try split_ifs) <;> simp_all [wires,Bool.and_eq_true] <;>
    rintro (rfl|rfl) <;> tauto
theorem retained_input (S : Finset V) (keep : Fin N → Bool) (c : Node V N) (v : V) :
    keepCode S keep c = .input v → c = .input v := by
  cases c <;> simp only [keepCode] <;> (try split_ifs) <;> simp
def valOf (raw : V → Bool) (w : Fin N → Bool) : Node V N → Bool
  | .zero => false
  | .input v => raw v
  | .copy a => w a
  | .all a b => w a && w b
  | .any a b => w a || w b
theorem val_congr (c : Node V N) (raw : V → Bool) (w z : Fin N → Bool)
    (h : ∀ a∈c.wires, w a=z a) : valOf raw w c=valOf raw z c := by
  cases c <;> simp_all [wires,valOf]
theorem keep_val (S A : Finset V) (keep : Fin N→Bool) (w : Fin N→Bool)
    (dead : ∀a, keep a=false → w a=false) (c : Node V N) :
    valOf (fun v=>decide (v∈A)) w (keepCode S keep c) =
    valOf (fun v=>decide (v∈A \ S)) w c := by
  cases c with
  | zero => rfl
  | input v => by_cases pin : v∈S <;> simp [keepCode,valOf,pin]
  | copy a => cases h : keep a <;> simp_all [keepCode,valOf]
  | all a b => cases ha : keep a <;> cases hb : keep b <;> simp_all [keepCode,valOf]
  | any a b => cases ha : keep a <;> cases hb : keep b <;> simp_all [keepCode,valOf]
end Node
namespace Dag
theorem value_eq (D : Dag V N) (A : Finset V) (w : Fin N) :
    D.value A w = Node.valOf (fun x => decide (x∈A)) (D.value A) (D.code w) := by
  unfold value
  rw [eval]
  cases h : D.code w <;> simp [blank,h,Node.valOf]
theorem value_empty (D : Dag V N) (w : Fin N) : D.value ∅ w=false := by
  induction w using WellFoundedLT.induction with
  | ind w ih =>
    rw [value_eq]
    cases h : D.code w with
    | zero => rfl
    | input x => simp [Node.valOf]
    | copy a => exact ih a (D.back w a (D.edgeCopy h))
    | all a b => simp [Node.valOf, ih a (D.back w a (D.edgeAll h).1)]
    | any a b => simp [Node.valOf, ih a (D.back w a (D.edgeAny h).1),ih b (D.back w b (D.edgeAny h).2)]
def keepAlive (D : Dag V N) (S : Finset V) (w : Fin N) := D.value (Finset.univ \ S) w
def restrict (D : Dag V N) (S : Finset V) : Dag V N where
  code := fun w => Node.keepCode S (D.keepAlive S) (D.code w)
  back := fun w a hw => D.back w a ((Node.wires_sub S _ _).subset hw)
  inputs_unique := fun i j x hi hj => D.inputs_unique i j x
    (Node.retained_input S _ _ x hi) (Node.retained_input S _ _ x hj)
theorem restricted_value (D : Dag V N) (A S : Finset V) (out : Fin N) :
    (D.restrict S).value A out=D.value (A \ S) out := by
  have dead (w : Fin N) (x : D.keepAlive S w=false) : D.value (A \ S) w=false := by
    by_contra! yes
    have sub : A \ S ⊆ Finset.univ \ S := fun v h => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,(Finset.mem_sdiff.mp h).2⟩
    have h := D.value_mono w _ _ sub (by simpa using yes)
    change D.value (Finset.univ \ S) w=false at x
    simp [x] at h
  induction out using WellFoundedLT.induction with
  | ind w ih =>
    rw [value_eq, value_eq D]
    change Node.valOf _ _ (Node.keepCode S _ (D.code w)) = _
    rw [Node.val_congr _ _ _ (D.value (A \ S)) (fun a ha =>
      ih a (D.back w a ((Node.wires_sub S _ _).subset ha)))]
    exact Node.keep_val S A _ _ dead _
theorem support_pin_decrease (D : Dag V N) (p : Fin N) (multi : 2≤fanout D.parents p) :
    excess (D.restrict (D.support p)).parents < excess D.parents := by
  let S := D.support p
  have off : D.keepAlive S p=false := by
    unfold keepAlive
    rw [D.value_support p]
    have z : (Finset.univ \ S) ∩ D.support p=∅ := by ext x; simp [S]
    rw [z,D.value_empty]
  apply excess_strict (fun w => Node.wires_sub S _ (D.code w)) p multi
  unfold fanout
  apply Finset.sum_eq_zero
  intro w _
  apply List.count_eq_zero.mpr
  intro hp
  have on := Node.retained_wire S (D.keepAlive S) (D.code w) p hp
  simp [off] at on
end Dag
end PEqualNP.Outside.L_meta_10057_aux

namespace PEqualNP.Outside.L_meta_10057_aux.Dag

open PEqualNP.Outside.L_meta_10057_aux.Cycle

variable {V : Type} {N : ℕ} [DecidableEq V]

private theorem cone_append {P : Parents N} {i a w : Fin N}
    (path : InCone P i a) (edge : a ∈ P w) : InCone P i w := by
  induction path with
  | self => exact .step edge (.self w)
  | step m _ ih => exact .step m (ih edge)

theorem support_sub (D : Dag V N) {a w : Fin N} (edge : a ∈ D.parents w) :
    D.support a ⊆ D.support w := by
  intro x hx
  obtain ⟨j,path,r⟩ := (D.support_iff a x).mp hx
  exact (D.support_iff w x).mpr ⟨j,cone_append path edge,r⟩

theorem distinct_children (D : Dag V N) {w a b : Fin N}
    (children : D.parents w = [a,b]) (before : ∀ i < w, fanout D.parents i ≤ 1) : a≠b := by
  intro e
  subst b
  have m : a ∈ D.parents w := by simp [children]
  have counts : 2 ≤ fanout D.parents a := by
    have low := Finset.single_le_sum (f := fun j => (D.parents j).count a)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
    simpa [children,fanout] using low
  have high := before a (D.back w a m)
  omega

theorem disjoint_supports (D : Dag V N) {w a b : Fin N}
    (ma : a ∈ D.parents w) (mb : b ∈ D.parents w) (ne : a ≠ b)
    (early : ∀ i < w, fanout D.parents i ≤ 1) :
    Disjoint (D.support a) (D.support b) := by
  apply Finset.disjoint_left.mpr
  intro x ha hb
  obtain ⟨i,ia,iv⟩ := (D.support_iff a x).mp ha
  obtain ⟨j,jb,jv⟩ := (D.support_iff b x).mp hb
  have e := D.inputs_unique i j x iv jv
  exact ne (one_reader_unique_last D.parents w D.back early ma mb ia (e.symm ▸ jb))

def ForTree (D : Dag V N) (w : Fin N) (T : PEqualNP.Outside.L_meta_10057_aux.Cycle.Tree V) : Prop :=
  T.linear ∧ T.leaves ⊆ D.support w ∧ ∀ A, D.value A w = T.eval A

def AsTree (D : Dag V N) (w : Fin N) : Prop :=
  (∀ A, D.value A w = false) ∨ ∃ T, ForTree D w T

private theorem binaryTree (D : Dag V N) {w a b : Fin N} (op : Bool)
    (h : D.code w = if op then .any a b else .all a b)
    (early : ∀ i < w, fanout D.parents i ≤ 1)
    (left : AsTree D a) (right : AsTree D b) : AsTree D w := by
  have parentsEq : D.parents w = [a,b] := by
    cases op <;> simp [parents,h,Node.wires]
  have ma : a ∈ D.parents w := by simp [parentsEq]
  have mb : b ∈ D.parents w := by simp [parentsEq]
  have val (A : Finset V) : D.value A w =
      if op then D.value A a || D.value A b else D.value A a && D.value A b := by
    unfold value
    cases op <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h ⊢
    all_goals rw [eval, show blank w = none from rfl, h]
  rcases left with za | ⟨L,ll,ld,lv⟩ <;> rcases right with zb | ⟨R,rl,rd,rv⟩
  · exact Or.inl fun A => by rw [val,za,zb]; cases op <;> rfl
  · cases op
    · exact Or.inl fun A => by simp [val,za]
    · exact Or.inr ⟨R,rl,rd.trans (D.support_sub mb),fun A => by simp [val,za,rv]⟩
  · cases op
    · exact Or.inl fun A => by simp [val,zb]
    · exact Or.inr ⟨L,ll,ld.trans (D.support_sub ma),fun A => by simp [val,zb,lv]⟩
  · have dis : Disjoint L.leaves R.leaves :=
      (D.disjoint_supports ma mb (D.distinct_children parentsEq early) early).mono ld rd
    have incl : L.leaves ∪ R.leaves ⊆ D.support w :=
      Finset.union_subset (ld.trans (D.support_sub ma)) (rd.trans (D.support_sub mb))
    cases op
    · exact Or.inr ⟨PEqualNP.Outside.L_meta_10057_aux.Cycle.Tree.all L R,⟨ll,rl,dis⟩,incl,fun A => by simp [val,lv,rv,PEqualNP.Outside.L_meta_10057_aux.Cycle.Tree.eval]⟩
    · exact Or.inr ⟨PEqualNP.Outside.L_meta_10057_aux.Cycle.Tree.any L R,⟨ll,rl,dis⟩,incl,fun A => by simp [val,lv,rv,PEqualNP.Outside.L_meta_10057_aux.Cycle.Tree.eval]⟩

/-- An evaluation cone before the first repeat is either false everywhere or a linear tree. -/
theorem cone_tree (D : Dag V N) (w : Fin N) (early : ∀ i < w, fanout D.parents i ≤ 1) :
    AsTree D w := by
  induction w using WellFoundedLT.induction with
  | ind w ih =>
    have child (u : Fin N) (m : u ∈ D.parents w) : AsTree D u :=
      ih u (D.back w u m) (fun i hi => early i (hi.trans (D.back w u m)))
    cases gate : D.code w with
    | zero => exact Or.inl fun A => by rw [value,eval,show blank w = none from rfl,gate]
    | input x =>
      refine Or.inr ⟨PEqualNP.Outside.L_meta_10057_aux.Cycle.Tree.input x,trivial,?_,fun A => ?_⟩
      · intro y hy
        have e : y=x := by simpa [PEqualNP.Outside.L_meta_10057_aux.Cycle.Tree.leaves] using hy
        subst y
        exact (D.support_iff w x).mpr ⟨w,.self w,gate⟩
      · rw [value,eval,show blank w = none from rfl,gate]
        rfl
    | copy a =>
      have m := D.edgeCopy gate
      have hval (A : Finset V) : D.value A w = D.value A a := by
        unfold value
        rw [eval,show blank w = none from rfl,gate]
      rcases child a m with zero | ⟨T,tl,ts,tv⟩
      · exact Or.inl fun A => (hval A).trans (zero A)
      · exact Or.inr ⟨T,tl,ts.trans (D.support_sub m),fun A => (hval A).trans (tv A)⟩
    | all a b =>
      have m := D.edgeAll gate
      exact binaryTree D false gate early (child a m.1) (child b m.2)
    | any a b =>
      have m := D.edgeAny gate
      exact binaryTree D true gate early (child a m.1) (child b m.2)

def outer (D : Dag V N) (p out : Fin N) (A : Finset V) (b : Bool) : Bool :=
  D.eval (fun x => decide (x∈A)) (stamp p b) out

theorem outer_mono (D : Dag V N) (p out : Fin N) (A : Finset V) :
    D.outer p out A false=true → D.outer p out A true=true := by
  apply D.eval_mono
  · intro _ h
    exact h
  · intro i
    by_cases h : i=p <;> simp [stamp,PatchLE,h]

theorem factorize (D : Dag V N) (p out : Fin N) (le : p ≤ out)
    (early : ∀ i < p, fanout D.parents i ≤ 1) (A : Finset V) :
    D.value A out = folded (D.support p) (fun X => D.value X p) (D.outer p out) A := by
  unfold folded outer
  let S := D.support p
  let bit := D.value (A ∩ S) p
  let visible (w : Fin N) := ¬InCone D.parents w p ∨ w=p
  have childVisible {w a : Fin N} (outside : ¬InCone D.parents w p) (m : a ∈ D.parents w) :
      visible a := by
    by_cases h : InCone D.parents a p
    · exact Or.inr (only_pivot_exits D.parents p a w D.back early h m outside)
    · exact Or.inl h
  have eq (w : Fin N) (vis : visible w) :
      D.value A w = D.eval (fun x => decide (x∈A\S)) (stamp p bit) w := by
    induction w using WellFoundedLT.induction with
    | ind w ih =>
      rcases vis with outside | eqWp
      · have ne : w≠p := fun h => outside (h.symm ▸ InCone.self p)
        have noStamp : stamp p bit w = none := by simp [stamp,ne]
        have go (a : Fin N) (m : a ∈ D.parents w) :=
          ih a (D.back w a m) (childVisible outside m)
        unfold value
        rw [eval,eval,noStamp]
        simp only [blank]
        cases rule : D.code w with
        | zero => rfl
        | input x =>
          have xout : x ∉ S := by
            intro xin
            obtain ⟨j,path,same⟩ := (D.support_iff p x).mp xin
            exact outside (D.inputs_unique j w x same rule ▸ path)
          simp [xout]
        | copy a => exact go a (D.edgeCopy rule)
        | all a b =>
          obtain ⟨ma,mb⟩ := D.edgeAll rule
          change (D.value A a && D.value A b) =
            (D.eval (fun x => decide (x∈A\S)) (stamp p bit) a &&
             D.eval (fun x => decide (x∈A\S)) (stamp p bit) b)
          rw [←go a ma,←go b mb]
        | any a b =>
          obtain ⟨ma,mb⟩ := D.edgeAny rule
          change (D.value A a || D.value A b) =
            (D.eval (fun x => decide (x∈A\S)) (stamp p bit) a ||
             D.eval (fun x => decide (x∈A\S)) (stamp p bit) b)
          rw [←go a ma,←go b mb]
      · subst w
        rw [eval, show stamp p bit p = some bit by simp [stamp]]
        exact D.value_support p A
  apply eq
  by_cases h : out=p
  · exact Or.inr h
  · exact Or.inl fun path => h (le_antisymm (cone_order D.back path) le)

theorem no_repeat_output (D : Dag V N) (out : Fin N) (zero : excess D.parents=0) :
    AsTree D out :=
  D.cone_tree out (fun i _ => (no_repeats_iff_zero _).mp zero i)

end PEqualNP.Outside.L_meta_10057_aux.Dag

namespace PEqualNP.Outside.L_meta_10057_aux.Packing
open PEqualNP.Outside.L_meta_10057_aux.Cycle PEqualNP.Outside.L_meta_10057_aux
theorem zero_empty (W : Finset V) (f : Finset V → Bool) (h : Describes W f)
    (allzero : ∀ A, f A=false) : (intact W).card=0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have e := (path_in W i hi).1
  have yes := (h.2 _ _ (bip _ _ _ e)).trans (decide_eq_true e)
  rw [allzero] at yes
  contradiction
theorem constant_cut (W S : Finset V) (h : Finset V → Bool) (g : Finset V → Bool → Bool)
    (desc : Describes W (folded S h g)) (allzero : ∀A, h A=false) : untouched S W := by
  intro i hi a mem
  obtain ⟨z,ez⟩ := path_neighbor W i hi a
  have yes := (desc.2 _ _ (bip _ _ _ ez)).trans (decide_eq_true ez)
  have no := desc.1 z
  unfold folded at yes no
  rw [allzero,Finset.insert_sdiff_of_mem _ mem] at yes
  rw [allzero] at no
  simp [yes] at no
theorem dag_count {N : ℕ} (D : Dag V N) (out : Fin N) (last : ∀ p, p≤out) (W : Finset V)
    (desc : Describes W (fun A => D.value A out)) :
    (intact W).card ≤ 2 * excess D.parents := by
  generalize ey : excess D.parents = k
  induction k using Nat.strong_induction_on generalizing D W with
  | ind k ih =>
    by_cases zero : k=0
    · have tree := D.no_repeat_output out (ey.trans zero)
      have empty : (intact W).card=0 := by
        rcases tree with const|⟨T,_,_,he⟩
        · exact zero_empty W _ desc const
        · have hg : (fun A => D.value A out) = T.eval := funext he
          rw [hg] at desc
          exact linear_empty W T (by assumption) desc
      omega
    · have nonzero : 0 < excess D.parents := by omega
      obtain ⟨p,multi,early⟩ := earliest_repeat_exists D.parents nonzero
      let S := D.support p
      let f := fun A => D.value A p
      let g := D.outer p out
      have same : (fun A => D.value A out) = folded S f g := funext (D.factorize p out (last p) early)
      have hd : Describes W (folded S f g) := same ▸ desc
      have he : folded S f g ∅=false := (congrFun same ∅).symm.trans (D.value_empty out)
      have charge : (intact W).card ≤ (intact (W \ S)).card+2 := by
        rcases D.cone_tree p early with const|⟨T,lin,deps,core⟩
        · exact step_general _ _ (Or.inr (constant_cut W S f g hd const))
        · exact exclusive_cost W S f g hd he (D.value_mono p) (D.outer_mono p out)
            T lin deps (fun A _ => core A)
      have dn := D.support_pin_decrease p multi
      have next : Describes (W \ S) (fun A => (D.restrict S).value A out) := by
        have id : (fun A => (D.restrict S).value A out) = (fun A => D.value (A \ S) out) :=
          funext (fun A => D.restricted_value A S out)
        rw [id]
        exact restrict_describes desc (D.value_empty out)
      have dec : excess (D.restrict S).parents < k := by simpa [ey,S] using dn
      have bound := ih (excess (D.restrict S).parents) dec (D.restrict S) (W \ S) next rfl
      omega
theorem excess_nine {N : ℕ} (D : Dag V N) (out : Fin N) (last : ∀ p, p≤out)
    (desc : Describes Finset.univ (fun A => D.value A out)) : 9≤excess D.parents := by
  have b := dag_count D out last Finset.univ desc
  have c : (intact Finset.univ).card=17 := by simp [intact]
  omega
end PEqualNP.Outside.L_meta_10057_aux.Packing

-- Gate bypass and wire semantics adapted from checked L-meta-2668.
-- Bypass helpers adapted from willakone, L-meta-1499, PR 3112.
namespace PEqualNP.Outside.L_meta_10057_aux.Bypass

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
    (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
    (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < n
    · rw [val_input hx hun, val_input hx hun]
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < m := by omega
      rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + k
      · rw [if_pos hi, if_pos hi]; exact ih i hi (by omega)
      · rw [if_neg hi, if_neg hi]

def aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

def aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

def bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (fun k =>
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
    aliasWire (n + r) i C.output⟩

lemma bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

lemma bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

lemma gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
    gateAt (bypass n C r i) k =
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
  have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
  rw [gateAt_eq hk']
  simp [bypass]

lemma bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
    (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
  apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
  intro k hk
  rw [gateAt_bypass (by omega), if_pos hk]

lemma aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]

lemma aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
  unfold aliasWire; rw [if_neg (by omega), if_neg (by omega)]

lemma aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
  unfold aliasWire; rw [if_neg (by omega), if_pos hu]

lemma bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : (∃ k, r < k ∧ k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
      R (val C x (n + r)) (val C x i)) :
    ∀ u, u ≠ n + r → R (val C x u) (val (bypass n C r i) x (aliasWire (n + r) i u)) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hne
    by_cases hlt : u < n + r
    · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]; exact hrefl _
    · rw [aliasWire_gt_self (by omega)]
      by_cases hge : n + C.gates.length ≤ u
      · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]; exact hrefl _
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
        have hk1 : k + 1 < C.gates.length := by omega
        have hkr : ¬ k < r := by omega
        have e : n + (k + 1) - 1 = n + k := by omega
        rw [e, val_gate hx hk1, val_gate hx (by rw [bypass_length]; omega),
          gateAt_bypass (by omega), if_neg hkr]
        simp only [aliasGate, List.map_map]
        refine hmono _ (hAO _ hk1) _ _ _ ?_
        intro i' hi'
        simp only [Function.comp_apply]
        by_cases h1 : i' = n + r
        · subst h1
          rw [aliasWire_self, if_pos (by omega)]
          have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
            rcases hi with hi | hi
            · rw [if_pos (by omega), bypass_val_lt hx hr i hi]
            · rw [if_neg (by omega), val_ge hx hi]
          rw [hgi]
          exact hR ⟨k + 1, by omega, hk1, hi'⟩
        · by_cases h2 : i' < n + r
          · rw [aliasWire_lt_self h2, if_pos (by omega), if_pos (by omega),
              bypass_val_lt hx hr i' h2]
            exact hrefl _
          · by_cases h3 : i' < n + (k + 1)
            · have key := ih i' h3 h1
              rw [aliasWire_gt_self (by omega)] at key
              rw [aliasWire_gt_self (by omega), if_pos h3, if_pos (by omega)]
              exact key
            · rw [aliasWire_gt_self (by omega), if_neg h3, if_neg (by omega)]
              exact hrefl _

lemma bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : R (val C x (n + r)) (val C x i)) :
    R (C.eval x) ((bypass n C r i).eval x) := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  by_cases h : C.output = n + r
  · have hgi : val (bypass n C r i) x i = val C x i := by
      rcases hi with hi | hi
      · exact bypass_val_lt hx hr i hi
      · rw [val_ge hx hi, val_ge hx (by rw [bypass_length]; omega)]
    rw [h, aliasWire_self, hgi]; exact hR
  · exact bypass_rel hrefl hmono hx hAO hr hi (fun _ => hR) _ h

lemma bypass_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : val C x (n + r) = val C x i) :
    (bypass n C r i).eval x = C.eval x :=
  (bypass_eval_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi hR).symm

lemma bypass_eval_unread {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hout : C.output ≠ n + r)
    (hno : ∀ k, r < k → k < C.gates.length → n + r ∉ (gateAt C k).inputs) :
    (bypass n C r i).eval x = C.eval x := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi
    (fun ⟨k, hrk, hk, hm⟩ => absurd hm (hno k hrk hk)) _ hout).symm

lemma bypass_AO {n : ℕ} {C : Circuit} {r i : ℕ} (hr : r < C.gates.length)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ k < (bypass n C r i).gates.length,
      (gateAt (bypass n C r i) k).op = GateOp.and ∨
        (gateAt (bypass n C r i) k).op = GateOp.or := by
  intro k hk
  rw [bypass_length] at hk
  rw [gateAt_bypass hk]
  split_ifs with h
  · exact hAO k (by omega)
  · exact hAO (k + 1) (by omega)

lemma bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
    ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
      g.inputs.length = g'.inputs.length := by
  intro g hg
  simp only [bypass, List.mem_map, List.mem_range] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  split_ifs with h
  · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
  · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

lemma aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
    aliasWire w i u < m := by
  unfold aliasWire; split_ifs <;> omega

lemma bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
    (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
    ∀ k < (bypass n C r i).gates.length,
      ∀ u ∈ (gateAt (bypass n C r i) k).inputs, u < n + k := by
  intro k hk u hu
  rw [bypass_length] at hk
  rw [gateAt_bypass hk] at hu
  split_ifs at hu with h
  · exact hRB k (by omega) u hu
  · simp only [aliasGate, List.mem_map] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    have := hRB (k + 1) (by omega) u' hu'
    exact aliasWire_lt hi (by omega) (by omega)


lemma erase_eq_bypass (n : ℕ) (C : Circuit) (r i : ℕ) (hr : r < C.gates.length) :
    PEqualNP.CircuitMoves.eraseGate n C r i = bypass n C r i := by
  unfold PEqualNP.CircuitMoves.eraseGate
  rw [if_pos hr]
  change Circuit.mk _ (aliasWire (n + r) i C.output) = Circuit.mk _ (aliasWire (n + r) i C.output)
  congr 1
  apply List.ext_getElem
  · simp [bypass]; omega
  · intro k hk hk'
    have hlen : (C.gates.take r).length = r := by simp; omega
    have hklen : k < C.gates.length - 1 := by simpa [bypass] using hk'
    simp only [bypass, List.getElem_map, List.getElem_range]
    by_cases hkr : k < r
    · rw [if_pos hkr, List.getElem_append_left (by omega), List.getElem_take,
        gateAt_eq (by omega)]
    · rw [if_neg hkr, List.getElem_append_right (by omega), List.getElem_map,
        List.getElem_drop]
      simp only [hlen]
      have he : r + 1 + (k - r) = k + 1 := by omega
      simp only [he]
      rw [gateAt_eq (by omega : k + 1 < C.gates.length)]
      rfl

lemma mono_ops {C : Circuit} (hM : Monotone2 C) :
    ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  intro k hk
  exact (hM _ (gateAt_mem hk)).1

lemma wire_monotone (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ u, val C (List.ofFn x) u = true → val C (List.ofFn y) u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hun : u < n
    · rw [val_input (n := n) (by simp) hun, val_input (n := n) (by simp) hun]
      simpa [hun] using hxy ⟨u, hun⟩
    · by_cases hge : n + C.gates.length ≤ u
      · rw [val_ge (n := n) (by simp) hge]
        intro h; cases h
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk, val_gate (n := n) (by simp) hk]
        apply opMono_imp _ (mono_ops hM k hk)
        intro i hi
        by_cases hil : i < n + k
        · rw [if_pos hil, if_pos hil]
          exact ih i hil
        · rw [if_neg hil, if_neg hil]
          exact id

lemma circuit_monotone (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) : C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true :=
  wire_monotone n C hM x y hxy C.output

lemma opMono_reverse : OpMono (fun a b => b = true → a = true) := by
  intro op hop l f g h
  exact opMono_imp op hop l g f h

lemma bypass_mono {n : ℕ} {C : Circuit} {r i : ℕ} (hM : Monotone2 C) :
    Monotone2 (bypass n C r i) := by
  intro g hg
  obtain ⟨g', hg', hop, hlen⟩ := bypass_mem g hg
  rw [hop, hlen]
  exact hM g' hg'

lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ p l, G.Adj p l ∧ x p = true ∧ x l = true := by
  simp [graphFun]

lemma pair_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p l : Fin n)
    (hp : G.Adj p l) : graphFun G ∅ (PEqualNP.EdgeOwnership.pairInput p l) = true := by
  rw [graph_true]
  exact ⟨p, l, hp, by simp [PEqualNP.EdgeOwnership.pairInput], by simp [PEqualNP.EdgeOwnership.pairInput]⟩


end PEqualNP.Outside.L_meta_10057_aux.Bypass

namespace PEqualNP.Outside.L_meta_10057_aux.Cycle.Initial
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_10057_aux.Bypass

variable {n : ℕ}

def left (u : Fin n) : Fin (n+n) := u.castAdd n
def right (u : Fin n) : Fin (n+n) := u.natAdd n

lemma left_right (u v : Fin n) : left u ≠ right v := by
  intro e
  have h := congrArg Fin.val e
  change u.val = n+v.val at h
  have := u.isLt
  omega

def row (u v : Fin n) (w : Fin (n+n)) : Bool := decide (w=left u ∨ w=right v)

lemma row_eq (u v : Fin n) : List.ofFn (row u v) = oneEach u v := by
  unfold oneEach
  rw [List.ofFn_add]
  have hLeft : (fun i : Fin n => row u v (i.castLE (Nat.le_add_right n n))) =
      (fun i => decide (i=u)) := by
    funext i
    change row u v (left i) = decide (i=u)
    have p : left i = left u ↔ i=u := ⟨fun h => Fin.ext (congrArg (fun j : Fin (n+n) => j.val) h),congrArg left⟩
    simp [row,left_right,p]
  have hRight : (fun i : Fin n => row u v (i.natAdd n)) =
      (fun i => decide (i=v)) := by
    funext i
    change row u v (right i) = decide (i=v)
    have p : right i = right v ↔ i=v := by
      constructor
      · intro h
        have h' := congrArg Fin.val h
        change n+i.val=n+v.val at h'
        exact Fin.ext (by omega)
      · exact congrArg right
    have neq : right i ≠ left u := Ne.symm (left_right u i)
    simp [row,neq,p]
  rw [hLeft,hRight]

lemma val_raw {k : ℕ} (C : Circuit) (x : Fin k → Bool) (v : Fin k) :
    val C (List.ofFn x) v.val = x v := by
  rw [val_input (n:=k) (by simp) v.isLt,List.getD_eq_getElem _ _ (by simpa using v.isLt)]
  simp

lemma eval_row (A : Fin n → Fin n → Bool) (C : Circuit) (exactA : Represents A C)
    (u v : Fin n) : C.eval (List.ofFn (row u v)) = A u v := by
  rw [row_eq]
  exact exactA u v

lemma diag_contains (w : Fin (n+n)) : ∃ i : Fin n, row i i w = true := by
  refine Fin.addCases ?_ ?_ w
  · intro u
    exact ⟨u,by simp [row,left]⟩
  · intro u
    exact ⟨u,by simp [row,right]⟩

theorem singleton_false (A : Fin n → Fin n → Bool) (C : Circuit) (mono : Monotone2 C)
    (exactA : Represents A C) (diag : ∀ i,A i i=false) (w : Fin (n+n)) :
    C.eval (List.ofFn (fun i : Fin (n+n) => decide (i=w))) = false := by
  obtain ⟨i,active⟩ := diag_contains w
  apply Bool.eq_false_iff.mpr
  intro h
  have atDiag := circuit_monotone (n+n) C mono (fun v => decide (v=w)) (row i i)
    (fun a yes => by have same : a=w := of_decide_eq_true yes; subst a; exact active) h
  rw [eval_row A C exactA,diag] at atDiag
  contradiction

theorem output_nonraw (A : Fin n → Fin n → Bool) (C : Circuit) (mono : Monotone2 C)
    (exactA : Represents A C) (diag : ∀ i,A i i=false) : n+n ≤ C.output := by
  by_contra bad
  let w : Fin (n+n) := ⟨C.output,by omega⟩
  have neg := singleton_false A C mono exactA diag w
  change val C (List.ofFn (fun i : Fin (n+n) => decide (i=w))) w.val = false at neg
  rw [val_raw] at neg
  simp at neg

theorem output_earlier (A : Fin n → Fin n → Bool) (C : Circuit)
    (exactA : Represents A C) (pos : ∃ u v,A u v=true) :
    C.output < (n+n)+C.gates.length := by
  obtain ⟨u,v,yes⟩ := pos
  by_contra bad
  have h := eval_row A C exactA u v
  rw [yes,eval_eq_val,val_ge (n:=n+n) (by simp) (by omega)] at h
  contradiction

lemma positive_negative (A : Fin n → Fin n → Bool)
    (sym : ∀ a b,A a b = A b a) (good : ∀ a,∃ b,A a b=true) (w : Fin (n+n)) :
    ∃ a b k : Fin n, A a b=true ∧
      ∀ v : Fin (n+n), v≠w → row a b v=true → row k k v=true := by
  refine Fin.addCases ?_ ?_ w
  · intro a
    obtain ⟨b,yes⟩ := good a
    refine ⟨a,b,b,yes,?_⟩
    intro j notA on
    change j ≠ left a at notA
    have e : j=left a ∨ j=right b := of_decide_eq_true on
    rw [e.resolve_left notA]
    simp [row]
  · intro a
    obtain ⟨b,yes⟩ := good a
    refine ⟨b,a,b,(sym b a).trans yes,?_⟩
    intro j notA on
    change j ≠ right a at notA
    have e : j=left b ∨ j=right a := of_decide_eq_true on
    rw [e.resolve_right notA]
    simp [row]

lemma no_reader {n : ℕ} (C : Circuit) (v : Fin n)
    (none : ∀ j, j < C.gates.length → v.val ∉ (gateAt C j).inputs)
    (x y : Fin n → Bool) (agree : ∀ u, u ≠ v → x u = y u) :
    ∀ w, w ≠ v.val → val C (List.ofFn x) w = val C (List.ofFn y) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hne
    by_cases raw : w < n
    · let u : Fin n := ⟨w, raw⟩
      change val C (List.ofFn x) u.val = val C (List.ofFn y) u.val
      rw [val_raw, val_raw]
      exact agree u (fun e => hne (congrArg Fin.val e))
    by_cases outside : n + C.gates.length ≤ w
    · rw [val_ge (n := n) (by simp) outside, val_ge (n := n) (by simp) outside]
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    rw [val_gate (n := n) (by simp) hj, val_gate (n := n) (by simp) hj]
    congr 1
    apply List.map_congr_left
    intro i hi
    by_cases early : i < n + j
    · simp only [if_pos early]
      exact ih i early (fun he => none j hj (he ▸ hi))
    · simp only [if_neg early]

theorem every_raw_read (A : Fin n → Fin n → Bool) (C : Circuit) (mono : Monotone2 C)
    (exactA : Represents A C) (symmetric : ∀ a b,A a b=A b a) (diag : ∀ i,A i i=false)
    (inc : ∀ a,∃ b,A a b=true) (w : Fin (n+n)) :
    ∃ j < C.gates.length, w.val ∈ (gateAt C j).inputs := by
  by_contra hn
  push Not at hn
  obtain ⟨a,b,k,yes,comp⟩ := positive_negative A symmetric inc w
  let x := row a b
  let y := row k k
  let off : Fin (n+n) → Bool := fun i => if i=w then false else x i
  have same := no_reader C w hn x off (fun i ne => by simp [off,ne]) C.output
    (by have := output_nonraw A C mono exactA diag; have := w.isLt; omega)
  have onX : C.eval (List.ofFn x)=true := (eval_row A C exactA a b).trans yes
  have onOff : C.eval (List.ofFn off)=true := same.symm.trans onX
  have onY : C.eval (List.ofFn y)=true := by
    apply circuit_monotone (n+n) C mono off y _ onOff
    intro i on
    by_cases e : i=w
    · simp [off,e] at on
    · exact comp i e (by simpa [off,e] using on)
  have noY : C.eval (List.ofFn y)=false := (eval_row A C exactA k k).trans (diag k)
  rw [noY] at onY
  contradiction
end PEqualNP.Outside.L_meta_10057_aux.Cycle.Initial

namespace PEqualNP.Outside.L_meta_10057_aux.Cycle.Initial
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_10057_aux.Bypass
variable {n : ℕ}

def MinRep (A : Fin n → Fin n → Bool) (C : Circuit) : Prop :=
  ∀ D : Circuit, Monotone2 D → Represents A D → C.size ≤ D.size

lemma minimum_of_witness (A : Fin n → Fin n → Bool) (size : ℕ)
    (has : RepSizeAtMost A size) :
    ∃ C : Circuit, Monotone2 C ∧ Represents A C ∧ MinRep A C ∧ C.size ≤ size := by
  classical
  let witness (s : ℕ) := ∃ C : Circuit, Monotone2 C ∧ Represents A C ∧ C.size = s
  have ex : ∃ s, witness s := by
    obtain ⟨D, hm, _, hr⟩ := has
    exact ⟨D.size, D, hm, hr, rfl⟩
  obtain ⟨C, hm, hr, hc⟩ := Nat.find_spec ex
  have min : MinRep A C := by
    intro D hd he
    rw [hc]
    exact Nat.find_min' ex (show witness D.size from ⟨D, hd, he, rfl⟩)
  obtain ⟨D, hmD, szD, hrD⟩ := has
  exact ⟨C, hm, hr, min, (min D hmD hrD).trans szD⟩

theorem output_last (A : Fin n → Fin n → Bool) (C : Circuit)
    (mono : Monotone2 C) (correct : Represents A C) (min : MinRep A C)
    (diag : ∀ i, A i i=false) (pos : ∃ u v, A u v=true) :
    C.output + 1 = (n+n) + C.gates.length := by
  have lo := output_nonraw A C mono correct diag
  have hi := output_earlier A C correct pos
  let m := C.output - (n+n) + 1
  have hm : m ≤ C.gates.length := by omega
  let D : Circuit := ⟨C.gates.take m, C.output⟩
  have len : D.gates.length = m := by simp [D, Nat.min_eq_left hm]
  have hd : Monotone2 D := fun g hg => mono g (List.mem_of_mem_take hg)
  have hg (k : ℕ) (hk : k < m) : gateAt D k = gateAt C k := by
    have kd : k < D.gates.length := by omega
    have kc : k < C.gates.length := by omega
    rw [gateAt_eq kd, gateAt_eq kc]
    simp [D, List.getElem_take]
  have exactD : Represents A D := by
    intro i j
    rw [← row_eq]
    have same := val_prefix (n := n+n) (C := C) (D := D)
      (x := List.ofFn (row i j)) (by simp) hm (by omega) hg C.output (by omega)
    change D.eval (List.ofFn (row i j)) = C.eval (List.ofFn (row i j)) at same
    exact same.trans (eval_row A C correct i j)
  have hsize := min D hd exactD
  change C.gates.length ≤ D.gates.length at hsize
  omega

theorem live_reader (A : Fin n → Fin n → Bool) (C : Circuit)
    (mono : Monotone2 C) (correct : Represents A C) (min : MinRep A C)
    (j : ℕ) (hj : j < C.gates.length) (notOut : (n+n)+j ≠ C.output) :
    ∃ k, j < k ∧ k < C.gates.length ∧ (n+n)+j ∈ (gateAt C k).inputs := by
  by_contra hn
  push Not at hn
  let D := bypass (n+n) C j ((n+n) + C.gates.length)
  have same : Represents A D := by
    intro i l
    rw [← row_eq]
    exact (bypass_eval_unread (n := n+n) (C := C) (by simp) (mono_ops mono) hj
      (Or.inr le_rfl) notOut.symm hn).trans (eval_row A C correct i l)
  have hsize := min D (bypass_mono mono) same
  change C.gates.length ≤ (bypass (n+n) C j ((n+n)+C.gates.length)).gates.length at hsize
  rw [bypass_length] at hsize
  omega

def Live (A : Fin n → Fin n → Bool) (C : Circuit) : Prop :=
  Monotone2 C ∧ Represents A C ∧
  C.output + 1 = (n+n) + C.gates.length ∧
  ∀ w < C.output, ∃ j < C.gates.length, w < (n+n) + j ∧ w ∈ (gateAt C j).inputs

theorem minimum_live (A : Fin n → Fin n → Bool) (C : Circuit)
    (mono : Monotone2 C) (correct : Represents A C) (min : MinRep A C)
    (sym : ∀ a b, A a b = A b a) (diag : ∀ a, A a a=false)
    (inc : ∀ a, ∃ b, A a b=true) (pos : ∃ a b, A a b=true) :
    Live A C := by
  refine ⟨mono, correct, output_last A C mono correct min diag pos, ?_⟩
  intro w hw
  by_cases raw : w < n+n
  · let v : Fin (n+n) := ⟨w, raw⟩
    obtain ⟨j, hj, read⟩ := every_raw_read A C mono correct sym diag inc v
    exact ⟨j, hj, by omega, read⟩
  · obtain ⟨k, rfl⟩ : ∃ k, w = (n+n)+k := ⟨w-(n+n), by omega⟩
    have last := output_last A C mono correct min diag pos
    obtain ⟨j, kj, hj, read⟩ := live_reader A C mono correct min k (by omega) (by omega)
    exact ⟨j, hj, by omega, read⟩

def cycle (k : ℕ) (a b : Fin (3*k)) : Bool :=
  decide (∃ i : Fin k,
    ((a.val=i.val ∨ a.val=k+i.val) ∧ (b.val=(i.val+1)%k ∨ b.val=2*k+i.val)) ∨
    ((b.val=i.val ∨ b.val=k+i.val) ∧ (a.val=(i.val+1)%k ∨ a.val=2*k+i.val)))

lemma cycle_sym (k : ℕ) (a b : Fin (3*k)) : cycle k a b = cycle k b a := by
  apply Bool.eq_iff_iff.mpr
  simp only [cycle,decide_eq_true_eq]
  constructor <;> rintro ⟨i,h⟩ <;> exact ⟨i,h.symm⟩

lemma cycle9_diag : ∀ i : Fin 27, cycle 9 i i=false := by decide +kernel
lemma cycle9_inc : ∀ i : Fin 27, ∃ j, cycle 9 i j=true := by decide +kernel
lemma cycle13_diag : ∀ i : Fin 39, cycle 13 i i=false := by decide +kernel
lemma cycle13_inc : ∀ i : Fin 39, ∃ j, cycle 13 i j=true := by decide +kernel

theorem cycle9_live (s : ℕ) (has : RepSizeAtMost (cycle 9) s) :
    ∃ C : Circuit, Live (cycle 9) C ∧ C.size ≤ s := by
  obtain ⟨C,mono,correct,min,sz⟩ := minimum_of_witness _ _ has
  exact ⟨C,minimum_live _ C mono correct min (cycle_sym 9) cycle9_diag cycle9_inc
    ⟨0, (cycle9_inc 0).choose,(cycle9_inc 0).choose_spec⟩,sz⟩

theorem cycle13_live (s : ℕ) (has : RepSizeAtMost (cycle 13) s) :
    ∃ C : Circuit, Live (cycle 13) C ∧ C.size ≤ s := by
  obtain ⟨C,mono,correct,min,sz⟩ := minimum_of_witness _ _ has
  exact ⟨C,minimum_live _ C mono correct min (cycle_sym 13) cycle13_diag cycle13_inc
    ⟨0, (cycle13_inc 0).choose,(cycle13_inc 0).choose_spec⟩,sz⟩
end PEqualNP.Outside.L_meta_10057_aux.Cycle.Initial

namespace PEqualNP.Outside.L_meta_10057_aux.Packing
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.TopForm
open PEqualNP.Outside.L_meta_10057_aux.Cycle.Initial
def rawIndex (u : V) : Fin 39 := ⟨u.val % 39,Nat.mod_lt _ (by decide)⟩
theorem shore_cases :
    (∀ v : V, color v = true → v=left (rawIndex v)) ∧
    (∀ v : V, color v = false → v=right (rawIndex v)) := by decide +kernel
set_option maxRecDepth 10000 in
theorem edge_cycle : ∀ i j : Fin 39, edge (left i) (right j) = cycle 13 i j := by decide +kernel
def rowEval (C : Circuit) (A : Finset V) := C.eval (List.ofFn (fun i : V => decide (i∈A)))
theorem rowEval_cycle {C : Circuit} (h : Represents (cycle 13) C) (i j : Fin 39) :
    rowEval C {left i,right j} = cycle 13 i j := by
  have eq : (fun x : V => decide (x∈({left i,right j} : Finset V))) = row i j := by
    funext x
    simp [row]
  unfold rowEval
  rw [eq]
  exact eval_row _ _ h _ _
lemma initial_desc (C : Circuit) (ao : IsAO2 78 C) (rep : Represents (cycle 13) C) : Describes Finset.univ (rowEval C) := by
  have mono : Monotone2 C := fun g hg => ⟨ao.1 g hg, by rw [ao.2.2 g hg]⟩
  constructor
  · intro a
    simpa [rowEval] using singleton_false _ C mono rep cycle13_diag a
  · intro a b diff
    have rhs : decide ((graphOn Finset.univ).Adj a b) = edge a b := by
      change decide (a∈(Finset.univ : Finset V) ∧ b∈Finset.univ ∧ edge a b=true) = _
      cases e : edge a b <;> simp [e]
    rw [rhs]
    cases ca : color a <;> cases cb : color b
    · exact False.elim (diff (ca.trans cb.symm))
    · have aa := shore_cases.2 a ca
      have bb := shore_cases.1 b cb
      calc
        rowEval C {a,b} = rowEval C {left (rawIndex b),right (rawIndex a)} := by
          rw [Finset.pair_comm a b]
          exact congrArg (rowEval C) (congrArg₂ (fun x y : V => ({x,y}:Finset V)) bb aa)
        _ = cycle 13 (rawIndex b) (rawIndex a) := rowEval_cycle rep _ _
        _ = edge (left (rawIndex b)) (right (rawIndex a)) := (edge_cycle _ _).symm
        _ = edge a b := by rw [←bb,←aa,edge_symm]
    · have aa := shore_cases.1 a ca
      have bb := shore_cases.2 b cb
      calc
        rowEval C {a,b} = rowEval C {left (rawIndex a),right (rawIndex b)} := congrArg (rowEval C) (congrArg₂ (fun x y : V => ({x,y}:Finset V)) aa bb)
        _ = cycle 13 (rawIndex a) (rawIndex b) := rowEval_cycle rep _ _
        _ = edge (left (rawIndex a)) (right (rawIndex b)) := (edge_cycle _ _).symm
        _ = edge a b := by rw [←aa,←bb]
    · exact False.elim (diff (ca.trans cb.symm))
end PEqualNP.Outside.L_meta_10057_aux.Packing

-- The fold compiler is adapted from the public Shannon, Support, and Elim helpers.
namespace PEqualNP.Outside.L_meta_10057_aux.Normalize

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

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

/-- What a gate becomes, given the statuses of the wires it reads; `m` is the number of the
next new wire. The result is the gate to emit, if any, and the status of the gate's wire. -/
def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

/-- One step of the pass: `acc.1` holds the statuses of the old wires, `acc.2` the new gates. -/
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

/-- If the status of old wire `k` is a constant and some gate reads wire `k`, one gate is
saved. -/
theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

/-- The invariant of the pass, for one input `y` of the new circuit: `w` are the old wires,
and every old wire has a valid status whose value on the new wires is the old value. -/
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2


open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.Represents

private def good (m : ℕ) (g : Gate) : Prop :=
    (g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) ∧
    g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < m

private def packed (n : ℕ) (gs : List Gate) : Prop :=
    ∀ j < gs.length, good (n+j) (gs.getD j ⟨.or, []⟩)

private theorem emitted_good (op : GateOp) (hop : op ∈ ({GateOp.and,GateOp.or} : Set GateOp))
    (m : ℕ) (ins : List Stat) (valid : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, good m g := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
      (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd, good, Stat.Valid]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
      (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr, good, Stat.Valid]

private theorem packed_extend (n : ℕ) (gs : List Gate) (step : Option Gate)
    (h : packed n gs) (hstep : ∀ g ∈ step, good (n+gs.length) g) :
    packed n (gs ++ step.toList) := by
  cases step with
  | none => simpa using h
  | some g =>
    intro j hj
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj']
      exact h j hj'
    · have he : j = gs.length := by simp at hj; omega
      subst j
      simpa using hstep g (by simp)

private theorem elim_packed (n : ℕ) (gs : List Gate) (y : List Bool) (hy : y.length = n)
    (hmono : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (w : List Bool) (acc : List Stat × List Gate)
    (hs : Inv n y w acc) (hp : packed n acc.2) :
    packed n (elim n gs acc).2 := by
  induction gs generalizing acc w with
  | nil => exact hp
  | cons g gs ih =>
    have hOk (g' : Gate) (mem : g' ∈ g :: gs) : Ok g' := by
      obtain ⟨op,len⟩ := hmono g' mem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op
      exact ⟨op.elim Or.inl (Or.inr ∘ Or.inl), len⟩
    apply ih (fun g' hg => hmono g' (List.mem_cons_of_mem _ hg))
      (wiresFrom [g] w) (elimStep n acc g)
    · exact inv_elim n y hy [g] w acc
        (fun g' hg => hOk g' (List.mem_cons.mpr (Or.inl (by simpa using hg)))) hs
    · unfold elimStep
      refine packed_extend _ _ _ hp (emitted_good g.op (hmono g (by simp)).1 _ _ ?_)
      intro s h
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp h
      exact (hs.2 a).1

private def startStats (n : ℕ) : List Stat :=
    List.ofFn (fun i : Fin n => Stat.wire i)

private theorem inv_start (n : ℕ) (y : List Bool) (hy : y.length = n) :
    Inv n y y (startStats n, []) := by
  refine ⟨by simp [startStats, hy], ?_⟩
  intro i
  change ((startStats n).getD i (.const false)).Valid (n+0) ∧
    ((startStats n).getD i (.const false)).val y = y.getD i false
  by_cases hi : i < n
  · simp [startStats, List.getD_eq_getElem?_getD, hi, Stat.Valid, Stat.val]
  · simp [startStats, List.getD_eq_getElem?_getD, hi, hy, Stat.Valid, Stat.val]

private theorem packed_isAO2 {n : ℕ} {gs : List Gate} (h : packed n gs) (o : ℕ) :
    IsAO2 n (⟨gs,o⟩ : Circuit) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g mem
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp mem
    have hh := h j hj
    rw [List.getD_eq_getElem?_getD] at hh
    exact (by simpa [hj] using hh.1)
  · intro j hj i hi
    exact (h j hj).2.2 i hi
  · intro g mem
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp mem
    have hh := h j hj
    rw [List.getD_eq_getElem?_getD] at hh
    exact (by simpa [hj] using hh.2.1)

/-- Fold missing inputs, constants, and copies, emitting a backward binary AND/OR list. -/
theorem normalize_nonconstant {n : ℕ} {C : Circuit} (mono : Monotone2 C)
    {x y : List Bool} (hx : x.length = n) (hy : y.length = n) (hne : C.eval x ≠ C.eval y) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ D.output < n+D.gates.length ∧
      ∀ z : List Bool, z.length = n → D.eval z = C.eval z := by
  let a := elim n C.gates (startStats n, [])
  have hOk (g : Gate) (mem : g ∈ C.gates) : Ok g := by
    obtain ⟨op,len⟩ := mono g mem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op
    exact ⟨op.elim Or.inl (Or.inr ∘ Or.inl), len⟩
  have hInv (z : List Bool) (hz : z.length = n) :
      Inv n z (wiresFrom C.gates z) a :=
    inv_elim n z hz C.gates z _ hOk (inv_start n z hz)
  have hp : packed n a.2 := elim_packed n C.gates x hx mono x _
    (inv_start n x hx) (by simp [packed])
  have hl : a.2.length ≤ C.gates.length := by
    simpa [a] using elim_len n C.gates (startStats n, [])
  cases hs : a.1.getD C.output (.const false) with
  | const b =>
    apply False.elim
    apply hne
    have ex := ((hInv x hx).2 C.output).2
    have ey := ((hInv y hy).2 C.output).2
    rw [hs] at ex ey
    exact ex.symm.trans ey
  | wire o =>
    have hh := ((hInv x hx).2 C.output).1
    rw [hs] at hh
    refine ⟨⟨a.2,o⟩, packed_isAO2 hp o, hl, hh, ?_⟩
    intro z hz
    have e := ((hInv z hz).2 C.output).2
    rw [hs] at e
    exact e

end PEqualNP.Outside.L_meta_10057_aux.Normalize

namespace PEqualNP.Outside.L_meta_10057_aux.Normalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_10057_aux.Cycle.Initial

/-- A least representative of a nonempty irreflexive symmetric promise relation
can be chosen in binary backward form, with every wire below its output read. -/
theorem binary_live_of_rep {n : ℕ} (A : Fin n → Fin n → Bool) {s : ℕ}
    (has : RepSizeAtMost A s) (sym : ∀ a b, A a b = A b a) (diag : ∀ a, A a a = false)
    (inc : ∀ a, ∃ b, A a b = true) (pos : ∃ a b, A a b = true) :
    ∃ D : Circuit, IsAO2 (n+n) D ∧ Represents A D ∧ D.size ≤ s ∧
      D.output+1 = n+n+D.gates.length ∧
      ∀ w < D.output, ∃ j < D.gates.length, w ∈ (gateAt D j).inputs := by
  obtain ⟨C, hm, hr, hmin, hc⟩ := minimum_of_witness A s has
  obtain ⟨u,v,huv⟩ := pos
  have different : C.eval (oneEach u v) ≠ C.eval (oneEach u u) := by
    change ∀ _ : C.eval (oneEach u v) = C.eval (oneEach u u), False
    rw [hr u v, hr u u, huv, diag]
    decide
  obtain ⟨D,hD,hDC,_,same⟩ := normalize_nonconstant hm
    (n := n+n) (x := oneEach u v) (y := oneEach u u)
    (by simp [oneEach]) (by simp [oneEach]) different
  have md : Monotone2 D := fun g hg => ⟨hD.1 g hg, by rw [hD.2.2 g hg]⟩
  have rd : Represents A D := fun a b =>
    (same _ (by simp [oneEach])).trans (hr a b)
  have dmin : MinRep A D := fun Q hQ rQ => hDC.trans (hmin Q hQ rQ)
  have full := minimum_live A D md rd dmin sym diag inc ⟨u,v,huv⟩
  refine ⟨D,hD,rd,hDC.trans hc,full.2.2.1,?_⟩
  intro w hw
  obtain ⟨j,hj,_,rw⟩ := full.2.2.2 w hw
  exact ⟨j,hj,rw⟩

theorem cycle13_binary_live {s : ℕ} (has : RepSizeAtMost (cycle 13) s) :
    ∃ D : Circuit, IsAO2 78 D ∧ Represents (cycle 13) D ∧ D.size ≤ s ∧
      D.output+1 = 78+D.gates.length ∧
      ∀ w < D.output, ∃ j < D.gates.length, w ∈ (gateAt D j).inputs :=
  binary_live_of_rep (cycle 13) has (cycle_sym 13) cycle13_diag cycle13_inc
    ⟨0,(cycle13_inc 0).choose,(cycle13_inc 0).choose_spec⟩

theorem cycle9_binary_live {s : ℕ} (has : RepSizeAtMost (cycle 9) s) :
    ∃ D : Circuit, IsAO2 54 D ∧ Represents (cycle 9) D ∧ D.size ≤ s ∧
      D.output+1 = 54+D.gates.length ∧
      ∀ w < D.output, ∃ j < D.gates.length, w ∈ (gateAt D j).inputs :=
  binary_live_of_rep (cycle 9) has (cycle_sym 9) cycle9_diag cycle9_inc
    ⟨0,(cycle9_inc 0).choose,(cycle9_inc 0).choose_spec⟩

end PEqualNP.Outside.L_meta_10057_aux.Normalize

namespace PEqualNP.Outside.L_meta_10057_aux

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover TopForm

def apparentInputs (n : ℕ) (C : Circuit) (j : Fin (n+C.gates.length)) : List ℕ :=
  if j.val < n then [] else (gateAt C (j.val-n)).inputs

def parentsOf (n : ℕ) (C : Circuit) : Parents (n+C.gates.length) :=
  fun j => (apparentInputs n C j).filterMap fun i =>
    if h : i < n+C.gates.length then some ⟨i,h⟩ else none

theorem parentsOf_mem (n : ℕ) (C : Circuit) (j i : Fin (n+C.gates.length)) :
    i ∈ parentsOf n C j ↔ i.val ∈ apparentInputs n C j := by
  unfold parentsOf
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a,ha, eq⟩
    split at eq
    · exact (congrArg Fin.val (Option.some.inj eq)) ▸ ha
    · cases eq
  · intro h
    refine ⟨i.val,h,?_⟩
    simp [i.isLt]

theorem apparent_back {n : ℕ} {C : Circuit} (back : ReadsBack n C)
    {j : Fin (n+C.gates.length)} {i : ℕ} (mem : i ∈ apparentInputs n C j) : i < j.val := by
  unfold apparentInputs at mem
  split at mem
  · cases mem
  · rename_i lower
    have bound := j.isLt
    have hj : j.val-n < C.gates.length := by omega
    have hi := back _ hj i mem
    omega

theorem parentsOf_back {n : ℕ} {C : Circuit} (back : ReadsBack n C) :
    ∀ j i, i ∈ parentsOf n C j → i < j :=
  fun j i mem => apparent_back back ((parentsOf_mem n C j i).mp mem)

theorem parentsOf_vals {n : ℕ} {C : Circuit} (back : ReadsBack n C)
    (j : Fin (n+C.gates.length)) :
    (parentsOf n C j).map Fin.val = apparentInputs n C j := by
  unfold parentsOf
  generalize hlist : apparentInputs n C j = ins
  have bound (i : ℕ) (hit : i ∈ ins) : i < n+C.gates.length := by
    rw [←hlist] at hit
    exact (apparent_back back hit).trans j.isLt
  clear hlist
  induction ins with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filterMap_cons, dif_pos (bound a (by simp)),
      List.map_cons]
    rw [ih (fun i mem => bound i (List.mem_cons_of_mem _ mem))]

theorem circuit_slot_bound {n : ℕ} {C : Circuit} (ha : IsAO2 n C) :
    slots (parentsOf n C) ≤ 2*C.gates.length := by
  unfold slots
  have rb (j : Fin (n+C.gates.length)) :
      (parentsOf n C j).length ≤ if j.val < n then 0 else 2 := by
    rw [← List.length_map (f := (Fin.val : Fin (n+C.gates.length) → ℕ)),
      parentsOf_vals ha.2.1]
    unfold apparentInputs
    split
    · simp
    · rename_i notRaw
      have hj : j.val-n < C.gates.length := by have h := j.isLt; omega
      have member : gateAt C (j.val-n) ∈ C.gates := by
        simp [gateAt, List.getD_eq_getElem?_getD, hj, List.getElem_mem]
      exact (ha.2.2 _ member).le
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => rb j)
  refine h.trans ?_
  rw [Fin.sum_univ_add]
  have raw (j : Fin n) :
      (if (Fin.castAdd C.gates.length j).val < n then 0 else 2) = 0 := if_pos j.isLt
  have gate (j : Fin C.gates.length) :
      (if (Fin.natAdd n j).val < n then 0 else 2) = 2 := by
    apply if_neg
    change ¬ n+j.val < n
    omega
  simp only [raw,gate]
  simp [Nat.mul_comm]

theorem live_fanout {n : ℕ} {C : Circuit} (ha : IsAO2 n C)
    (last : C.output+1=n+C.gates.length)
    (live : ∀ w < C.output, ∃ j < C.gates.length, w ∈ (gateAt C j).inputs) :
    let o : Fin (n+C.gates.length) := ⟨C.output,by omega⟩
    (∀ w ≠ o, 1 ≤ fanout (parentsOf n C) w) ∧ fanout (parentsOf n C) o = 0 := by
  dsimp only
  refine ⟨?_,?_⟩
  · intro w ne
    have h := w.isLt
    have nd : w.val ≠ C.output := fun he => ne (Fin.ext he)
    obtain ⟨j,jl,mem⟩ := live w.val (by omega)
    let dst : Fin (n+C.gates.length) := ⟨n+j, by omega⟩
    have input : w ∈ parentsOf n C dst := by
      rw [parentsOf_mem]
      simpa [apparentInputs, dst] using mem
    have hpos := List.count_pos_iff.mpr input
    unfold fanout
    exact hpos.trans_le (Finset.single_le_sum (f := fun j => (parentsOf n C j).count w)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ dst))
  · unfold fanout
    apply Finset.sum_eq_zero
    intro j _
    apply Nat.eq_zero_of_not_pos
    intro h
    have mem := List.count_pos_iff.mp h
    have hw := parentsOf_back ha.2.1 j _ mem
    have hj := j.isLt
    change C.output < j.val at hw
    omega

theorem circuit_initial_excess (C : Circuit) (ha : IsAO2 78 C)
    (small : C.size ≤ 84) (last : C.output+1=78+C.gates.length)
    (live : ∀ w < C.output, ∃ j < C.gates.length, w ∈ (gateAt C j).inputs) :
    excess (parentsOf 78 C) ≤ 7 := by
  obtain ⟨every, gone⟩ := live_fanout ha last live
  exact initial_excess_le_seven _ _ every gone (circuit_slot_bound ha) small

theorem circuit_excess_le {n : ℕ} (C : Circuit) (ha : IsAO2 n C)
    (last : C.output+1=n+C.gates.length)
    (live : ∀ w < C.output, ∃ j < C.gates.length, w ∈ (gateAt C j).inputs) :
    excess (parentsOf n C) ≤ C.size + 1 - n := by
  obtain ⟨every, gone⟩ := live_fanout ha last live
  have balance := excess_eq_slots (parentsOf n C) _ every gone
  have cap := circuit_slot_bound ha
  change _ ≤ C.gates.length + 1 - n
  omega

end PEqualNP.Outside.L_meta_10057_aux

namespace PEqualNP.Outside.L_meta_10057_aux.Cycle.CircuitDag

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover TopForm
open PEqualNP.Outside.L_meta_10057_aux
open PEqualNP.Outside.L_meta_10057_aux.Bypass

variable {n : ℕ} {C : Circuit}

def code (n : ℕ) (C : Circuit) (j : Fin (n+C.gates.length)) :
    Node (Fin n) (n+C.gates.length) :=
  if h : j.val < n then .input ⟨j.val,h⟩
  else match parentsOf n C j with
    | [a,b] => match (gateAt C (j.val-n)).op with
      | .and => .all a b
      | _ => .any a b
    | _ => .zero

theorem parent_pair (ao : IsAO2 n C) (j : Fin (n+C.gates.length))
    (ng : ¬ j.val < n) :
    ∃ a b, parentsOf n C j = [a,b] := by
  have hj : j.val-n < C.gates.length := by have h := j.isLt; omega
  have hlen : (parentsOf n C j).length = 2 := by
    rw [← List.length_map (f := Fin.val), parentsOf_vals ao.2.1, apparentInputs, if_neg ng]
    exact ao.2.2 _ (gateAt_mem hj)
  generalize he : parentsOf n C j = l at hlen ⊢
  cases l with
  | nil => simp at hlen
  | cons a l =>
    cases l with
    | nil => simp at hlen
    | cons b l =>
      cases l with
      | nil => exact ⟨a,b,rfl⟩
      | cons c l => simp at hlen

theorem code_parents (ao : IsAO2 n C) (j : Fin (n+C.gates.length)) :
    (code n C j).wires = parentsOf n C j := by
  by_cases hr : j.val<n
  · simp [code, hr, Node.wires, parentsOf, apparentInputs]
  · obtain ⟨a,b,hs⟩ := parent_pair ao j hr
    have hj : j.val-n < C.gates.length := by have h := j.isLt; omega
    rcases ao.1 _ (gateAt_mem hj) with ha | ha <;>
      simp [code, hr, hs, ha, Node.wires]

def dag (ao : IsAO2 n C) : Dag (Fin n) (n+C.gates.length) where
  code := code n C
  back j i h := parentsOf_back ao.2.1 j i ((code_parents ao j).symm ▸ h)
  inputs_unique i j x hi hj := by
    have aux (w : Fin (n+C.gates.length)) (hx : code n C w = .input x) : w.val=x.val := by
      by_cases hr : w.val<n
      · simp [code,hr] at hx
        exact congrArg Fin.val hx
      · obtain ⟨a,b,hs⟩ := parent_pair ao w hr
        have hw : w.val-n < C.gates.length := by have h := w.isLt; omega
        rcases ao.1 _ (gateAt_mem hw) with ha | ha <;> simp [code,hr,hs,ha] at hx
    exact Fin.ext ((aux i hi).trans (aux j hj).symm)

theorem parents_eq (ao : IsAO2 n C) : (dag ao).parents = parentsOf n C :=
  funext (code_parents ao)

theorem raw_code (ao : IsAO2 n C) (u : Fin n) :
    (dag ao).code (u.castAdd C.gates.length) = .input u := by
  have h : (u.castAdd C.gates.length).val < n := u.isLt
  simp [dag, code, h]

theorem evalWire (ao : IsAO2 n C) (x : Fin n → Bool) (w : Fin (n+C.gates.length)) :
    (dag ao).eval x (fun _ => none) w = val C (List.ofFn x) w.val := by
  have hx : (List.ofFn x).length = n := List.length_ofFn
  induction w using WellFoundedLT.induction with
  | ind w ih =>
    by_cases hr : w.val<n
    · have hcode : (dag ao).code w = .input ⟨w.val,hr⟩ := by
        change code n C w = _
        unfold code
        rw [dif_pos hr]
      rw [val_input hx hr, Dag.eval]
      cases hc : (dag ao).code w <;> simp [hc] at hcode
      subst_vars
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hr]
    · obtain ⟨a,b,hs⟩ := parent_pair ao w hr
      have ha : a < w := parentsOf_back ao.2.1 w a (by simp [hs])
      have hb : b < w := parentsOf_back ao.2.1 w b (by simp [hs])
      have hj : w.val-n < C.gates.length := by have h := w.isLt; omega
      have hw : n+(w.val-n)=w.val := by omega
      have vals := parentsOf_vals ao.2.1 w
      rw [hs, apparentInputs, if_neg hr] at vals
      change [a.val,b.val] = (gateAt C (w.val-n)).inputs at vals
      have run := val_gate (C := C) hx hj
      rw [hw, ← vals] at run
      have hla : a.val < w.val := ha
      have hlb : b.val < w.val := hb
      rw [run, Dag.eval]
      rcases ao.1 _ (gateAt_mem hj) with hop | hop
      · have hcode : (dag ao).code w = .all a b := by simp [dag,code,hr,hs,hop]
        cases hc : (dag ao).code w <;> simp [hc] at hcode
        obtain ⟨ea,eb⟩ := hcode
        subst_vars
        simp [hop, GateOp.eval, hla, hlb, ih _ ha, ih _ hb]
      · have hcode : (dag ao).code w = .any a b := by simp [dag,code,hr,hs,hop]
        cases hc : (dag ao).code w <;> simp [hc] at hcode
        obtain ⟨ea,eb⟩ := hcode
        subst_vars
        simp [hop, GateOp.eval, hla, hlb, ih _ ha, ih _ hb]

theorem evalOutput (ao : IsAO2 n C) (valid : C.output < n+C.gates.length)
    (x : Fin n → Bool) : (dag ao).eval x (fun _ => none) ⟨C.output,valid⟩ =
      C.eval (List.ofFn x) := evalWire ao x _

end PEqualNP.Outside.L_meta_10057_aux.Cycle.CircuitDag

namespace PEqualNP.Outside.L_meta_10057_aux.Packing
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.Represents
open PEqualNP.Outside.L_meta_10057_aux.Cycle.Initial PEqualNP.Outside.L_meta_10057_aux.Cycle.CircuitDag
open PEqualNP.Outside.L_meta_10057_aux PEqualNP.Outside.L_meta_10057_aux.Normalize
theorem no_eighty_four : ¬ RepSizeAtMost (cycle 13) 84 := by
  intro has
  obtain ⟨C,ao,rep,small,last,live⟩ := cycle13_binary_live has
  have valid : C.output < 78+C.gates.length := by omega
  let o : Fin (78+C.gates.length) := ⟨C.output,valid⟩
  have endw (p : Fin (78+C.gates.length)) : p≤o := by
    change p.val ≤ C.output
    have := p.isLt
    omega
  have sem : (fun A : Finset V => (dag ao).value A o) = rowEval C := by
    funext A
    exact evalOutput ao valid _
  have desc : Describes Finset.univ (fun A : Finset V => (dag ao).value A o) := sem ▸ initial_desc C ao rep
  have lower := excess_nine (dag ao) o endw desc
  rw [parents_eq ao] at lower
  have upper := circuit_initial_excess C ao small last live
  omega
end PEqualNP.Outside.L_meta_10057_aux.Packing

theorem PEqualNP.Outside.L_meta_10057 : ¬ (PEqualNP.Represents.RepSizeAtMost (fun a b : Fin 39 => decide (∃ i : Fin 13, ((a.val = i.val ∨ a.val = 13 + i.val) ∧ (b.val = (i.val + 1) % 13 ∨ b.val = 26 + i.val)) ∨ ((b.val = i.val ∨ b.val = 13 + i.val) ∧ (a.val = (i.val + 1) % 13 ∨ a.val = 26 + i.val)))) 84) :=
  PEqualNP.Outside.L_meta_10057_aux.Packing.no_eighty_four
