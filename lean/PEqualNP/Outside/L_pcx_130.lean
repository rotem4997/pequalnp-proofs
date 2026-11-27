import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_130_aux

namespace PNP130Dag

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

inductive Rule (F : Set (LinClause V)) (pi : List (LinClause V)) (i : Fin pi.length)
    : Type
  | ax (inFormula : pi.get i ∈ F)
  | res (j k : Fin pi.length) (hj : i < j) (hk : i < k)
      (valid : IsLinResolvent (pi.get j) (pi.get k) (pi.get i))
  | weak (j : Fin pi.length) (hj : i < j)
      (valid : ∀ a, LinClauseSat a (pi.get j) → LinClauseSat a (pi.get i))

def Rule.parents {F : Set (LinClause V)} {pi : List (LinClause V)}
    {i : Fin pi.length} : Rule F pi i → List (Fin pi.length)
  | .ax _ => []
  | .res j k _ _ _ => [j, k]
  | .weak j _ _ => [j]

theorem Rule.lt_of_mem_parents {F : Set (LinClause V)} {pi : List (LinClause V)}
    {i j : Fin pi.length} (r : Rule F pi i) (h : j ∈ r.parents) : i < j := by
  cases r with
  | ax _ => simp [parents] at h
  | res a b ha hb _ =>
    simp [parents] at h
    rcases h with rfl | rfl <;> assumption
  | weak a ha _ =>
    simp only [parents, List.mem_singleton] at h
    simpa [h] using ha

def Rule.cons {F : Set (LinClause V)} {pi : List (LinClause V)}
    {i : Fin pi.length} (C : LinClause V) (r : Rule F pi i) :
    Rule F (C :: pi) i.succ := by
  cases r with
  | ax h => exact .ax (by simpa using h)
  | res j k hj hk h =>
    exact .res j.succ k.succ (by simpa using hj) (by simpa using hk) (by simpa using h)
  | weak j hj h =>
    exact .weak j.succ (by simpa using hj) (by simpa using h)

theorem line_rules {F : Set (LinClause V)} {pi : List (LinClause V)}
    (deriv : IsLinDerivation F pi) : ∀ i, Nonempty (Rule F pi i) := by
  classical
  induction deriv with
  | nil =>
    intro i
    exact Fin.elim0 i
  | @ax pi C deriv hC ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨.ax (by simpa using hC)⟩
    · exact ⟨(Classical.choice (ih j)).cons C⟩
  | @res pi C D R deriv hC hD hr ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · obtain ⟨j, hj, ej⟩ := List.mem_iff_getElem.mp hC
      obtain ⟨k, hk, ek⟩ := List.mem_iff_getElem.mp hD
      let j' : Fin pi.length := ⟨j, hj⟩
      let k' : Fin pi.length := ⟨k, hk⟩
      have ej' : pi.get j' = C := ej
      have ek' : pi.get k' = D := ek
      refine ⟨.res j'.succ k'.succ (Fin.succ_pos _) (Fin.succ_pos _) ?_⟩
      change IsLinResolvent (pi.get j') (pi.get k') R
      rwa [ej', ek']
    · exact ⟨(Classical.choice (ih j)).cons R⟩
  | @weak pi C D deriv hC hw ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · obtain ⟨j, hj, ej⟩ := List.mem_iff_getElem.mp hC
      let j' : Fin pi.length := ⟨j, hj⟩
      have ej' : pi.get j' = C := ej
      refine ⟨.weak j'.succ (Fin.succ_pos _) ?_⟩
      change ∀ a, LinClauseSat a (pi.get j') → LinClauseSat a D
      rwa [ej']
    · exact ⟨(Classical.choice (ih j)).cons D⟩

noncomputable def choose_rules {F : Set (LinClause V)} {pi : List (LinClause V)}
    (deriv : IsLinDerivation F pi) (i : Fin pi.length) : Rule F pi i :=
  Classical.choice (line_rules deriv i)

theorem derivation_dedup {F : Set (LinClause V)} {pi : List (LinClause V)}
    (deriv : IsLinDerivation F pi) :
    ∃ rho, IsLinDerivation F rho ∧ rho.Nodup ∧ rho.Sublist pi ∧
      ∀ c, c ∈ pi ↔ c ∈ rho := by
  classical
  induction deriv with
  | nil =>
    exact ⟨[], .nil, List.nodup_nil, .slnil, fun _ => Iff.rfl⟩
  | @ax pi C deriv hC ih =>
    obtain ⟨rho, hd, nd, sub, eq⟩ := ih
    by_cases h : C ∈ rho
    · refine ⟨rho, hd, nd, sub.cons C, fun c => ?_⟩
      simp only [List.mem_cons, eq]
      exact ⟨fun H => H.elim (fun e => e.symm ▸ h) id, Or.inr⟩
    · exact ⟨C :: rho, .ax hd hC, List.nodup_cons.mpr ⟨h, nd⟩,
        sub.cons_cons C, fun c => by simp [eq]⟩
  | @res pi C D R deriv hC hD hr ih =>
    obtain ⟨rho, hd, nd, sub, eq⟩ := ih
    by_cases h : R ∈ rho
    · refine ⟨rho, hd, nd, sub.cons R, fun c => ?_⟩
      simp only [List.mem_cons, eq]
      exact ⟨fun H => H.elim (fun e => e.symm ▸ h) id, Or.inr⟩
    · exact ⟨R :: rho, .res hd ((eq C).mp hC) ((eq D).mp hD) hr,
        List.nodup_cons.mpr ⟨h, nd⟩, sub.cons_cons R, fun c => by simp [eq]⟩
  | @weak pi C D deriv hC hw ih =>
    obtain ⟨rho, hd, nd, sub, eq⟩ := ih
    by_cases h : D ∈ rho
    · refine ⟨rho, hd, nd, sub.cons D, fun c => ?_⟩
      simp only [List.mem_cons, eq]
      exact ⟨fun H => H.elim (fun e => e.symm ▸ h) id, Or.inr⟩
    · exact ⟨D :: rho, .weak hd ((eq C).mp hC) hw,
        List.nodup_cons.mpr ⟨h, nd⟩, sub.cons_cons D, fun c => by simp [eq]⟩

theorem derivation_trim {F : Set (LinClause V)} {pi : List (LinClause V)}
    (rules : ∀ i, Rule F pi i) (keep : List (Fin pi.length))
    (order : keep.Pairwise (· < ·))
    (closed : ∀ i ∈ keep, ∀ j ∈ (rules i).parents, j ∈ keep) :
    IsLinDerivation F (keep.map pi.get) := by
  induction keep with
  | nil => exact .nil
  | cons i keep ih =>
    obtain ⟨head, later⟩ := List.pairwise_cons.mp order
    have ht : ∀ j ∈ keep, ∀ k ∈ (rules j).parents, k ∈ keep := by
      intro j hj k hk
      have mem := closed j (List.mem_cons_of_mem i hj) k hk
      rcases List.mem_cons.mp mem with eq | hm
      · have hlt := (rules j).lt_of_mem_parents hk
        rw [eq] at hlt
        exact False.elim (not_lt_of_ge (head _ hj).le hlt)
      · exact hm
    have prev := ih later ht
    have hm : ∀ j ∈ (rules i).parents, j ∈ keep := by
      intro j hj
      have hlt := (rules i).lt_of_mem_parents hj
      have mem := closed i List.mem_cons_self j hj
      rcases List.mem_cons.mp mem with eq | mem
      · exact False.elim (hlt.ne eq.symm)
      · exact mem
    generalize eq : rules i = r at hm
    cases r with
    | ax h => exact .ax prev h
    | res j k _ _ h =>
      have hj := hm j (by simp [Rule.parents])
      have hk := hm k (by simp [Rule.parents])
      exact .res prev (List.mem_map_of_mem hj) (List.mem_map_of_mem hk) h
    | weak j _ h =>
      have hj := hm j (by simp [Rule.parents])
      exact .weak prev (List.mem_map_of_mem hj) h

def Parent {F : Set (LinClause V)} {pi : List (LinClause V)}
    (rules : ∀ i, Rule F pi i) (i j : Fin pi.length) : Prop :=
  j ∈ (rules i).parents

abbrev Reaches {F : Set (LinClause V)} {pi : List (LinClause V)}
    (rules : ∀ i, Rule F pi i) := Relation.ReflTransGen (Parent rules)

theorem reachable_of_shortest {F : Set (LinClause V)} {pi : List (LinClause V)}
    (rules : ∀ i, Rule F pi i) (root : Fin pi.length) (hroot : pi.get root = ∅)
    (shortest : ∀ rho, IsLinDerivation F rho → (∅ : LinClause V) ∈ rho → pi.length ≤ rho.length) :
    ∀ i, Reaches rules root i := by
  classical
  let keep := (List.finRange pi.length).filter (fun j => decide (Reaches rules root j))
  have order : keep.Pairwise (· < ·) := (List.pairwise_lt_finRange _).filter _
  have member (j : Fin pi.length) : j ∈ keep ↔ Reaches rules root j := by
    simp [keep, List.mem_finRange]
  have closed : ∀ i ∈ keep, ∀ j ∈ (rules i).parents, j ∈ keep := by
    intro i hi j hj
    exact (member j).mpr ((member i).mp hi |>.tail hj)
  have deriv := derivation_trim rules keep order closed
  have emptyMem : (∅ : LinClause V) ∈ keep.map pi.get := by
    rw [← hroot]
    exact List.mem_map_of_mem ((member root).mpr .refl)
  have lengthBound := shortest _ deriv emptyMem
  rw [List.length_map] at lengthBound
  have sub : keep.Sublist (List.finRange pi.length) := List.filter_sublist
  have same : keep = List.finRange pi.length :=
    sub.eq_of_length (by have := sub.length_le; simp at this; simp; omega)
  intro i
  exact (member i).mp (same.symm ▸ List.mem_finRange i)

structure ShortestDag (F : Set (LinClause V)) where
  pi : List (LinClause V)
  nodup : pi.Nodup
  root : Fin pi.length
  rootEmpty : pi.get root = ∅
  rules : ∀ i, Rule F pi i
  reachable : ∀ i, Reaches rules root i

theorem shortest_dag {F : Set (LinClause V)} {pi : List (LinClause V)}
    (deriv : IsLinDerivation F pi) (contains : (∅ : LinClause V) ∈ pi) :
    ∃ d : ShortestDag F, d.pi.length ≤ pi.length := by
  classical
  let P (n : Nat) := ∃ rho, IsLinDerivation F rho ∧ (∅ : LinClause V) ∈ rho ∧ rho.length = n
  have exist : ∃ n, P n := ⟨pi.length, pi, deriv, contains, rfl⟩
  obtain ⟨rho, hr, hempty, hlen⟩ := Nat.find_spec exist
  have shortest (tau : List (LinClause V)) (h : IsLinDerivation F tau)
      (he : (∅ : LinClause V) ∈ tau) : rho.length ≤ tau.length := by
    rw [hlen]
    exact Nat.find_min' exist ⟨tau, h, he, rfl⟩
  obtain ⟨delta, hd, nd, sub, eq⟩ := derivation_dedup hr
  have bdd := shortest delta hd ((eq ∅).mp hempty)
  have same : delta = rho := sub.eq_of_length (Nat.le_antisymm sub.length_le bdd)
  have noDup : rho.Nodup := same ▸ nd
  obtain ⟨k, hk, ek⟩ := List.mem_iff_getElem.mp hempty
  let root : Fin rho.length := ⟨k, hk⟩
  have rootEmpty : rho.get root = ∅ := ek
  let rules := choose_rules hr
  exact ⟨⟨rho, noDup, root, rootEmpty, rules,
    reachable_of_shortest rules root rootEmpty shortest⟩, shortest pi deriv contains⟩

namespace ShortestDag

variable {F : Set (LinClause V)} (d : ShortestDag F)

def children (i : Fin d.pi.length) : List (Fin d.pi.length) := (d.rules i).parents

theorem children_lt (i j : Fin d.pi.length) (h : j ∈ d.children i) : i < j :=
  (d.rules i).lt_of_mem_parents h

theorem root_val_zero : d.root.val = 0 := by
  let z : Fin d.pi.length := ⟨0, Nat.zero_lt_of_lt d.root.isLt⟩
  have h := d.reachable z
  have le : ∀ v, Reaches d.rules d.root v → d.root ≤ v := by
    intro v hr
    induction hr with
    | refl => exact le_rfl
    | @tail v w _ hp ih => exact ih.trans (d.children_lt v w hp).le
  exact Nat.eq_zero_of_le_zero (le _ h)

theorem exists_parent (j : Fin d.pi.length) (hn : j.val ≠ 0) :
    ∃ i, j ∈ d.children i := by
  have h := d.reachable j
  induction h with
  | refl => exact (hn d.root_val_zero).elim
  | @tail v w hr hp _ => exact ⟨v, hp⟩

def incoming (j : Fin d.pi.length) : ℕ :=
  ∑ i : Fin d.pi.length, (d.children i).count j

theorem incoming_pos (j : Fin d.pi.length) (hn : j.val ≠ 0) : 0 < d.incoming j := by
  obtain ⟨i, hi⟩ := d.exists_parent j hn
  have hpos : 0 < (d.children i).count j := List.count_pos_iff.mpr hi
  exact hpos.trans_le (Finset.single_le_sum (fun b _ => Nat.zero_le ((d.children b).count j))
    (Finset.mem_univ i))

theorem children_length (i : Fin d.pi.length) : (d.children i).length ≤ 2 := by
  unfold children
  cases d.rules i <;> simp [Rule.parents]

theorem axiom_of_no_children (i : Fin d.pi.length) (h : d.children i = []) :
    d.pi.get i ∈ F := by
  cases hr : d.rules i with
  | ax hf => exact hf
  | res => simp [children, hr, Rule.parents] at h
  | weak => simp [children, hr, Rule.parents] at h

def AxiomIndex := { i : Fin d.pi.length // d.children i = [] }

def axiomClause (i : d.AxiomIndex) : { C : LinClause V // C ∈ F } :=
  ⟨d.pi.get i.val, d.axiom_of_no_children i.val i.property⟩

theorem axiomClause_injective : Function.Injective d.axiomClause := by
  intro a b h
  exact Subtype.ext (d.nodup.injective_get (congrArg Subtype.val h))

private theorem false_res {C D R : LinClause V} (h : IsLinResolvent C D R)
    (a : V → Bool) (hR : ¬ LinClauseSat a R) :
    ¬ LinClauseSat a C ∨ ¬ LinClauseSat a D := by
  obtain ⟨f, hC, hD, rfl⟩ := h
  by_cases hf : Odd (f.filter (fun v => a v = true)).card
  · left
    rintro ⟨q, hq, hs⟩
    refine hR ⟨q, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨?_, hq⟩), hs⟩
    rintro rfl
    have := hs.1 hf
    cases this
  · right
    rintro ⟨q, hq, hs⟩
    refine hR ⟨q, Finset.mem_union_right _ (Finset.mem_erase.2 ⟨?_, hq⟩), hs⟩
    rintro rfl
    exact hf (hs.2 rfl)

theorem false_child_or_axiom (a : V → Bool) (i : Fin d.pi.length)
    (hf : ¬ LinClauseSat a (d.pi.get i)) :
    d.children i = [] ∨ ∃ j ∈ d.children i, ¬ LinClauseSat a (d.pi.get j) := by
  cases hr : d.rules i with
  | ax hae => exact Or.inl (by simp [children, hr, Rule.parents])
  | res j k hj hk hv =>
    rcases false_res hv a hf with eh | eh
    · exact Or.inr ⟨j, by simp [children, hr, Rule.parents], eh⟩
    · exact Or.inr ⟨k, by simp [children, hr, Rule.parents], eh⟩
  | weak j hj hv =>
    exact Or.inr ⟨j, by simp [children, hr, Rule.parents], fun hj' => hf (hv a hj')⟩

theorem reaches_axiom (a : V → Bool) (i : Fin d.pi.length)
    (hf : ¬ LinClauseSat a (d.pi.get i)) :
    ∃ j, Reaches d.rules i j ∧ d.children j = [] ∧ ¬ LinClauseSat a (d.pi.get j) := by
  have aux (k : ℕ) : ∀ i : Fin d.pi.length, d.pi.length - i.val = k →
      ¬ LinClauseSat a (d.pi.get i) →
      ∃ j, Reaches d.rules i j ∧ d.children j = [] ∧ ¬ LinClauseSat a (d.pi.get j) := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro i hi hf
      rcases d.false_child_or_axiom a i hf with e | ⟨j, hj, hn⟩
      · exact ⟨i, .refl, e, hf⟩
      · have edge := d.children_lt i j hj
        have hl : d.pi.length - j.val < k := by
          have hbound := j.isLt
          have hv : i.val < j.val := edge
          omega
        obtain ⟨w, hpath, he, hw⟩ := ih (d.pi.length - j.val) hl j rfl hn
        exact ⟨w, hpath.head hj, he, hw⟩
  exact aux _ i rfl hf

theorem incoming_at_first : d.incoming d.root = 0 := by
  classical
  unfold incoming
  apply Finset.sum_eq_zero
  intro i _
  apply List.count_eq_zero_of_not_mem
  intro h
  have hp : i.val < d.root.val := d.children_lt i d.root h
  rw [d.root_val_zero] at hp
  omega

end ShortestDag

end PNP130Dag

namespace PNP130Dag

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

abbrev Test (V : Type) := Finset V × Bool

def testParity (a : V → Bool) (f : Finset V) : Bool :=
  decide (Odd (f.filter (fun v => a v = true)).card)

noncomputable def Rule.labelled {F : Set (LinClause V)} {pi : List (LinClause V)}
    {i : Fin pi.length} : Rule F pi i → List (Fin pi.length × Option (Test V))
  | .ax _ => []
  | .weak j _ _ => [(j, none)]
  | .res j k _ _ hr =>
      let f := Classical.choose hr
      [(j, some (f, true)), (k, some (f, false))]

theorem Rule.labelled_map {F : Set (LinClause V)} {pi : List (LinClause V)}
    {i : Fin pi.length} (r : Rule F pi i) : r.labelled.map Prod.fst = r.parents := by
  cases r <;> rfl

inductive LocalTree (V I : Type)
  | ax (i : I)
  | exit (j : I)
  | weak (i : I) (child : LocalTree V I)
  | res (i : I) (pivot : Finset V) (left right : LocalTree V I)

inductive LocalTree.Route {I : Type} :
    LocalTree V I → I → List (Option (Test V)) → Prop
  | ax (i : I) : Route (.ax i) i []
  | weak {i t j qs} (h : Route t j qs) : Route (.weak i t) j (none :: qs)
  | left {i f l r j qs} (h : Route l j qs) : Route (.res i f l r) j (some (f,true) :: qs)
  | right {i f l r j qs} (h : Route r j qs) : Route (.res i f l r) j (some (f,false) :: qs)

namespace ShortestDag

variable {F : Set (LinClause V)} (d : ShortestDag F)

noncomputable abbrev labels (i : Fin d.pi.length) := (d.rules i).labelled

theorem label_child {i j : Fin d.pi.length} {q : Option (Test V)}
    (h : (j,q) ∈ d.labels i) : j ∈ d.children i := by
  rw [children, ← (d.rules i).labelled_map]
  exact List.mem_map.mpr ⟨(j,q), h, rfl⟩

theorem labelled_of_child {i j : Fin d.pi.length} (h : j ∈ d.children i) :
    ∃ q, (j,q) ∈ d.labels i := by
  rw [children, ← (d.rules i).labelled_map] at h
  obtain ⟨⟨k,q⟩, hk, he⟩ := List.mem_map.mp h
  cases he
  exact ⟨q,hk⟩

theorem res_children_ne {i j k : Fin d.pi.length} (hj : i < j)
    (hr : IsLinResolvent (d.pi.get j) (d.pi.get k) (d.pi.get i)) : j ≠ k := by
  rintro rfl
  obtain ⟨f, h0, h1, he⟩ := hr
  have heq : (d.pi.get j).erase (f,false) ∪ (d.pi.get j).erase (f,true) =
      d.pi.get j := by
    ext q
    simp only [Finset.mem_union, Finset.mem_erase]
    constructor
    · exact fun h => h.elim And.right And.right
    · intro h
      by_cases hq : q = (f,false)
      · exact Or.inr ⟨by simp [hq], h⟩
      · exact Or.inl ⟨hq, h⟩
  have eq := d.nodup.injective_get (he.trans heq)
  exact (ne_of_lt hj) eq

theorem labels_unique {i j : Fin d.pi.length} {q r : Option (Test V)}
    (hq : (j,q) ∈ d.labels i) (hr : (j,r) ∈ d.labels i) : q = r := by
  cases h : d.rules i with
  | ax => simp [labels, h, Rule.labelled] at hq
  | weak k hk hw => simp [labels, h, Rule.labelled] at hq hr; exact hq.2.trans hr.2.symm
  | res k l hk hl hv =>
    have hkl := d.res_children_ne hk hv
    simp [labels, h, Rule.labelled] at hq hr
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl,rfl⟩ <;>
      rcases hr with ⟨he, rfl⟩ | ⟨he,rfl⟩
    · rfl
    · exact (hkl he).elim
    · exact (hkl he.symm).elim
    · rfl

theorem parent_unique {i k j : Fin d.pi.length} (hin : d.incoming j = 1)
    (hi : j ∈ d.children i) (hk : j ∈ d.children k) : i = k := by
  classical
  by_contra h
  have hci := List.count_pos_iff.mpr hi
  have hck := List.count_pos_iff.mpr hk
  have subset : ({i,k} : Finset (Fin d.pi.length)) ⊆ Finset.univ := Finset.subset_univ _
  have lb := Finset.sum_le_sum_of_subset_of_nonneg subset (fun x _ _ =>
    Nat.zero_le ((d.children x).count j))
  rw [← incoming, hin] at lb
  simp [h] at lb
  omega

def Accepts (a : V → Bool) : Option (Test V) → Prop
  | none => True
  | some (f,b) => testParity a f = b

private theorem res_false_label {i j k : Fin d.pi.length}
    (hr : IsLinResolvent (d.pi.get j) (d.pi.get k) (d.pi.get i))
    (a : V → Bool) (hf : ¬ LinClauseSat a (d.pi.get i)) :
    if testParity a (Classical.choose hr) then ¬ LinClauseSat a (d.pi.get j)
    else ¬ LinClauseSat a (d.pi.get k) := by
  let f := Classical.choose hr
  obtain ⟨_, _, he⟩ := Classical.choose_spec hr
  change (if testParity a f then ¬ LinClauseSat a (d.pi.get j)
    else ¬ LinClauseSat a (d.pi.get k))
  by_cases odd : Odd (f.filter (fun v => a v = true)).card
  · simp [testParity, odd]
    rintro ⟨q,hq,hqs⟩
    apply hf
    refine ⟨q, ?_, hqs⟩
    rw [he]
    refine Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, hq⟩)
    rintro rfl
    exact Bool.noConfusion (hqs.1 odd)
  · simp [testParity, odd]
    rintro ⟨q,hq,hqs⟩
    apply hf
    refine ⟨q, ?_, hqs⟩
    rw [he]
    refine Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hq⟩)
    rintro rfl
    exact odd (hqs.2 rfl)

theorem false_label_or_axiom (a : V → Bool) (i : Fin d.pi.length)
    (hf : ¬ LinClauseSat a (d.pi.get i)) :
    d.children i = [] ∨ ∃ j q, (j,q) ∈ d.labels i ∧ Accepts a q ∧
      ¬ LinClauseSat a (d.pi.get j) := by
  cases h : d.rules i with
  | ax => left; simp [children, h, Rule.parents]
  | weak j hj hw =>
    exact Or.inr ⟨j, none, by simp [labels, h, Rule.labelled], trivial, fun hn => hf (hw a hn)⟩
  | res j k hj hk hr =>
    have hv := d.res_false_label hr a hf
    cases hp : testParity a (Classical.choose hr)
    · exact Or.inr ⟨k, some (Classical.choose hr,false), by simp [labels, h, Rule.labelled],
        hp, by simpa [hp] using hv⟩
    · exact Or.inr ⟨j, some (Classical.choose hr,true), by simp [labels, h, Rule.labelled],
        hp, by simpa [hp] using hv⟩

def ActiveStep (a : V → Bool) (i j : Fin d.pi.length) : Prop :=
  ∃ q, (j,q) ∈ d.labels i ∧ Accepts a q ∧
    ¬ LinClauseSat a (d.pi.get i) ∧ ¬ LinClauseSat a (d.pi.get j)

abbrev Active (a : V → Bool) := Relation.ReflTransGen (d.ActiveStep a)

theorem active_axiom (a : V → Bool) (i : Fin d.pi.length)
    (hf : ¬ LinClauseSat a (d.pi.get i)) :
    ∃ j, d.Active a i j ∧ d.children j = [] ∧ ¬ LinClauseSat a (d.pi.get j) := by
  have aux (k : ℕ) : ∀ i : Fin d.pi.length, d.pi.length - i.val = k →
      ¬ LinClauseSat a (d.pi.get i) →
      ∃ j, d.Active a i j ∧ d.children j = [] ∧ ¬ LinClauseSat a (d.pi.get j) := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro i hi hf
      rcases d.false_label_or_axiom a i hf with e | ⟨j, q, hj, ha, hn⟩
      · exact ⟨i, .refl, e, hf⟩
      · have edge : i.val < j.val := d.children_lt i j (d.label_child hj)
        have hb := j.isLt
        have hl : d.pi.length - j.val < k := by omega
        obtain ⟨w, hpath, he, hw⟩ := ih (d.pi.length - j.val) hl j rfl hn
        exact ⟨w, hpath.head ⟨q,hj,ha,hf,hn⟩, he, hw⟩
  exact aux _ i rfl hf

theorem active_initial_clause (a : V → Bool) :
    ∃ j, d.Active a d.root j ∧ d.children j = [] ∧ ¬ LinClauseSat a (d.pi.get j) :=
  d.active_axiom a d.root (by rw [d.rootEmpty]; simp [LinClauseSat])

inductive LocalPath : Fin d.pi.length → Fin d.pi.length → List (Option (Test V)) → Prop
  | nil (i) : LocalPath i i []
  | cons {i j k q qs} (label : (j,q) ∈ d.labels i) (unique : d.incoming j = 1)
      (rest : LocalPath j k qs) : LocalPath i k (q :: qs)

theorem peel_active {a : V → Bool} {i j : Fin d.pi.length} {q : Option (Test V)}
    (h : d.Active a d.root j) (he : (j,q) ∈ d.labels i) (hu : d.incoming j = 1) :
    d.Active a d.root i ∧ Accepts a q ∧ ¬ LinClauseSat a (d.pi.get i) := by
  cases h with
  | refl => have hz := d.incoming_at_first; omega
  | @tail k j hp hs =>
    obtain ⟨r, hr, ar, hnk, _⟩ := hs
    have eq := d.parent_unique hu (d.label_child hr) (d.label_child he)
    subst k
    have eqr := d.labels_unique hr he
    exact ⟨hp, eqr ▸ ar, hnk⟩

theorem local_path_active {a : V → Bool} {i j : Fin d.pi.length} {qs}
    (hp : d.LocalPath i j qs) (ha : d.Active a d.root j)
    (hf : ¬ LinClauseSat a (d.pi.get j)) :
    d.Active a d.root i ∧ ¬ LinClauseSat a (d.pi.get i) ∧ ∀ q ∈ qs, Accepts a q := by
  induction hp with
  | nil _ => exact ⟨ha, hf, by simp⟩
  | @cons i j k q qs he hu rest ih =>
    obtain ⟨haj, hfj, acc⟩ := ih ha hf
    obtain ⟨hai, aq, hfi⟩ := d.peel_active haj he hu
    exact ⟨hai,hfi,fun r hr => (List.mem_cons.mp hr).elim (fun e => e.symm ▸ aq) (acc r)⟩

noncomputable def unroll (i : Fin d.pi.length) : LocalTree V (Fin d.pi.length) :=
  match d.rules i with
  | .ax _ => .ax i
  | .weak j _hj _ =>
      .weak i (if d.incoming j = 1 then unroll j else .exit j)
  | .res j k _hj _hk h =>
      .res i (Classical.choose h)
        (if d.incoming j = 1 then unroll j else .exit j)
        (if d.incoming k = 1 then unroll k else .exit k)
termination_by d.pi.length - i.val
decreasing_by
  all_goals
    apply Nat.sub_lt_sub_left
    · exact i.isLt
    · first | exact _hj | exact _hk

noncomputable def cutChild (j : Fin d.pi.length) : LocalTree V (Fin d.pi.length) :=
  if d.incoming j = 1 then d.unroll j else .exit j

theorem unroll_ax {i : Fin d.pi.length} {h} (hr : d.rules i = .ax h) :
    d.unroll i = .ax i := by
  rw [unroll, hr]

theorem unroll_weak {i j : Fin d.pi.length} {hj hw}
    (hr : d.rules i = .weak j hj hw) :
    d.unroll i = .weak i (d.cutChild j) := by
  rw [unroll, hr]
  rfl

theorem unroll_res {i j k : Fin d.pi.length} {hj hk hv}
    (hr : d.rules i = .res j k hj hk hv) :
    d.unroll i = .res i (Classical.choose hv) (d.cutChild j) (d.cutChild k) := by
  rw [unroll, hr]
  rfl

theorem no_route_exit {i j : Fin d.pi.length} {qs} :
    ¬ LocalTree.Route (.exit i : LocalTree V _) j qs := by
  intro h
  cases h

theorem route_of_unroll {i j : Fin d.pi.length} {qs}
    (h : LocalTree.Route (d.unroll i) j qs) :
    d.LocalPath i j qs ∧ d.children j = [] := by
  have aux (n : ℕ) : ∀ (i : Fin d.pi.length) qs, d.pi.length - i.val = n →
      LocalTree.Route (d.unroll i) j qs → d.LocalPath i j qs ∧ d.children j = [] := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro i qs hn h
      have sub (k : Fin d.pi.length) (lt : i < k) {rs}
          (hk : LocalTree.Route (d.cutChild k) j rs) :
          d.incoming k = 1 ∧ d.LocalPath k j rs ∧ d.children j = [] := by
        by_cases he : d.incoming k = 1
        · rw [cutChild, ite_eq_left he] at hk
          have size : d.pi.length - k.val < n := by
            have hlt : i.val < k.val := lt
            have bound := k.isLt
            omega
          exact ⟨he, ih _ size k rs rfl hk⟩
        · rw [cutChild, ite_eq_right he] at hk
          exact (d.no_route_exit hk).elim
      cases hr : d.rules i with
      | ax ha =>
        rw [d.unroll_ax hr] at h
        cases h
        exact ⟨.nil _, by simp [children, hr, Rule.parents]⟩
      | weak k hlt hv =>
        rw [d.unroll_weak hr] at h
        cases h with
        | weak h =>
          obtain ⟨h1,h2,h3⟩ := sub k hlt h
          exact ⟨.cons (by simp [labels,hr,Rule.labelled]) h1 h2,h3⟩
      | res k l hk hl hrule =>
        rw [d.unroll_res hr] at h
        cases h with
        | left h =>
          obtain ⟨h1,h2,h3⟩ := sub k hk h
          exact ⟨.cons (by simp [labels,hr,Rule.labelled]) h1 h2,h3⟩
        | right h =>
          obtain ⟨h1,h2,h3⟩ := sub l hl h
          exact ⟨.cons (by simp [labels,hr,Rule.labelled]) h1 h2,h3⟩
  exact aux _ i qs rfl h

theorem unroll_of_route {i j : Fin d.pi.length} {qs}
    (h : d.LocalPath i j qs) (hax : d.children j = []) :
    LocalTree.Route (d.unroll i) j qs := by
  induction h with
  | nil i =>
    cases hr : d.rules i with
    | ax h => rw [d.unroll_ax hr]; exact .ax i
    | weak => simp [children,hr,Rule.parents] at hax
    | res => simp [children,hr,Rule.parents] at hax
  | @cons i k j q qs he h1 hp ih =>
    have cut : LocalTree.Route (d.cutChild k) j qs := by
      rw [cutChild, ite_eq_left h1]
      exact ih hax
    cases hr : d.rules i with
    | ax => simp [labels,hr,Rule.labelled] at he
    | weak l hlt hv =>
      rw [d.unroll_weak hr]
      simp [labels,hr,Rule.labelled] at he
      obtain ⟨rfl,rfl⟩ := he
      exact .weak cut
    | res l r hl hr' hv =>
      rw [d.unroll_res hr]
      simp [labels,hr,Rule.labelled] at he
      rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact .left cut
      · exact .right cut

theorem local_path_append {i j k : Fin d.pi.length} {qs rs}
    (h : d.LocalPath i j qs) (g : d.LocalPath j k rs) :
    d.LocalPath i k (qs ++ rs) := by
  induction h with
  | nil => exact g
  | cons h u _ ih =>
    exact .cons h u (ih g)

theorem axiom_component (j : Fin d.pi.length) (hj : d.children j = []) :
    ∃ i qs, d.incoming i ≠ 1 ∧ LocalTree.Route (d.unroll i) j qs := by
  have aux (n : ℕ) : ∀ j : Fin d.pi.length, j.val = n →
      ∃ i qs, d.incoming i ≠ 1 ∧ d.LocalPath i j qs := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro j hn
      by_cases h : d.incoming j = 1
      · have hzero : j.val ≠ 0 := by
          intro hj
          have heq : j = d.root := Fin.ext (hj.trans d.root_val_zero.symm)
          rw [heq, d.incoming_at_first] at h
          contradiction
        obtain ⟨k, hk⟩ := d.exists_parent j hzero
        have lt : k.val < n := hn ▸ d.children_lt k j hk
        obtain ⟨i, qs, h1, hp⟩ := ih k.val lt k rfl
        obtain ⟨q, hq⟩ := d.labelled_of_child hk
        exact ⟨i, qs ++ [q], h1, d.local_path_append hp (.cons hq h (.nil _))⟩
      · exact ⟨j, [], h, .nil j⟩
  obtain ⟨i, qs, hi, hp⟩ := aux j.val j rfl
  exact ⟨i, qs, hi, d.unroll_of_route hp hj⟩

theorem unroll_route_active (a : V → Bool) {i j : Fin d.pi.length} {qs}
    (h : LocalTree.Route (d.unroll i) j qs)
    (unique : ∀ C ∈ F, ¬ LinClauseSat a C → C = d.pi.get j) :
    ¬ LinClauseSat a (d.pi.get i) ∧ ∀ q ∈ qs, Accepts a q := by
  obtain ⟨k, hk, hax, hf⟩ := d.active_initial_clause a
  have heq := d.nodup.injective_get (unique _ (d.axiom_of_no_children k hax) hf)
  subst k
  exact (d.local_path_active (d.route_of_unroll h).1 hk hf).2

end ShortestDag

end PNP130Dag

namespace Pcx130

open PEqualNP.ProofComplexity

abbrev Variable := Fin 5 × Fin 2
abbrev Assignment := Variable → Bool

structure Collision where
  left : Fin 5
  right : Fin 5
  hole : Fin 4
  ordered : left < right

def otherHoles (h : Fin 4) : List (Fin 4) :=
  (List.finRange 4).filter (· != h)

def otherRank (i j p : Fin 5) : ℕ :=
  ((List.finRange 5).filter (fun q => decide (q < p) && q != i && q != j)).length

def sampleHole (i j : Fin 5) (h : Fin 4) (phase : Fin 3) (p : Fin 5) : Fin 4 :=
  if p = i ∨ p = j then h else (otherHoles h).getD ((otherRank i j p + phase.val) % 3) h

def sample (c : Collision) (phase : Fin 3) : Assignment :=
  fun v => (sampleHole c.left c.right c.hole phase v.1).val.testBit v.2.val

def allIn (h : Fin 4) : Assignment := fun v => h.val.testBit v.2.val

theorem sample_hole_facts : ∀ (i j : Fin 5) (h : Fin 4) (r : Fin 3), i < j →
    sampleHole i j h r i = h ∧ sampleHole i j h r j = h ∧
    ∀ p q : Fin 5, p < q →
      (sampleHole i j h r p = sampleHole i j h r q ↔ p = i ∧ q = j) := by
  decide +kernel

theorem bit_geometry : ∀ (i j : Fin 5) (h : Fin 4) (p : Fin 5) (b : Fin 2), i < j →
    ((∀ r : Fin 3, (sampleHole i j h r p).val.testBit b.val = h.val.testBit b.val) ↔
      p = i ∨ p = j) ∧
    ((sampleHole i j h 0 p).val.testBit b.val ^^
      ((sampleHole i j h 1 p).val.testBit b.val ^^
        (sampleHole i j h 2 p).val.testBit b.val)) = h.val.testBit b.val := by
  decide +kernel

theorem sample_bits_xor (c : Collision) (v : Variable) :
    (sample c 0 v ^^ (sample c 1 v ^^ sample c 2 v)) = allIn c.hole v :=
  (bit_geometry c.left c.right c.hole v.1 v.2 c.ordered).2

def parity (f : Finset Variable) (a : Assignment) : Bool :=
  decide (Odd (f.filter (fun v => a v = true)).card)

theorem parity_insert (a : Assignment) (f : Finset Variable) (v : Variable)
    (fresh : v ∉ f) : parity (insert v f) a = (a v ^^ parity f a) := by
  cases hv : a v
  · simp [parity, Finset.filter_insert, hv]
  · simp [parity, Finset.filter_insert, hv, Finset.card_insert_of_notMem,
      (show v ∉ f.filter (fun v => a v = true) from fun hm => fresh (Finset.mem_of_mem_filter v hm)),
      Nat.odd_add_one]
    let n := (f.filter (fun v => a v = true)).card
    change decide (Even n) = !decide (Odd n)
    by_cases ho : Odd n
    · have he : ¬ Even n := fun h => (Nat.not_odd_iff_even.mpr h) ho
      simp [ho, he]
    · have he : Even n := Nat.not_odd_iff_even.mp ho
      simp [ho, he]

theorem parity_xor (f : Finset Variable) (a b : Assignment) :
    parity f (fun v => a v ^^ b v) = (parity f a ^^ parity f b) := by
  classical
  induction f using Finset.induction_on with
  | empty => simp [parity]
  | insert v f fresh ih =>
    rw [parity_insert _ _ _ fresh, parity_insert _ _ _ fresh, parity_insert _ _ _ fresh, ih]
    cases a v <;> cases b v <;> cases parity f a <;> cases parity f b <;> rfl

theorem allIn_follows (c : Collision) (f : Finset Variable) (b : Bool)
    (agrees : ∀ r : Fin 3, parity f (sample c r) = b) :
    parity f (allIn c.hole) = b := by
  have eq : (fun v => sample c 0 v ^^ (sample c 1 v ^^ sample c 2 v)) = allIn c.hole :=
    funext (sample_bits_xor c)
  rw [← eq, parity_xor, parity_xor, agrees 0, agrees 1, agrees 2]
  cases b <;> rfl

theorem bit_constant (c : Collision) (v : Variable) (b : Bool)
    (agrees : ∀ r : Fin 3, sample c r v = b) : (v.1 = c.left ∨ v.1 = c.right) ∧
      b = allIn c.hole v := by
  have eq := sample_bits_xor c v
  rw [agrees 0, agrees 1, agrees 2] at eq
  have value : b = allIn c.hole v := by cases b <;> simpa using eq
  exact ⟨(bit_geometry c.left c.right c.hole v.1 v.2 c.ordered).1.mp
    (fun r => (agrees r).trans value), value⟩

end Pcx130

namespace Pcx130

def Collision.support (c : Collision) : Finset Variable :=
  Finset.univ.filter (fun v => v.1 = c.left ∨ v.1 = c.right)

theorem support_size (c : Collision) : c.support.card = 4 := by
  have finite : ∀ i j : Fin 5, i < j →
      (Finset.univ.filter (fun v : Variable => v.1 = i ∨ v.1 = j)).card = 4 := by
    decide +kernel
  exact finite c.left c.right c.ordered

def commonSet (i j p q : Fin 5) (h k : Fin 4) : Finset Variable :=
  Finset.univ.filter (fun v =>
    (v.1 = i ∨ v.1 = j) ∧ (v.1 = p ∨ v.1 = q) ∧ allIn h v = allIn k v)

theorem commonSet_card : ∀ (i j p q : Fin 5) (h k : Fin 4), h ≠ k →
    (commonSet i j p q h k).card ≤ 2 := by
  decide +kernel

theorem three_holes_vary : ∀ (h k l : Fin 4) (d : Fin 2), h ≠ k → h ≠ l → k ≠ l →
    ¬ (h.val.testBit d.val = k.val.testBit d.val ∧ h.val.testBit d.val = l.val.testBit d.val) := by
  decide +kernel

theorem parity_singleton (v : Variable) (a : Assignment) : parity {v} a = a v := by
  cases hv : a v <;> simp [parity, Finset.filter_singleton, hv]

end Pcx130

namespace Pcx130

inductive TestTree where
  | ax (c : Collision)
  | exit
  | split (form : Finset Variable) (left right : TestTree)

namespace TestTree

def marks : TestTree → List Collision
  | .ax c => [c]
  | .exit => []
  | .split _ l r => l.marks ++ r.marks

def exits : TestTree → ℕ
  | .ax _ => 0
  | .exit => 1
  | .split _ l r => l.exits + r.exits

def grant (known f : Finset Variable) : Finset Variable :=
  if f.card = 1 then known ∪ f else known

def Shared (cs : List Collision) (known : Finset Variable) : Prop :=
  ∀ v ∈ known, ∃ b : Bool, ∀ c ∈ cs, ∀ r : Fin 3, sample c r v = b

def Route (b : Bool) (f : Finset Variable) (cs : List Collision) : Prop :=
  ∀ c ∈ cs, ∀ r : Fin 3, parity f (sample c r) = b

def Valid : TestTree → Finset Variable → Prop
  | .ax c, known => c.support ⊆ known
  | .exit, _ => True
  | .split f l r, known =>
    Route false f l.marks ∧ Route true f r.marks ∧
      l.Valid (grant known f) ∧ r.Valid (grant known f)

def Routed : TestTree → Prop
  | .ax _ => True
  | .exit => True
  | .split f l r =>
    Route false f l.marks ∧ Route true f r.marks ∧ l.Routed ∧ r.Routed

theorem valid_routed {t : TestTree} {known : Finset Variable} (valid : t.Valid known) :
    t.Routed := by
  induction t generalizing known with
  | ax => trivial
  | exit => trivial
  | split f l r ihl ihr =>
    obtain ⟨takesLeft, takesRight, validLeft, validRight⟩ := valid
    exact ⟨takesLeft, takesRight, ihl validLeft, ihr validRight⟩

theorem routed_holes {t : TestTree} (routed : t.Routed) :
    (t.marks.map Collision.hole).Nodup := by
  induction t with
  | ax => simp [marks]
  | exit => simp [marks]
  | split f l r ihl ihr =>
    obtain ⟨takesLeft, takesRight, routeLeft, routeRight⟩ := routed
    rw [marks, List.map_append, List.nodup_append']
    refine ⟨ihl routeLeft, ihr routeRight, ?_⟩
    intro h hl hr
    obtain ⟨c, hc, eqc⟩ := List.mem_map.mp hl
    obtain ⟨d, hd, eqd⟩ := List.mem_map.mp hr
    have even := allIn_follows c f false (takesLeft c hc)
    have odd := allIn_follows d f true (takesRight d hd)
    rw [eqc, ← eqd, odd] at even
    cases even

theorem mark_holes {t : TestTree} {known : Finset Variable} (valid : t.Valid known) :
    (t.marks.map Collision.hole).Nodup :=
  routed_holes (valid_routed valid)

theorem grant_size (known f : Finset Variable) :
    (grant known f).card ≤ known.card + 1 := by
  unfold grant
  split
  · next h => exact (Finset.card_union_le _ _).trans (by omega)
  · omega

theorem shared_grant {cs : List Collision} {known f : Finset Variable} {b : Bool}
    (shared : Shared cs known) (route : Route b f cs) :
    Shared cs (grant known f) := by
  intro v hv
  unfold grant at hv
  split at hv
  · next h =>
    rcases Finset.mem_union.mp hv with hk | hf
    · exact shared v hk
    · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h
      have eq : v = w := Finset.mem_singleton.mp hf
      subst w
      exact ⟨b, fun c hc p => (parity_singleton v (sample c p)).symm.trans (route c hc p)⟩
  · exact shared v hv

theorem shared_pair {cs : List Collision} {known : Finset Variable}
    (nodup : (cs.map Collision.hole).Nodup) (enough : 2 ≤ cs.length)
    (shared : Shared cs known) : known.card ≤ 2 := by
  rcases cs with _ | ⟨c, _ | ⟨d, rest⟩⟩
  · simp at enough
  · simp at enough
  · have distinct : c.hole ≠ d.hole := by
      intro eq
      have absent := (List.nodup_cons.mp nodup).1
      exact absent (by simp [eq])
    apply (Finset.card_le_card ?_).trans (commonSet_card c.left c.right d.left d.right c.hole d.hole distinct)
    intro v hv
    obtain ⟨b, agree⟩ := shared v hv
    have hc := bit_constant c v b (agree c (by simp))
    have hd := bit_constant d v b (agree d (by simp))
    simpa [commonSet] using And.intro hc.1 (And.intro hd.1 (hc.2.symm.trans hd.2))

theorem shared_three {cs : List Collision} {known : Finset Variable}
    (nodup : (cs.map Collision.hole).Nodup) (enough : 3 ≤ cs.length)
    (shared : Shared cs known) : known.card = 0 := by
  rcases cs with _ | ⟨c, _ | ⟨d, _ | ⟨g, rest⟩⟩⟩
  · simp at enough
  · simp at enough
  · simp at enough
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro v hv
    obtain ⟨b, agree⟩ := shared v hv
    have hc := bit_constant c v b (agree c (by simp))
    have hd := bit_constant d v b (agree d (by simp))
    have hg := bit_constant g v b (agree g (by simp))
    have first := List.nodup_cons.mp nodup
    have second := List.nodup_cons.mp first.2
    apply three_holes_vary c.hole d.hole g.hole v.2
    · intro eq
      exact first.1 (by simp [eq])
    · intro eq
      exact first.1 (by simp [eq])
    · intro eq
      exact second.1 (by simp [eq])
    · exact ⟨hc.2.symm.trans hd.2, hc.2.symm.trans hg.2⟩

private theorem arithmetic (k₀ k₁ e₀ e₁ d d' : ℕ)
    (increase : d' ≤ d + 1)
    (pairCredit : 2 ≤ k₀ + k₁ → d ≤ 2)
    (tripleCredit : 3 ≤ k₀ + k₁ → d = 0)
    (leftEmpty : k₀ = 0 → 1 ≤ e₀) (rightEmpty : k₁ = 0 → 1 ≤ e₁)
    (leftSmall : k₀ = 1 ∨ k₀ = 2 → 4 ≤ e₀ + d')
    (rightSmall : k₁ = 1 ∨ k₁ = 2 → 4 ≤ e₁ + d')
    (leftBig : 3 ≤ k₀ → 6 ≤ e₀) (rightBig : 3 ≤ k₁ → 6 ≤ e₁) :
    (k₀ + k₁ = 0 → 1 ≤ e₀ + e₁) ∧
    (k₀ + k₁ = 1 ∨ k₀ + k₁ = 2 → 4 ≤ e₀ + e₁ + d) ∧
    (3 ≤ k₀ + k₁ → 6 ≤ e₀ + e₁) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have l := leftEmpty (by omega)
    omega
  · intro h
    by_cases l : k₀ = 0
    · have e := leftEmpty l
      have r := rightSmall (by omega)
      omega
    by_cases r : k₁ = 0
    · have e := rightEmpty r
      have l' := leftSmall (by omega)
      omega
    have dl := leftSmall (by omega)
    have dr := rightSmall (by omega)
    have dh := pairCredit (by omega)
    omega
  · intro h
    by_cases l : 3 ≤ k₀
    · have e := leftBig l
      omega
    by_cases r : 3 ≤ k₁
    · have e := rightBig r
      omega
    have dh := tripleCredit h
    have dl := leftSmall (by omega)
    have dr := rightSmall (by omega)
    omega

theorem exits_lower_aux (t : TestTree) {known : Finset Variable}
    (valid : t.Valid known) (shared : Shared t.marks known) :
    (t.marks.length = 0 → 1 ≤ t.exits) ∧
    (t.marks.length = 1 ∨ t.marks.length = 2 → 4 ≤ t.exits + known.card) ∧
    (3 ≤ t.marks.length → 6 ≤ t.exits) := by
  induction t generalizing known with
  | exit => simp [marks, exits]
  | ax c =>
    have enough := Finset.card_le_card (show c.support ⊆ known from valid)
    rw [support_size] at enough
    simpa [marks, exits] using enough
  | split f l r ihl ihr =>
    obtain ⟨takesLeft, takesRight, validLeft, validRight⟩ := valid
    have knownLeft : Shared l.marks known := by
      intro v hv
      obtain ⟨b, agrees⟩ := shared v hv
      exact ⟨b, fun c hc => agrees c (List.mem_append_left _ hc)⟩
    have knownRight : Shared r.marks known := by
      intro v hv
      obtain ⟨b, agrees⟩ := shared v hv
      exact ⟨b, fun c hc => agrees c (List.mem_append_right _ hc)⟩
    obtain ⟨l₀, l₁, l₂⟩ := ihl validLeft (shared_grant knownLeft takesLeft)
    obtain ⟨r₀, r₁, r₂⟩ := ihr validRight (shared_grant knownRight takesRight)
    have nodup := mark_holes (t := .split f l r) (known := known)
      ⟨takesLeft, takesRight, validLeft, validRight⟩
    have pairCredit (h : 2 ≤ l.marks.length + r.marks.length) : known.card ≤ 2 :=
      shared_pair nodup (by simpa [marks] using h) shared
    have tripleCredit (h : 3 ≤ l.marks.length + r.marks.length) : known.card = 0 :=
      shared_three nodup (by simpa [marks] using h) shared
    simpa [marks, exits] using
      arithmetic l.marks.length r.marks.length l.exits r.exits known.card (grant known f).card
        (grant_size known f) pairCredit tripleCredit l₀ r₀ l₁ r₁ l₂ r₂

theorem marks_at_most_four (t : TestTree) (routed : t.Routed) :
    t.marks.length ≤ 4 := by
  classical
  have nd := routed_holes routed
  have h := (Finset.card_le_univ ((t.marks.map Collision.hole).toFinset))
  rw [List.toFinset_card_of_nodup nd, List.length_map, Fintype.card_fin] at h
  exact h

theorem pure_exit_bound (t : TestTree) {known : Finset Variable}
    (valid : t.Valid known) (shared : Shared t.marks known) :
    2 * t.marks.length ≤ t.exits + 2 := by
  obtain ⟨_, small, large⟩ := exits_lower_aux t valid shared
  have max := marks_at_most_four t (valid_routed valid)
  by_cases h : t.marks.length ≤ 1
  · omega
  by_cases h' : t.marks.length = 2
  · have fits := shared_pair (mark_holes valid) (by omega) shared
    have bound := small (Or.inr h')
    omega
  · have bound := large (by omega)
    omega

end TestTree

end Pcx130

namespace Pcx130

open PEqualNP.ProofComplexity

def bits (h : Fin 4) : Fin 2 → Bool := fun b => h.val.testBit b.val

def holeOf (a : Fin 2 → Bool) : Fin 4 :=
  if a 1 then (if a 0 then 3 else 2) else (if a 0 then 1 else 0)

theorem bits_hole (a : Fin 2 → Bool) : bits (holeOf a) = a := by
  funext b
  cases h0 : a 0 <;> cases h1 : a 1 <;> fin_cases b <;> simp [holeOf, bits, h0, h1] <;> rfl

theorem hole_bits : ∀ h : Fin 4, holeOf (bits h) = h := by decide +kernel

theorem bits_injective : Function.Injective bits := by
  intro h k eq
  rw [← hole_bits h, ← hole_bits k, eq]

def pairClause (i j : Fin 5) (a : Fin 2 → Bool) : Clause Variable :=
  Finset.univ.image (fun b : Fin 2 => ((i, b), !a b)) ∪
    Finset.univ.image (fun b : Fin 2 => ((j, b), !a b))

def Collision.clause (c : Collision) : LinClause Variable :=
  linOfClause (pairClause c.left c.right (bits c.hole))

abbrev Formula := (fun C => linOfClause C) '' BPHP 5 2

theorem Collision.mem_formula (c : Collision) : c.clause ∈ Formula := by
  exact ⟨pairClause c.left c.right (bits c.hole), ⟨c.left, c.right, bits c.hole, c.ordered.ne, rfl⟩, rfl⟩

theorem clause_key {D : LinClause Variable} (mem : D ∈ Formula) :
    ∃ c : Collision, D = c.clause := by
  obtain ⟨D0, ⟨i,j,a,hne,rfl⟩, rfl⟩ := mem
  rcases lt_or_gt_of_ne hne with forward | backward
  · exact ⟨⟨i,j,holeOf a,forward⟩, by simp [Collision.clause, pairClause, bits_hole]⟩
  · exact ⟨⟨j,i,holeOf a,backward⟩, by simp [Collision.clause, pairClause, bits_hole, Finset.union_comm]⟩

private theorem clause_iff (v : Variable) (s : Bool) (a : Assignment) :
    LinEqSat a ({v}, s) ↔ a v = s := by
  cases hv : a v <;> cases s <;> simp [LinEqSat, Finset.filter_singleton, hv]

theorem falsifies_pair_iff (i j : Fin 5) (b : Fin 2 → Bool) (a : Assignment) :
    ¬ LinClauseSat a (linOfClause (pairClause i j b)) ↔
      (∀ q, a (i,q) = b q) ∧ (∀ q, a (j,q) = b q) := by
  have eval : LinClauseSat a (linOfClause (pairClause i j b)) ↔
      (∃ q, a (i,q) = !(b q)) ∨ (∃ q, a (j,q) = !(b q)) := by
    unfold LinClauseSat linOfClause pairClause
    simp only [Finset.mem_image, Finset.mem_union, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, ⟨_, (⟨q, rfl⟩ | ⟨q, rfl⟩), rfl⟩, sat⟩
      · exact Or.inl ⟨q, (clause_iff _ _ _).mp sat⟩
      · exact Or.inr ⟨q, (clause_iff _ _ _).mp sat⟩
    · rintro (⟨q, e⟩ | ⟨q,e⟩)
      · exact ⟨_, ⟨_, Or.inl ⟨q,rfl⟩, rfl⟩, (clause_iff _ _ _).mpr e⟩
      · exact ⟨_, ⟨_, Or.inr ⟨q,rfl⟩, rfl⟩, (clause_iff _ _ _).mpr e⟩
  rw [eval]
  constructor
  · intro hn
    refine ⟨fun q => ?_, fun q => ?_⟩
    · have no : a (i,q) ≠ !(b q) := fun e => hn (Or.inl ⟨q,e⟩)
      cases hv : a (i,q) <;> cases hb : b q <;> simp_all
    · have no : a (j,q) ≠ !(b q) := fun e => hn (Or.inr ⟨q,e⟩)
      cases hv : a (j,q) <;> cases hb : b q <;> simp_all
  · rintro ⟨l,r⟩ (⟨q,e⟩ | ⟨q,e⟩)
    · have eq := l q
      rw [eq] at e
      cases h : b q <;> simp [h] at e
    · have eq := r q
      rw [eq] at e
      cases h : b q <;> simp [h] at e

theorem sample_falsifies (c : Collision) (r : Fin 3) :
    ¬ LinClauseSat (sample c r) c.clause := by
  have h := sample_hole_facts c.left c.right c.hole r c.ordered
  exact (falsifies_pair_iff _ _ _ _).mpr
    ⟨fun q => by simp [sample, bits, h.1], fun q => by simp [sample, bits, h.2.1]⟩

theorem unique_collision (c d : Collision) (r : Fin 3)
    (falsified : ¬ LinClauseSat (sample c r) d.clause) : c = d := by
  obtain ⟨l,r'⟩ := (falsifies_pair_iff _ _ _ _).mp falsified
  have lh : sampleHole c.left c.right c.hole r d.left = d.hole :=
    bits_injective (funext l)
  have rh : sampleHole c.left c.right c.hole r d.right = d.hole :=
    bits_injective (funext r')
  have samples := sample_hole_facts c.left c.right c.hole r c.ordered
  obtain ⟨leftEq,rightEq⟩ := (samples.2.2 d.left d.right d.ordered).mp (lh.trans rh.symm)
  have holeEq : c.hole = d.hole := by rw [leftEq, samples.1] at lh; exact lh
  cases c; cases d; simp_all

theorem sample_only_axiom (c : Collision) (r : Fin 3) {D : LinClause Variable}
    (mem : D ∈ Formula) (falsified : ¬ LinClauseSat (sample c r) D) : D = c.clause := by
  obtain ⟨d, rfl⟩ := clause_key mem
  rw [← unique_collision c d r falsified]

theorem clause_injective : Function.Injective Collision.clause := by
  intro c d same
  exact unique_collision c d 0 (same ▸ sample_falsifies c 0)

end Pcx130

namespace Pcx130

open PEqualNP.ProofComplexity

abbrev CollisionData := { t : Fin 5 × Fin 5 × Fin 4 // t.1 < t.2.1 }

def collisionEquiv : Collision ≃ CollisionData where
  toFun c := ⟨⟨c.left,c.right,c.hole⟩,c.ordered⟩
  invFun t := ⟨t.val.1,t.val.2.1,t.val.2.2,t.property⟩
  left_inv := by rintro ⟨i,j,h,p⟩; rfl
  right_inv := by rintro ⟨⟨i,j,h⟩,p⟩; rfl

instance : Fintype Collision := Fintype.ofEquiv CollisionData collisionEquiv.symm

theorem collision_count : Fintype.card Collision = 40 :=
  (Fintype.card_congr collisionEquiv).trans (by decide +kernel)

theorem Collision.support_has_atom (c : Collision) {v : Variable} (mem : v ∈ c.support) :
    ({v}, !allIn c.hole v) ∈ c.clause := by
  have sides : v.1 = c.left ∨ v.1 = c.right := by simpa [Collision.support] using mem
  rcases v with ⟨i,b⟩
  rcases sides with e | e
  · change i = c.left at e
    subst i
    exact Finset.mem_image.mpr ⟨_, Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩), rfl⟩
  · change i = c.right at e
    subst i
    exact Finset.mem_image.mpr ⟨_, Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩), rfl⟩

theorem Collision.atoms_are_singleton (c : Collision) {q : LinEq Variable} (mem : q ∈ c.clause) :
    q.1.card = 1 := by
  obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp mem
  simp

end Pcx130

namespace Pcx130

open PEqualNP.ProofComplexity

def singletonVars (C : LinClause Variable) : Finset Variable :=
  Finset.univ.filter (fun v => ∃ b : Bool, ({v}, b) ∈ C)

theorem mem_singletonVars (C : LinClause Variable) (v : Variable) :
    v ∈ singletonVars C ↔ ∃ b : Bool, ({v}, b) ∈ C := by
  simp [singletonVars]

theorem support_subset_singletons (c : Collision) : c.support ⊆ singletonVars c.clause := by
  intro v mem
  exact (mem_singletonVars _ _).mpr ⟨_, c.support_has_atom mem⟩

theorem shared_from_clause (C : LinClause Variable) (cs : List Collision)
    (bad : ∀ c ∈ cs, ∀ r : Fin 3, ¬ LinClauseSat (sample c r) C) :
      TestTree.Shared cs (singletonVars C) := by
  intro v hv
  obtain ⟨b, hb⟩ := (mem_singletonVars _ _).mp hv
  refine ⟨!b, fun c hc p => ?_⟩
  have diff : sample c p v ≠ b := fun h =>
    bad c hc p ⟨({v}, b), hb, (clause_iff _ _ _).mpr h⟩
  cases hv : sample c p v <;> cases b <;> simp_all

theorem grant_old {known f : Finset Variable} : known ⊆ TestTree.grant known f := by
  unfold TestTree.grant
  split
  · exact Finset.subset_union_left
  · exact Finset.Subset.refl _

theorem grant_test {known f : Finset Variable} (h : f.card = 1) :
    f ⊆ TestTree.grant known f := by
  simpa [TestTree.grant, h] using (Finset.subset_union_right (s₁ := known) (s₂ := f))

theorem carry_singletons {C D R : LinClause Variable} {f known : Finset Variable}
    (resolve : R = C.erase (f, false) ∪ D.erase (f, true))
    (knownEnough : singletonVars R ⊆ known) :
    singletonVars C ⊆ TestTree.grant known f ∧ singletonVars D ⊆ TestTree.grant known f := by
  constructor <;> intro v hv <;> obtain ⟨b, hb⟩ := (mem_singletonVars _ _).mp hv
  · by_cases eq : ({v} : Finset Variable) = f
    · subst f
      exact grant_test (by simp) (Finset.mem_singleton_self _)
    · have persists : ({v}, b) ∈ R := resolve ▸ Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨fun h => eq (congrArg Prod.fst h), hb⟩)
      exact grant_old (knownEnough ((mem_singletonVars _ _).mpr ⟨_, persists⟩))
  · by_cases eq : ({v} : Finset Variable) = f
    · subst f
      exact grant_test (by simp) (Finset.mem_singleton_self _)
    · have persists : ({v}, b) ∈ R := resolve ▸ Finset.mem_union_right _
        (Finset.mem_erase.mpr ⟨fun h => eq (congrArg Prod.fst h), hb⟩)
      exact grant_old (knownEnough ((mem_singletonVars _ _).mpr ⟨_, persists⟩))

end Pcx130

namespace Pcx130.TestTree

open PEqualNP.ProofComplexity

inductive Certified : TestTree → LinClause Variable → Prop
  | ax (c : Collision) : Certified (.ax c) c.clause
  | exit (C : LinClause Variable) : Certified .exit C
  | split {l r : TestTree} {L R C : LinClause Variable} (f : Finset Variable)
      (left : Certified l L) (right : Certified r R)
      (res : C = R.erase (f,false) ∪ L.erase (f,true)) : Certified (.split f l r) C

theorem valid_of_certified {t : TestTree} {C : LinClause Variable} {known : Finset Variable}
    (cert : Certified t C) (routed : t.Routed) (init : singletonVars C ⊆ known) :
    t.Valid known := by
  induction cert generalizing known with
  | ax c => exact (support_subset_singletons c).trans init
  | exit => trivial
  | split f _ _ resolvent ihl ihr =>
    obtain ⟨takesLeft, takesRight, routeLeft, routeRight⟩ := routed
    obtain ⟨keepRight, keepLeft⟩ := carry_singletons resolvent init
    exact ⟨takesLeft, takesRight, ihl routeLeft keepLeft, ihr routeRight keepRight⟩

theorem cost_of_certified {t : TestTree} {C : LinClause Variable}
    (cert : Certified t C) (routed : t.Routed)
    (bad : ∀ c ∈ t.marks, ∀ r : Fin 3, ¬ LinClauseSat (sample c r) C) :
    2 * t.marks.length ≤ t.exits + 2 :=
  pure_exit_bound t (valid_of_certified cert routed (Finset.Subset.refl _))
    (shared_from_clause C t.marks bad)

end Pcx130.TestTree

namespace Pcx130

theorem tight_accounting
    (components mergeExcess weakenings weakComponents exitEdges weakExits : ℕ)
    (enoughComponents : 40 ≤ 4 * components)
    (connected : components ≤ mergeExcess + 1)
    (budget : mergeExcess + weakenings ≤ 16)
    (weakCount : weakComponents ≤ weakenings)
    (edgeCount : exitEdges + 1 = components + mergeExcess)
    (pureCost : 80 + weakExits ≤ exitEdges + 6 * weakComponents + 2 * components) :
    components = 10 ∧ mergeExcess = 9 ∧ weakenings = 7 ∧
      weakComponents = 7 ∧ exitEdges = 18 ∧ weakExits = 0 := by
  omega

theorem pair_exit_cost {fixed shared before left right : ℕ}
    (common : shared ≤ 2)
    (initial : fixed ≤ shared)
    (prefixCost : shared ≤ before + fixed)
    (leftNeeded : 3 ≤ shared + left)
    (rightNeeded : 3 ≤ shared + right) :
    4 ≤ before + left + right + fixed := by
  omega

theorem pure_exit_cost {k e : ℕ} (cap : k ≤ 4)
    (pair : k = 2 → 2 ≤ e)
    (triple : k = 3 → 6 ≤ e)
    (quad : k = 4 → 6 ≤ e) :
    2 * k ≤ e + 2 := by
  omega

theorem no_small_proof
    (components mergeExcess weakenings weakComponents exitEdges weakExits : ℕ)
    (enoughComponents : 40 ≤ 4 * components)
    (connected : components ≤ mergeExcess + 1)
    (edgeCount : exitEdges + 1 = components + mergeExcess)
    (weakCount : weakComponents ≤ weakenings)
    (pureCost : 80 + weakExits ≤ exitEdges + 6 * weakComponents + 2 * components)
    (sinks : exitEdges = 18 → weakExits = 0 → components = 10 →
        weakComponents = 7 → 2 * weakComponents ≤ weakenings) :
    17 ≤ mergeExcess + weakenings := by
  by_contra cap
  have tight := tight_accounting components mergeExcess weakenings weakComponents exitEdges
    weakExits enoughComponents connected (by omega) weakCount edgeCount pureCost
  obtain ⟨cc, mm, ww, wc, ee, we⟩ := tight
  have extra := sinks ee we cc wc
  omega

end Pcx130

namespace PNP130Dag.ShortestDag

open PEqualNP.ProofComplexity Pcx130

variable (d : ShortestDag Formula)

noncomputable def keyAt (i : Fin d.pi.length) : Collision :=
  if h : d.children i = [] then Classical.choose (clause_key (d.axiom_of_no_children i h))
  else ⟨0, 1, 0, by decide⟩

theorem keyAt_clause {i : Fin d.pi.length} (hi : d.children i = []) :
    (d.keyAt i).clause = d.pi.get i := by
  rw [keyAt, dite_eq_left hi]
  exact (Classical.choose_spec (clause_key (d.axiom_of_no_children i hi))).symm

theorem keyAt_injective {i j : Fin d.pi.length} (hi : d.children i = [])
    (hj : d.children j = []) (same : d.keyAt i = d.keyAt j) : i = j := by
  apply d.nodup.injective_get
  rw [← d.keyAt_clause hi, ← d.keyAt_clause hj, same]

theorem keyAt_surjective (c : Collision) : ∃ i : Fin d.pi.length,
    d.children i = [] ∧ d.keyAt i = c := by
  obtain ⟨i, _, hi, bad⟩ := d.active_initial_clause (sample c 0)
  refine ⟨i, hi, clause_injective ?_⟩
  rw [d.keyAt_clause hi]
  exact sample_only_axiom c 0 (d.axiom_of_no_children i hi) bad

noncomputable def axiomKeyEquiv : d.AxiomIndex ≃ Collision :=
  Equiv.ofBijective (fun i => d.keyAt i.val) ⟨by
    intro i j eq
    exact Subtype.ext (d.keyAt_injective i.property j.property eq), by
    intro c
    obtain ⟨i,h,e⟩ := d.keyAt_surjective c
    exact ⟨⟨i,h⟩,e⟩⟩

theorem axiom_count : (Finset.univ.filter (fun i => (d.children i).length = 0)).card = 40 := by
  classical
  let s : Finset (Fin d.pi.length) := Finset.univ.filter (fun i => (d.children i).length = 0)
  let equiv : (↑s : Type) ≃ d.AxiomIndex :=
    { toFun := fun i => ⟨i.val, List.length_eq_zero_iff.mp ((Finset.mem_filter.mp i.property).2)⟩
      invFun := fun i => ⟨i.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [i.property]⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let : Fintype d.AxiomIndex := Fintype.ofEquiv (↑s : Type) equiv
  calc
    s.card = Fintype.card (↑s : Type) := (Fintype.card_coe s).symm
    _ = Fintype.card Collision := Fintype.card_congr (equiv.trans d.axiomKeyEquiv)
    _ = 40 := collision_count

noncomputable def actualTree : LocalTree Variable (Fin d.pi.length) → TestTree
  | .ax i => .ax (d.keyAt i)
  | .exit _ => .exit
  | .weak _ t => actualTree t
  | .res _ f l r => .split f (actualTree r) (actualTree l)

theorem mark_route (t : LocalTree Variable (Fin d.pi.length)) {c : Collision}
    (mem : c ∈ (d.actualTree t).marks) :
    ∃ j qs, LocalTree.Route t j qs ∧ d.keyAt j = c := by
  induction t with
  | ax i =>
    simp [actualTree, TestTree.marks] at mem
    exact ⟨i, [], .ax i, mem.symm⟩
  | exit => simp [actualTree, TestTree.marks] at mem
  | weak _ t ih =>
    obtain ⟨j,qs,rt,eq⟩ := ih mem
    exact ⟨j, none :: qs, .weak rt, eq⟩
  | res _ f l r ihl ihr =>
    change c ∈ (d.actualTree r).marks ++ (d.actualTree l).marks at mem
    rcases List.mem_append.mp mem with hr | hl
    · obtain ⟨j,qs,rt,eq⟩ := ihr hr
      exact ⟨j, some (f,false) :: qs, .right rt, eq⟩
    · obtain ⟨j,qs,rt,eq⟩ := ihl hl
      exact ⟨j, some (f,true) :: qs, .left rt, eq⟩

theorem route_mark {t : LocalTree Variable (Fin d.pi.length)} {i : Fin d.pi.length} {qs}
    (route : LocalTree.Route t i qs) : d.keyAt i ∈ (d.actualTree t).marks := by
  induction route with
  | ax => simp [actualTree, TestTree.marks]
  | weak _ ih => exact ih
  | left _ ih => exact List.mem_append_right _ ih
  | right _ ih => exact List.mem_append_left _ ih

theorem actualTree_routed (t : LocalTree Variable (Fin d.pi.length))
    (phases : ∀ j qs, LocalTree.Route t j qs → ∀ r : Fin 3, ∀ q ∈ qs,
      Accepts (sample (d.keyAt j) r) q) : (d.actualTree t).Routed := by
  induction t with
  | ax => trivial
  | exit => trivial
  | weak _ t ih =>
    exact ih (fun j qs route r q hq => phases j (none :: qs) (.weak route) r q (List.mem_cons_of_mem _ hq))
  | res _ f l r ihl ihr =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c hc phase
      obtain ⟨j,qs,route,rfl⟩ := d.mark_route r hc
      exact phases j _ (.right route) phase _ (List.mem_cons_self)
    · intro c hc phase
      obtain ⟨j,qs,route,rfl⟩ := d.mark_route l hc
      exact phases j _ (.left route) phase _ (List.mem_cons_self)
    · exact ihr (fun j qs route r q hq => phases j (some (f,false) :: qs) (.right route) r q (List.mem_cons_of_mem _ hq))
    · exact ihl (fun j qs route r q hq => phases j (some (f,true) :: qs) (.left route) r q (List.mem_cons_of_mem _ hq))

theorem marked_sample_route {i j : Fin d.pi.length} {qs}
    (route : LocalTree.Route (d.unroll i) j qs) (r : Fin 3) :
    ¬ LinClauseSat (sample (d.keyAt j) r) (d.pi.get i) ∧
      ∀ q ∈ qs, Accepts (sample (d.keyAt j) r) q := by
  refine d.unroll_route_active _ route (fun C hC bad => ?_)
  rw [← d.keyAt_clause (d.route_of_unroll route).2]
  exact sample_only_axiom _ _ hC bad

theorem actual_unroll_routed (i : Fin d.pi.length) :
    (d.actualTree (d.unroll i)).Routed :=
  d.actualTree_routed _ (fun _ _ route r => (d.marked_sample_route route r).2)

theorem actual_unroll_false (i : Fin d.pi.length) :
    ∀ c ∈ (d.actualTree (d.unroll i)).marks, ∀ r : Fin 3,
      ¬ LinClauseSat (sample c r) (d.pi.get i) := by
  intro c hc r
  obtain ⟨j,qs,route,rfl⟩ := d.mark_route (d.unroll i) hc
  exact (d.marked_sample_route route r).1

end PNP130Dag.ShortestDag

namespace PNP130Dag.LocalTree

variable {V I : Type}

def WeakFree : LocalTree V I → Prop
  | .ax _ => True
  | .exit _ => True
  | .weak _ _ => False
  | .res _ _ l r => l.WeakFree ∧ r.WeakFree

end PNP130Dag.LocalTree

namespace PNP130Dag.ShortestDag

open PEqualNP.ProofComplexity Pcx130

variable (d : ShortestDag Formula)

theorem actual_unroll_certified (i : Fin d.pi.length) (pure : (d.unroll i).WeakFree) :
    (d.actualTree (d.unroll i)).Certified (d.pi.get i) := by
  have aux (n : ℕ) : ∀ i : Fin d.pi.length, d.pi.length - i.val = n →
      (d.unroll i).WeakFree → (d.actualTree (d.unroll i)).Certified (d.pi.get i) := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro i hlen pure
      have sub (k : Fin d.pi.length) (lt : i < k) (hpure : (d.cutChild k).WeakFree) :
          (d.actualTree (d.cutChild k)).Certified (d.pi.get k) := by
        by_cases h : d.incoming k = 1
        · rw [cutChild, if_pos h] at hpure ⊢
          have hk : k.val < d.pi.length := k.isLt
          have hlt : i.val < k.val := lt
          exact ih _ (by omega) k rfl hpure
        · rw [cutChild, if_neg h, actualTree]
          exact .exit _
      cases hr : d.rules i with
      | ax ha =>
        rw [d.unroll_ax hr, actualTree]
        have hi : d.children i = [] := by simp [children, hr, Rule.parents]
        rw [← d.keyAt_clause hi]
        exact .ax _
      | weak j hj hw =>
        rw [d.unroll_weak hr] at pure
        exact False.elim pure
      | res j k hj hk hres =>
        rw [d.unroll_res hr] at pure ⊢
        have hv : (d.cutChild j).WeakFree ∧ (d.cutChild k).WeakFree := pure
        exact .split _ (sub k hk hv.2) (sub j hj hv.1) (Classical.choose_spec hres).2.2
  exact aux _ i rfl pure

theorem actual_unroll_at_most_four (i : Fin d.pi.length) :
    (d.actualTree (d.unroll i)).marks.length ≤ 4 :=
  TestTree.marks_at_most_four _ (d.actual_unroll_routed i)

theorem actual_unroll_exit_bound (i : Fin d.pi.length) (pure : (d.unroll i).WeakFree) :
    2 * (d.actualTree (d.unroll i)).marks.length ≤ (d.actualTree (d.unroll i)).exits + 2 :=
  TestTree.cost_of_certified (d.actual_unroll_certified i pure) (d.actual_unroll_routed i)
    (d.actual_unroll_false i)

end PNP130Dag.ShortestDag

namespace Pcx130.Components

open Finset
open scoped BigOperators

variable {n : ℕ}

abbrev Children (n : ℕ) := Fin n → List (Fin n)

def degree (d : Children n) (v : Fin n) : ℕ := ∑ u, (d u).count v

def roots (d : Children n) : Finset (Fin n) := univ.filter fun v => degree d v ≠ 1

def excess (d : Children n) : ℕ := ∑ v, (degree d v - 1)

def exitsAt (d : Children n) (v : Fin n) : ℕ :=
  ((d v).filter fun w => decide (2 ≤ degree d w)).length

def axiomNodes (d : Children n) := univ.filter fun v => (d v).length = 0

def weakNodes (d : Children n) := univ.filter fun v => (d v).length = 1

theorem count_all [Fintype α] [DecidableEq α] (l : List α) :
    (∑ v, l.count v) = l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simpa [List.count_cons, Finset.sum_add_distrib] using ih

theorem sum_degrees (d : Children n) : (∑ v, degree d v) = ∑ u, (d u).length := by
  unfold degree
  rw [Finset.sum_comm]
  simp [count_all]

theorem no_incoming_zero (d : Children n) (r : Fin n) (h0 : r.val = 0)
    (order : ∀ u v, v ∈ d u → u.val < v.val) : degree d r = 0 := by
  unfold degree
  apply Finset.sum_eq_zero
  intro u hu
  apply List.count_eq_zero_of_not_mem
  intro hr
  have lt := order u r hr
  omega

theorem degree_pos_of_parent (d : Children n) {u v : Fin n} (h : v ∈ d u) :
    0 < degree d v := by
  have hc := List.count_pos_iff.mpr h
  exact hc.trans_le (Finset.single_le_sum (s := univ) (f := fun a => (d a).count v)
    (fun a _ => Nat.zero_le _) (mem_univ u))

theorem parent_exists (d : Children n) {v : Fin n} (h : degree d v ≠ 0) :
    ∃ u, v ∈ d u := by
  by_contra! all
  apply h
  exact Finset.sum_eq_zero (fun u _ => List.count_eq_zero_of_not_mem (all u))

noncomputable def parent (d : Children n) (v : Fin n) (h : degree d v = 1) : Fin n :=
  Classical.choose (parent_exists d (v := v) (by omega))

theorem parent_mem (d : Children n) (v : Fin n) (h : degree d v = 1) : v ∈ d (parent d v h) :=
  Classical.choose_spec (parent_exists d (v := v) (by omega))

theorem equal_parents (d : Children n) {u w v : Fin n} (h : degree d v = 1)
    (hu : v ∈ d u) (hw : v ∈ d w) : u = w := by
  by_contra neq
  have hu' := List.count_pos_iff.mpr hu
  have hw' := List.count_pos_iff.mpr hw
  have hsum := Finset.add_sum_erase univ (fun i => (d i).count v) (mem_univ u)
  have hmem : w ∈ (univ : Finset (Fin n)).erase u := mem_erase.mpr ⟨Ne.symm neq,mem_univ _⟩
  have le := Finset.single_le_sum (f := fun i => (d i).count v)
    (fun i _ => Nat.zero_le _) hmem
  unfold degree at h
  omega

noncomputable def owner (d : Children n) (order : ∀ u v, v ∈ d u → u.val < v.val)
    (v : Fin n) : Fin n :=
  if h : degree d v = 1 then owner d order (parent d v h) else v
termination_by v.val
decreasing_by exact order _ _ (parent_mem d v h)

theorem owner_root (d : Children n) (order : ∀ u v, v ∈ d u → u.val < v.val)
    (v : Fin n) (hv : degree d v ≠ 1) : owner d order v = v := by
  rw [owner]
  simp [hv]

theorem owner_child (d : Children n) (order : ∀ u v, v ∈ d u → u.val < v.val)
    {u v : Fin n} (h : v ∈ d u) (hv : degree d v = 1) :
    owner d order v = owner d order u := by
  rw [owner, dif_pos hv, equal_parents d hv (parent_mem d v hv) h]

theorem owner_mem (d : Children n) (order : ∀ u v, v ∈ d u → u.val < v.val)
    (v : Fin n) : owner d order v ∈ roots d := by
  by_cases e : degree d v = 1
  · rw [owner_child d order (parent_mem d v e) e]
    exact owner_mem d order (parent d v e)
  · rw [owner_root d order v e]
    exact mem_filter.mpr ⟨mem_univ _,e⟩
termination_by v.val
decreasing_by exact order _ _ (parent_mem d v e)

theorem degree_mass (d : Children n) (r : Fin n) (hr : degree d r = 0)
    (other : ∀ v, v ≠ r → 0 < degree d v) :
    (∑ v, degree d v) + 1 = n + excess d := by
  have point (v : Fin n) :
      degree d v + (if v = r then 1 else 0) = 1 + (degree d v - 1) := by
    by_cases e : v = r
    · subst v; simp [hr]
    · have pos := other v e; simp [e]; omega
  have ans := Finset.sum_congr (s₁ := univ) rfl (fun v _ => point v)
  simpa [Finset.sum_add_distrib,excess] using ans

theorem roots_le (d : Children n) (r : Fin n) (hr : degree d r = 0)
    (other : ∀ v, v ≠ r → 0 < degree d v) : (roots d).card ≤ excess d + 1 := by
  have point (v : Fin n) : (if degree d v ≠ 1 then 1 else 0) ≤
       (degree d v - 1) + if v = r then 1 else 0 := by
    by_cases eq : v = r
    · subst v; simp [hr]
    · have pos := other v eq
      by_cases one : degree d v = 1 <;> simp [eq, one] <;> omega
  have ans := Finset.sum_le_sum (s := univ) (fun v _ => point v)
  simpa [roots,Finset.card_filter,Finset.sum_add_distrib,excess] using ans

theorem filtered_count [Fintype α] [DecidableEq α] (P : α → Prop) [DecidablePred P]
    (l : List α) : (l.filter fun a => decide (P a)).length =
      ∑ v, if P v then l.count v else 0 := by
  rw [← count_all (l.filter fun a => decide (P a))]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : P v
  · simp [h,List.count_filter (by simpa using h : decide (P v) = true)]
  · rw [if_neg h]
    apply List.count_eq_zero_of_not_mem
    simp [h]

theorem total_exits (d : Children n) : (∑ u, exitsAt d u) =
    ∑ v, if 2 ≤ degree d v then degree d v else 0 := by
  unfold exitsAt
  simp_rw [filtered_count]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  split <;> rename_i h <;> simp [h,degree]

theorem exit_mass (d : Children n) (r : Fin n) (hr : degree d r = 0)
    (other : ∀ v, v ≠ r → 0 < degree d v) :
    (∑ u, exitsAt d u) + 1 = (roots d).card + excess d := by
  rw [total_exits]
  have point (v : Fin n) :
      (if 2 ≤ degree d v then degree d v else 0) + (if v = r then 1 else 0) =
      (if degree d v ≠ 1 then 1 else 0) + (degree d v - 1) := by
    by_cases eq : v = r
    · subst v; simp [hr]
    · have pos := other v eq
      by_cases two : 2 ≤ degree d v <;> by_cases one : degree d v = 1 <;> simp [eq,two,one] <;> omega
  have ans := Finset.sum_congr (s₁ := univ) rfl (fun v _ => point v)
  simpa [Finset.sum_add_distrib,roots,Finset.card_filter,excess] using ans

theorem node_budget (d : Children n) (r : Fin n) (hr : degree d r = 0)
    (other : ∀ v, v ≠ r → 0 < degree d v) (arity : ∀ v, (d v).length ≤ 2)
    (distinctAxioms : 40 ≤ (axiomNodes d).card) (size : n ≤ 95) :
    excess d + (weakNodes d).card ≤ 16 := by
  have point (v : Fin n) : (d v).length + (if (d v).length = 1 then 1 else 0) +
       2 * (if (d v).length = 0 then 1 else 0) = 2 := by
    have h := arity v
    rcases (show (d v).length = 0 ∨ (d v).length = 1 ∨ (d v).length = 2 by omega) with e|e|e <;> simp [e]
  have sums := Finset.sum_congr (s₁ := univ) rfl (fun v _ => point v)
  have hands := degree_mass d r hr other
  rw [sum_degrees] at hands
  have shape : (∑ v, (d v).length) + (weakNodes d).card + 2 * (axiomNodes d).card = n * 2 := by
    unfold weakNodes axiomNodes
    rw [Finset.card_filter, Finset.card_filter, Finset.mul_sum]
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using sums
  omega

def keptChildren (d : Children n) (u : Fin n) : List (Fin n) :=
  (d u).filter fun v => decide (degree d v = 1)

theorem weighted_count [Fintype α] [DecidableEq α] (l : List α) (m : α → ℕ) :
    (l.map m).sum = ∑ v, l.count v * m v := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [List.count_cons, Nat.add_mul, Finset.sum_add_distrib, ih, ite_mul, Nat.add_comm]

theorem kept_mass (d : Children n) (m : Fin n → ℕ) :
    (∑ u, ((keptChildren d u).map m).sum) =
       ∑ v, if degree d v = 1 then m v else 0 := by
  simp_rw [weighted_count]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : degree d v = 1
  · have hcnt (u : Fin n) : (keptChildren d u).count v = (d u).count v :=
      List.count_filter (by simpa using h)
    simp_rw [hcnt]
    rw [← Finset.sum_mul]
    change degree d v * m v = _
    simp [h]
  · have hcnt (u : Fin n) : (keptChildren d u).count v = 0 := by
      apply List.count_eq_zero_of_not_mem
      simp [keptChildren, h]
    simp [hcnt,h]

theorem component_mass (d : Children n) (m weight : Fin n → ℕ)
    (recurrence : ∀ u, m u = weight u + ((keptChildren d u).map m).sum) :
    (∑ r ∈ roots d, m r) = ∑ u, weight u := by
  have gathered := Finset.sum_congr (s₁ := univ) rfl (fun u _ => recurrence u)
  rw [Finset.sum_add_distrib, kept_mass] at gathered
  have parts :
      (∑ r ∈ roots d, m r) + (∑ v, if degree d v = 1 then m v else 0) = ∑ v, m v := by
    rw [roots, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : degree d v = 1 <;> simp [h]
  exact Nat.add_right_cancel (parts.trans gathered)

end Pcx130.Components

namespace Pcx130.Components

open Finset
open scoped BigOperators

theorem global_bound {I : Type} [DecidableEq I] (S : Finset I) (A W E : I → ℕ)
    (s w : ℕ)
    (four : ∀ r ∈ S, A r ≤ 4)
    (forty : 40 ≤ ∑ r ∈ S, A r)
    (weakSum : (∑ r ∈ S, W r) = w)
    (edges : (∑ r ∈ S, E r) + 1 = S.card + s)
    (connected : S.card ≤ s + 1)
    (pure : ∀ r ∈ S, W r = 0 → 2 * A r ≤ E r + 2)
    (sink : ∀ r ∈ S, 3 ≤ A r → E r = 0 → W r ≠ 1) : 17 ≤ s + w := by
  classical
  let Q := S.filter fun r => 0 < W r
  let D := ∑ r ∈ S, if 0 < W r then E r else 0
  have cap : (∑ r ∈ S, A r) ≤ 4 * S.card := by
    simpa [Nat.mul_comm] using Finset.sum_le_sum (s := S) (g := fun _ => 4) four
  have ncomp : 40 ≤ 4 * S.card := forty.trans cap
  have qle : Q.card ≤ w := by
    rw [← weakSum]
    dsimp [Q]
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro r hr
    by_cases h : 0 < W r <;> simp [h] <;> omega
  have per r (hr : r ∈ S) : 2 * A r + (if 0 < W r then E r else 0)
      ≤ E r + 2 + 6 * (if 0 < W r then 1 else 0) := by
    by_cases h : 0 < W r
    · have b := four r hr
      simp [h]
      omega
    · have b := pure r hr (by omega)
      simpa [h] using b
  have cost : 80 + D ≤ (∑ r ∈ S, E r) + 6 * Q.card + 2 * S.card := by
    have sum := Finset.sum_le_sum (s := S) per
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul, Nat.cast_id] at sum
    have qc : Q.card = ∑ r ∈ S, if 0 < W r then 1 else 0 := Finset.card_filter _ S
    dsimp [D]
    rw [qc]
    omega
  apply Pcx130.no_small_proof S.card s w Q.card (∑ r ∈ S, E r) D
    ncomp connected edges qle cost
  intro _ noexit ten _
  have all4 (r : I) (hr : r ∈ S) : A r = 4 := by
    have er := Finset.add_sum_erase S A hr
    have other : (∑ t ∈ S.erase r, A t) ≤ (S.erase r).card * 4 := by
      simpa using Finset.sum_le_sum (s := S.erase r) (g := fun _ => 4)
        (fun t ht => four t (Finset.mem_of_mem_erase ht))
    have erCard := Finset.card_erase_of_mem hr
    have u := four r hr
    omega
  have allzero (r : I) (hr : r ∈ S) (hw : 0 < W r) : E r = 0 := by
    have one := Finset.single_le_sum (s := S) (f := fun r => if 0 < W r then E r else 0)
      (fun r _ => Nat.zero_le _) hr
    change (∑ r ∈ S, if 0 < W r then E r else 0) = 0 at noexit
    simp [hw,noexit] at one
    exact one
  rw [← weakSum, show Q.card = ∑ r ∈ S, if 0 < W r then 1 else 0 from Finset.card_filter _ S,
      Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  by_cases hw : 0 < W r
  · have ne := sink r hr (by rw [all4 r hr]; decide) (allzero r hr hw)
    simp [hw]
    omega
  · simp [hw]

end Pcx130.Components

namespace PNP130Dag.LocalTree

open Pcx130 PEqualNP.ProofComplexity

variable {I : Type}

def sinkExits : LocalTree Variable I → ℕ
  | .ax _ => 0
  | .exit _ => 1
  | .weak _ t => t.sinkExits
  | .res _ _ l r => l.sinkExits + r.sinkExits

def sinkWeaks : LocalTree Variable I → ℕ
  | .ax _ | .exit _ => 0
  | .weak _ t => 1 + t.sinkWeaks
  | .res _ _ l r => l.sinkWeaks + r.sinkWeaks

def sinkMarks (c : I → Collision) : LocalTree Variable I → List Collision
  | .ax j => [c j]
  | .exit _ => []
  | .weak _ t => t.sinkMarks c
  | .res _ _ l r => r.sinkMarks c ++ l.sinkMarks c

def sinkCut (c : I → Collision) : LocalTree Variable I → TestTree
  | .ax j => .ax (c j)
  | .exit _ | .weak _ _ => .exit
  | .res _ f l r => .split f (r.sinkCut c) (l.sinkCut c)

theorem cut_exits (c : I → Collision) (t : LocalTree Variable I) :
    (t.sinkCut c).exits ≤ t.sinkExits + t.sinkWeaks := by
  induction t with
  | ax | exit => simp [sinkCut, TestTree.exits, sinkExits, sinkWeaks]
  | weak => simp [sinkCut, TestTree.exits, sinkExits, sinkWeaks]; omega
  | res i f l r hl hr =>
    simp only [sinkCut, TestTree.exits, sinkExits, sinkWeaks]
    omega

theorem cut_marks_of_no_weak (c : I → Collision) (t : LocalTree Variable I)
    (hw : t.sinkWeaks = 0) : (t.sinkCut c).marks = t.sinkMarks c := by
  induction t with
  | ax | exit => rfl
  | weak => simp [sinkWeaks] at hw
  | res i f l r hl hr =>
    have h : l.sinkWeaks = 0 ∧ r.sinkWeaks = 0 := by simpa [sinkWeaks] using hw
    simp [sinkCut, TestTree.marks, sinkMarks, hl h.1, hr h.2]

theorem mark_route (c : I → Collision) (t : LocalTree Variable I) {k : Collision}
    (h : k ∈ t.sinkMarks c) :
    ∃ j qs, LocalTree.Route t j qs ∧ k = c j := by
  induction t with
  | ax j => exact ⟨j, [], .ax j, by simpa [sinkMarks] using h⟩
  | exit => simp [sinkMarks] at h
  | weak i t ht =>
    obtain ⟨j, qs, path, eq⟩ := ht h
    exact ⟨j, none :: qs, .weak path, eq⟩
  | res i f l r hl hr =>
    rcases List.mem_append.mp h with h | h
    · obtain ⟨j, qs, path, eq⟩ := hr h
      exact ⟨j, some (f, false) :: qs, .right path, eq⟩
    · obtain ⟨j, qs, path, eq⟩ := hl h
      exact ⟨j, some (f, true) :: qs, .left path, eq⟩

theorem cut_marks_subset (c : I → Collision) (t : LocalTree Variable I) :
    ∀ k ∈ (t.sinkCut c).marks, k ∈ t.sinkMarks c := by
  induction t with
  | ax => exact fun _ h => h
  | exit | weak => simp [sinkCut, TestTree.marks]
  | res i f l r hl hr =>
    intro k hk
    exact List.mem_append.mpr ((List.mem_append.mp hk).imp (hr k) (hl k))

theorem routes_hold (c : I → Collision) (t : LocalTree Variable I)
    (valid : ∀ j qs, LocalTree.Route t j qs →
      ∀ p ∈ qs, ∀ s : Fin 3,
        ShortestDag.Accepts (sample (c j) s) p) :
    (t.sinkCut c).Routed := by
  induction t with
  | ax | exit | weak => trivial
  | res i f l r hl hr =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k hk s
      obtain ⟨j, ps, path, rfl⟩ := r.mark_route c (r.cut_marks_subset c k hk)
      exact valid j _ (.right path) (some (f, false)) List.mem_cons_self s
    · intro k hk s
      obtain ⟨j, ps, path, rfl⟩ := l.mark_route c (l.cut_marks_subset c k hk)
      exact valid j _ (.left path) (some (f, true)) List.mem_cons_self s
    · exact hr (fun j qs route p hm s => valid j _ (.right route) p (List.mem_cons_of_mem _ hm) s)
    · exact hl (fun j qs route p hm s => valid j _ (.left route) p (List.mem_cons_of_mem _ hm) s)

theorem all_routes_hold (c : I → Collision) (t : LocalTree Variable I)
    (valid : ∀ j qs, LocalTree.Route t j qs →
      ∀ p ∈ qs, ∀ s : Fin 3,
        ShortestDag.Accepts (sample (c j) s) p) :
    (t.sinkMarks c |>.map Collision.hole).Nodup := by
  induction t with
  | ax | exit => simp [sinkMarks]
  | weak i t ht =>
    exact ht (fun j qs route p hm s => valid j _ (.weak route) p (List.mem_cons_of_mem _ hm) s)
  | res i f l r hl hr =>
    simp only [sinkMarks, List.map_append, List.nodup_append']
    refine ⟨?_, ?_, ?_⟩
    · exact hr (fun j qs route p hm s => valid j _ (.right route) p (List.mem_cons_of_mem _ hm) s)
    · exact hl (fun j qs route p hm s => valid j _ (.left route) p (List.mem_cons_of_mem _ hm) s)
    · intro h hm hn
      obtain ⟨e, he, eqe⟩ := List.mem_map.mp hm
      obtain ⟨g, hg, eqg⟩ := List.mem_map.mp hn
      obtain ⟨j, ps, rpath, rfl⟩ := r.mark_route c he
      obtain ⟨k, qs, lpath, rfl⟩ := l.mark_route c hg
      have even := allIn_follows (c j) f false (fun s => valid j _ (.right rpath) (some (f, false)) List.mem_cons_self s)
      have odd := allIn_follows (c k) f true (fun s => valid k _ (.left lpath) (some (f, true)) List.mem_cons_self s)
      rw [eqe, ← eqg, odd] at even
      cases even

end PNP130Dag.LocalTree

namespace PNP130Dag.LocalTree

open Pcx130

variable {I : Type}

theorem weakFree_iff_sinkWeaks (t : LocalTree Variable I) :
    t.WeakFree ↔ t.sinkWeaks = 0 := by
  induction t <;> simp_all [WeakFree, sinkWeaks]

end PNP130Dag.LocalTree

namespace PNP130Dag.ShortestDag

open Pcx130

variable (d : ShortestDag Formula)

theorem actual_marks_eq_sinkMarks (t : LocalTree Variable (Fin d.pi.length)) :
    (d.actualTree t).marks = t.sinkMarks d.keyAt := by
  induction t <;> simp_all [actualTree, TestTree.marks, LocalTree.sinkMarks]

theorem actual_exits_eq_sinkExits (t : LocalTree Variable (Fin d.pi.length)) :
    (d.actualTree t).exits = t.sinkExits := by
  induction t <;> simp_all [actualTree, TestTree.exits, LocalTree.sinkExits, Nat.add_comm]

theorem sinkMarks_at_most_four (i : Fin d.pi.length) :
    ((d.unroll i).sinkMarks d.keyAt).length ≤ 4 := by
  rw [← d.actual_marks_eq_sinkMarks]
  exact d.actual_unroll_at_most_four i

theorem sinkMarks_pure_exit_bound (i : Fin d.pi.length) (pure : (d.unroll i).sinkWeaks = 0) :
    2 * ((d.unroll i).sinkMarks d.keyAt).length ≤ (d.unroll i).sinkExits + 2 := by
  rw [← d.actual_marks_eq_sinkMarks, ← d.actual_exits_eq_sinkExits]
  exact d.actual_unroll_exit_bound i ((d.unroll i).weakFree_iff_sinkWeaks.mpr pure)

theorem sinkMarks_all_false (i : Fin d.pi.length) :
    ∀ c ∈ (d.unroll i).sinkMarks d.keyAt, ∀ r : Fin 3,
      ¬ PEqualNP.ProofComplexity.LinClauseSat (sample c r) (d.pi.get i) := by
  rw [← d.actual_marks_eq_sinkMarks]
  exact d.actual_unroll_false i

end PNP130Dag.ShortestDag

namespace PNP130Dag.ShortestDag

open PEqualNP.ProofComplexity Pcx130 Pcx130.Components
open scoped BigOperators

variable (d : ShortestDag Formula)

private theorem degree_eq_incoming (i : Fin d.pi.length) :
    degree d.children i = d.incoming i := rfl

private theorem incoming_one_or_multiple {i j : Fin d.pi.length} (h : j ∈ d.children i) :
    d.incoming j = 1 ∨ 2 ≤ d.incoming j := by
  have hp : 0 < d.incoming j := degree_pos_of_parent d.children h
  omega

theorem marks_recurrence (i : Fin d.pi.length) :
    (d.actualTree (d.unroll i)).marks.length =
      (if (d.children i).length = 0 then 1 else 0) +
      ((keptChildren d.children i).map (fun j => (d.actualTree (d.unroll j)).marks.length)).sum := by
  cases h : d.rules i with
  | ax ha =>
    simp [d.unroll_ax h, actualTree, TestTree.marks, keptChildren, children, h, Rule.parents]
  | weak j _ _ =>
    rw [d.unroll_weak h]
    by_cases hj : d.incoming j = 1 <;>
      simp [actualTree, TestTree.marks, keptChildren, children, h, Rule.parents, cutChild,
        hj, d.degree_eq_incoming]
  | res j k _ _ _ =>
    rw [d.unroll_res h]
    by_cases hj : d.incoming j = 1 <;> by_cases hk : d.incoming k = 1 <;>
      simp [actualTree, TestTree.marks, keptChildren, children, h, Rule.parents, cutChild,
        hj, hk, d.degree_eq_incoming, Nat.add_comm]

theorem exit_recurrence (i : Fin d.pi.length) :
    (d.actualTree (d.unroll i)).exits = exitsAt d.children i +
      ((keptChildren d.children i).map (fun j => (d.actualTree (d.unroll j)).exits)).sum := by
  cases h : d.rules i with
  | ax ha =>
    simp [d.unroll_ax h, actualTree, TestTree.exits, exitsAt, keptChildren, children, h, Rule.parents]
  | weak j _ _ =>
    rw [d.unroll_weak h]
    have hj' : j ∈ d.children i := by simp [children, h, Rule.parents]
    rcases d.incoming_one_or_multiple hj' with hj | hj
    · simp [actualTree, keptChildren, exitsAt, children, h, Rule.parents, cutChild,
        hj, d.degree_eq_incoming]
    · have notj : d.incoming j ≠ 1 := by omega
      simp [actualTree, TestTree.exits, keptChildren, exitsAt, children, h, Rule.parents, cutChild,
        hj, notj, d.degree_eq_incoming]
  | res j k _ _ _ =>
    rw [d.unroll_res h]
    have hj' : j ∈ d.children i := by simp [children, h, Rule.parents]
    have hk' : k ∈ d.children i := by simp [children, h, Rule.parents]
    rcases d.incoming_one_or_multiple hj' with hj | hj <;>
      rcases d.incoming_one_or_multiple hk' with hk | hk
    · simp [actualTree, TestTree.exits, keptChildren, exitsAt, children, h, Rule.parents, cutChild,
        hj, hk, d.degree_eq_incoming, Nat.add_comm]
    · have notk : d.incoming k ≠ 1 := by omega
      simp [actualTree, TestTree.exits, keptChildren, exitsAt, children, h, Rule.parents, cutChild,
        hj, hk, notk, d.degree_eq_incoming]
    · have notj : d.incoming j ≠ 1 := by omega
      simp [actualTree, TestTree.exits, keptChildren, exitsAt, children, h, Rule.parents, cutChild,
        hj, hk, notj, d.degree_eq_incoming, Nat.add_comm]
    · have notj : d.incoming j ≠ 1 := by omega
      have notk : d.incoming k ≠ 1 := by omega
      simp [actualTree, TestTree.exits, keptChildren, exitsAt, children, h, Rule.parents, cutChild,
        hj, hk, notj, notk, d.degree_eq_incoming]

theorem sum_marks : (∑ i ∈ roots d.children, (d.actualTree (d.unroll i)).marks.length) =
    (axiomNodes d.children).card := by
  rw [axiomNodes, Finset.card_filter]
  exact component_mass d.children _ _ d.marks_recurrence

theorem sum_exits : (∑ i ∈ roots d.children, (d.actualTree (d.unroll i)).exits) =
     ∑ i, exitsAt d.children i :=
  component_mass d.children _ _ d.exit_recurrence

theorem weak_recurrence (i : Fin d.pi.length) :
    (d.unroll i).sinkWeaks =
      (if (d.children i).length = 1 then 1 else 0) +
      ((keptChildren d.children i).map (fun j => (d.unroll j).sinkWeaks)).sum := by
  cases h : d.rules i with
  | ax ha =>
    simp [d.unroll_ax h, LocalTree.sinkWeaks, keptChildren, children, h, Rule.parents]
  | weak j _ _ =>
    rw [d.unroll_weak h]
    by_cases hj : d.incoming j = 1 <;>
      simp [LocalTree.sinkWeaks, keptChildren, children, h, Rule.parents, cutChild,
        hj, d.degree_eq_incoming]
  | res j k _ _ _ =>
    rw [d.unroll_res h]
    by_cases hj : d.incoming j = 1 <;> by_cases hk : d.incoming k = 1 <;>
      simp [LocalTree.sinkWeaks, keptChildren, children, h, Rule.parents, cutChild,
        hj, hk, d.degree_eq_incoming]

theorem sum_weaks : (∑ i ∈ roots d.children, (d.unroll i).sinkWeaks) =
    (weakNodes d.children).card := by
  rw [weakNodes, Finset.card_filter]
  exact component_mass d.children _ _ d.weak_recurrence

theorem sum_sink_marks : (∑ i ∈ roots d.children, ((d.unroll i).sinkMarks d.keyAt).length) =
    (axiomNodes d.children).card := by
  simp_rw [← d.actual_marks_eq_sinkMarks]
  exact d.sum_marks

theorem sum_sink_exits : (∑ i ∈ roots d.children, (d.unroll i).sinkExits) =
     ∑ i, exitsAt d.children i := by
  simp_rw [← d.actual_exits_eq_sinkExits]
  exact d.sum_exits

end PNP130Dag.ShortestDag

namespace PNP130Dag.ShortestDag

open PEqualNP.ProofComplexity Pcx130 Pcx130.Components
open scoped BigOperators

theorem length_bound_from_sink (d : ShortestDag Formula)
    (sink : ∀ i : Fin d.pi.length, 3 ≤ ((d.unroll i).sinkMarks d.keyAt).length →
      (d.unroll i).sinkExits = 0 → (d.unroll i).sinkWeaks ≠ 1) : 95 < d.pi.length := by
  classical
  by_contra! small
  have z : degree d.children d.root = 0 := d.incoming_at_first
  have pos (i : Fin d.pi.length) (h : i ≠ d.root) : 0 < degree d.children i :=
    d.incoming_pos i (fun e => h (Fin.ext (e.trans d.root_val_zero.symm)))
  have count : (axiomNodes d.children).card = 40 := d.axiom_count
  have budget := node_budget d.children d.root z pos d.children_length (Nat.le_of_eq count.symm) small
  have low := global_bound (roots d.children)
    (fun i => ((d.unroll i).sinkMarks d.keyAt).length) (fun i => (d.unroll i).sinkWeaks)
    (fun i => (d.unroll i).sinkExits) (excess d.children) (weakNodes d.children).card
    (fun i _ => d.sinkMarks_at_most_four i)
    (by rw [d.sum_sink_marks, count]) d.sum_weaks
    (by rw [d.sum_sink_exits]; exact exit_mass d.children d.root z pos)
    (roots_le d.children d.root z pos) (fun i _ => d.sinkMarks_pure_exit_bound i)
    (fun i _ => sink i)
  omega

end PNP130Dag.ShortestDag

namespace Pcx130

open PEqualNP.ProofComplexity

theorem singleton_satisfaction (v : Variable) (b : Bool) (a : Assignment) :
    LinEqSat a ({v}, b) ↔ a v = b := by
  cases h : a v <;> cases b <;> simp [LinEqSat, Finset.filter_singleton, h]

private theorem other_bit_value_card : ∀ (j : Fin 2) (b : Bool),
    (Finset.univ.filter fun h : Fin 4 => h.val.testBit j.val ≠ b).card = 2 := by
  decide +kernel

theorem not_allIn_false_of_singletons (q : LinClause Variable) (hne : q.Nonempty)
    (hsingle : ∀ e ∈ q, e.1.card = 1) (hs : Finset (Fin 4)) (h3 : 3 ≤ hs.card) :
    ¬ ∀ h ∈ hs, ¬ LinClauseSat (allIn h) q := by
  intro hfalse
  obtain ⟨e, emem⟩ := hne
  obtain ⟨v, one⟩ := Finset.card_eq_one.mp (hsingle e emem)
  have sub : hs ⊆ Finset.univ.filter fun h : Fin 4 => h.val.testBit v.2.val ≠ e.2 := by
    intro h hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro val
    apply hfalse h hmem
    refine ⟨e, emem, ?_⟩
    rcases e with ⟨f, b⟩
    change f = {v} at one
    subst f
    exact (singleton_satisfaction v b (allIn h)).2 val
  have le2 := Finset.card_le_card sub
  rw [other_bit_value_card] at le2
  omega

theorem affine_clause_allIn (c : Collision) (q : LinClause Variable)
    (h : ∀ r : Fin 3, ¬ LinClauseSat (sample c r) q) :
    ¬ LinClauseSat (allIn c.hole) q := by
  intro hs
  obtain ⟨⟨f,b⟩, hf, hsat⟩ := hs
  have neg : ∀ r : Fin 3, ¬ LinEqSat (sample c r) (f,b) :=
    fun r hi => h r ⟨(f,b), hf, hi⟩
  have val (a : Assignment) : LinEqSat a (f,b) ↔ parity f a = b := by
    cases b <;> simp [LinEqSat, parity]
  have agree (r : Fin 3) : parity f (sample c r) = !b := by
    have hn := mt (val (sample c r)).2 (neg r)
    cases b <;> simpa using hn
  have ho := allIn_follows c f (!b) agree
  have hyes := (val (allIn c.hole)).1 hsat
  cases b <;> simp_all

theorem weak_premise_not_common (q : LinClause Variable) (hne : q.Nonempty)
    (hsingle : ∀ e ∈ q, e.1.card = 1) (holes : Finset (Fin 4)) (three : 3 ≤ holes.card)
    (falseSamples : ∀ h ∈ holes, ∃ c : Collision, c.hole = h ∧
      ∀ r : Fin 3, ¬ LinClauseSat (sample c r) q) : False := by
  apply not_allIn_false_of_singletons q hne hsingle holes three
  intro h hh
  obtain ⟨c, ch, hf⟩ := falseSamples h hh
  simpa only [ch] using affine_clause_allIn c q hf

theorem sink_resolution_singletons {C D R : LinClause Variable} {f : Finset Variable}
    (result : R = C.erase (f, false) ∪ D.erase (f, true))
    (hc : ∀ e ∈ C, e.1.card = 1) (hd : ∀ e ∈ D, e.1.card = 1) :
    ∀ e ∈ R, e.1.card = 1 := by
  rintro e he
  rw [result, Finset.mem_union] at he
  rcases he with he | he
  · exact hc e (Finset.mem_of_mem_erase he)
  · exact hd e (Finset.mem_of_mem_erase he)

end Pcx130

namespace PNP130Dag.ShortestDag

open Pcx130 PEqualNP.ProofComplexity

variable (d : ShortestDag Formula)

theorem cutCertified (i : Fin d.pi.length) :
    ((d.unroll i).sinkCut d.keyAt).Certified (d.pi.get i) := by
  have aux (n : ℕ) : ∀ i : Fin d.pi.length, d.pi.length - i.val = n →
      ((d.unroll i).sinkCut d.keyAt).Certified (d.pi.get i) := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro i hn
      have sub (j : Fin d.pi.length) (hj : i < j) :
          ((d.cutChild j).sinkCut d.keyAt).Certified (d.pi.get j) := by
        by_cases h : d.incoming j = 1
        · rw [cutChild, ite_eq_left h]
          have bound := j.isLt
          have lt : i.val < j.val := hj
          exact ih _ (by omega) j rfl
        · rw [cutChild, ite_eq_right h]
          exact .exit _
      cases h : d.rules i with
      | ax _ =>
        rw [d.unroll_ax h]
        have ha : d.children i = [] := by simp [children, h, Rule.parents]
        rw [← d.keyAt_clause ha]
        exact .ax _
      | weak j hj hw =>
        rw [d.unroll_weak h]
        exact .exit _
      | res j k hj hk hv =>
        rw [d.unroll_res h]
        exact .split _ (sub k hk) (sub j hj) (Classical.choose_spec hv).2.2
  exact aux _ i rfl

private theorem ordinary_certified {t : TestTree} {C : LinClause Variable}
    (cert : t.Certified C) (zero : t.exits = 0) : ∀ e ∈ C, e.1.card = 1 := by
  induction cert with
  | ax c =>
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    simp
  | exit => simp [TestTree.exits] at zero
  | split f hl hr heq il ir =>
    simp only [TestTree.exits, Nat.add_eq_zero_iff] at zero
    exact sink_resolution_singletons heq (ir zero.2) (il zero.1)

private theorem marked_false (i : Fin d.pi.length) :
    ∀ c ∈ (d.unroll i).sinkMarks d.keyAt, ∀ r : Fin 3,
      ¬ LinClauseSat (sample c r) (d.pi.get i) := by
  intro c hc r
  obtain ⟨j, qs, path, rfl⟩ := (d.unroll i).mark_route d.keyAt hc
  exact (d.marked_sample_route path r).1

private theorem marked_distinct_holes (i : Fin d.pi.length) :
    (((d.unroll i).sinkMarks d.keyAt).map Collision.hole).Nodup :=
  (d.unroll i).all_routes_hold d.keyAt
    (fun _ _ h _ hq r => (d.marked_sample_route h r).2 _ hq)

theorem cut_marks_loss (i : Fin d.pi.length) (exits : (d.unroll i).sinkExits = 0)
    (weaks : (d.unroll i).sinkWeaks ≤ 1) :
    ((d.unroll i).sinkMarks d.keyAt).length ≤
      ((d.unroll i).sinkCut d.keyAt).marks.length + 2 * (d.unroll i).sinkWeaks := by
  have aux (n : ℕ) : ∀ i : Fin d.pi.length, d.pi.length - i.val = n →
      (d.unroll i).sinkExits = 0 → (d.unroll i).sinkWeaks ≤ 1 →
      ((d.unroll i).sinkMarks d.keyAt).length ≤
        ((d.unroll i).sinkCut d.keyAt).marks.length + 2 * (d.unroll i).sinkWeaks := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro i hn ex wk
      have sub (j : Fin d.pi.length) (hj : i < j) (ex : (d.cutChild j).sinkExits = 0)
          (wk : (d.cutChild j).sinkWeaks ≤ 1) :
          ((d.cutChild j).sinkMarks d.keyAt).length ≤
            ((d.cutChild j).sinkCut d.keyAt).marks.length + 2 * (d.cutChild j).sinkWeaks := by
        by_cases h : d.incoming j = 1
        · rw [cutChild, ite_eq_left h] at ex wk ⊢
          have bound := j.isLt
          have lt : i.val < j.val := hj
          exact ih _ (by omega) j rfl ex wk
        · rw [cutChild, ite_eq_right h] at ex
          simp [LocalTree.sinkExits] at ex
      cases rule : d.rules i with
      | ax _ => simp [d.unroll_ax rule, LocalTree.sinkMarks, LocalTree.sinkCut,
          LocalTree.sinkWeaks, TestTree.marks]
      | res j k hj hk hv =>
        rw [d.unroll_res rule] at ex wk ⊢
        have ee : (d.cutChild j).sinkExits = 0 ∧ (d.cutChild k).sinkExits = 0 := by
          simpa [LocalTree.sinkExits] using ex
        change (d.cutChild j).sinkWeaks + (d.cutChild k).sinkWeaks ≤ 1 at wk
        have jl := sub j hj ee.1 (by omega)
        have kl := sub k hk ee.2 (by omega)
        simp only [LocalTree.sinkMarks, LocalTree.sinkCut, LocalTree.sinkWeaks, TestTree.marks,
          List.length_append]
        omega
      | weak j hj hw =>
        rw [d.unroll_weak rule] at ex wk ⊢
        by_cases ha : d.incoming j = 1
        · rw [cutChild, ite_eq_left ha] at ex wk ⊢
          change (d.unroll j).sinkExits = 0 at ex
          change 1 + (d.unroll j).sinkWeaks ≤ 1 at wk
          have ww : (d.unroll j).sinkWeaks = 0 := by omega
          have exitzero : ((d.unroll j).sinkCut d.keyAt).exits = 0 := by
            have h := (d.unroll j).cut_exits d.keyAt
            omega
          have ordinary := ordinary_certified (d.cutCertified j) exitzero
          have nonempty : (d.pi.get j).Nonempty := by
            apply Finset.nonempty_iff_ne_empty.mpr
            intro he
            have eq := d.nodup.injective_get (he.trans d.rootEmpty.symm)
            have val := congrArg Fin.val eq
            have zz := d.root_val_zero
            have lt : i.val < j.val := hj
            omega
          have atMost : ((d.unroll j).sinkMarks d.keyAt).length ≤ 2 := by
            by_contra! big
            let keys := ((d.unroll j).sinkMarks d.keyAt |>.map Collision.hole).toFinset
            have card : keys.card = ((d.unroll j).sinkMarks d.keyAt).length := by
              simp [keys, List.toFinset_card_of_nodup (d.marked_distinct_holes j)]
            refine weak_premise_not_common (d.pi.get j) nonempty ordinary keys (by omega) ?_
            intro h hh
            obtain ⟨c, hc, eq⟩ := List.mem_map.mp (List.mem_toFinset.mp hh)
            exact ⟨c, eq, d.marked_false j c hc⟩
          simp only [LocalTree.sinkMarks, LocalTree.sinkCut, LocalTree.sinkWeaks, TestTree.marks,
            List.length_nil]
          omega
        · rw [cutChild, ite_eq_right ha] at ex
          simp [LocalTree.sinkExits] at ex
  exact aux _ i rfl exits weaks

theorem unroll_sink_bound (i : Fin d.pi.length) (exits : (d.unroll i).sinkExits = 0) :
    ((d.unroll i).sinkMarks d.keyAt).length ≤ 2 ∨ 2 ≤ (d.unroll i).sinkWeaks := by
  by_contra! contra
  have hweak : (d.unroll i).sinkWeaks ≤ 1 := by omega
  let t := (d.unroll i).sinkCut d.keyAt
  have hcut : t.exits ≤ 1 := by
    have h := (d.unroll i).cut_exits d.keyAt
    change t.exits ≤ _ at h
    omega
  have enough : 1 ≤ t.marks.length := by
    have h := d.cut_marks_loss i exits hweak
    change _ ≤ t.marks.length + _ at h
    omega
  have routed : t.Routed := (d.unroll i).routes_hold d.keyAt
    (fun _ _ path q hp r => (d.marked_sample_route path r).2 q hp)
  have hf : ∀ c ∈ t.marks, ∀ r : Fin 3, ¬ LinClauseSat (sample c r) (d.pi.get i) :=
    fun c hc => d.marked_false i c ((d.unroll i).cut_marks_subset d.keyAt c hc)
  have v := TestTree.valid_of_certified (d.cutCertified i) routed (Finset.Subset.refl _)
  have share := shared_from_clause (d.pi.get i) t.marks hf
  have noCredit : (singletonVars (d.pi.get i)).card = 0 :=
    TestTree.shared_three (d.marked_distinct_holes i) (by omega)
      (shared_from_clause _ _ (d.marked_false i))
  obtain ⟨_, low, high⟩ := TestTree.exits_lower_aux t v share
  have impossible : t.marks.length = 1 ∨ t.marks.length = 2 ∨ 3 ≤ t.marks.length := by omega
  rcases impossible with a | a | a
  · have h := low (Or.inl a)
    omega
  · have h := low (Or.inr a)
    omega
  · have h := high a
    omega

end PNP130Dag.ShortestDag

open PEqualNP.ProofComplexity Pcx130 PNP130Dag

theorem proved : ¬ (∃ π : List (LinClause (Fin 5 × Fin 2)),
    IsLinRefutation (BPHP 5 2) π ∧ π.length ≤ 95) := by
  rintro ⟨pi, ⟨deriv, empty⟩, size⟩
  obtain ⟨d, smaller⟩ := shortest_dag deriv empty
  have lower := d.length_bound_from_sink (fun i many noExit => by
    rcases d.unroll_sink_bound i noExit with few | manyWeaks <;> omega)
  omega

end PEqualNP.Outside.L_pcx_130_aux

theorem PEqualNP.Outside.L_pcx_130 : ¬ (∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin 5 × Fin 2)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP 5 2) π ∧ π.length ≤ 95) := PEqualNP.Outside.L_pcx_130_aux.proved
