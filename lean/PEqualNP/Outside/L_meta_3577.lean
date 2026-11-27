import Mathlib
import PEqualNP.Defs

-- The polynomial incidence graph builds on kunalb541's counterexample.
-- We use all unordered coordinate pairs and a constant-weight code, and
-- count the omitted labels separately for each side of the graph.
namespace PEqualNP.Outside.L_meta_3577

abbrev F := ZMod 389
abbrev Ix := Fin 14
abbrev Bits := Fin 15
abbrev DomainPair := {ij : Ix × Ix // ij.1 < ij.2}
abbrev Left := F × F × F
abbrev Right := DomainPair × (F × F)
abbrev V := Left ⊕ Right
abbrev Label := Bool ⊕ (Ix × Bits)

instance primeField : Fact (Nat.Prime 389) := ⟨by norm_num⟩

def xval (i : Ix) : F := (i.val : F)
lemma xval_inj : Function.Injective xval := by
  intro i j eq
  have same := congrArg ZMod.val eq
  apply Fin.ext
  simpa only [xval,ZMod.val_natCast,Nat.mod_eq_of_lt (by have := i.isLt; omega : i.val<389),
    Nat.mod_eq_of_lt (by have := j.isLt; omega : j.val<389)] using same

def eval (p : Left) (x : F) : F := p.1 + p.2.1*x + p.2.2*x*x
def prescribe (p : Left) (ij : DomainPair) : F × F :=
  (eval p (xval ij.val.1),eval p (xval ij.val.2))
def inc (p : Left) (z : Right) : Prop := prescribe p z.1 = z.2
instance incDec (p : Left) (z : Right) : Decidable (inc p z) := inferInstanceAs (Decidable (_ = _))

def graph : SimpleGraph V where
  Adj a b := match a,b with
    | .inl p,.inr z => inc p z
    | .inr z,.inl p => inc p z
    | _,_ => False
  symm := ⟨by rintro (_|_) (_|_) h <;> exact h⟩
  loopless := ⟨by rintro (_|_) <;> simp⟩

instance graphDec : DecidableRel graph.Adj := fun a b => by
  rcases a with p|z <;> rcases b with p'|z' <;> first | exact inferInstanceAs (Decidable (inc _ _)) | exact isFalse id

-- Two different unordered pairs of coordinates supply at least three inputs.
lemma freshCoordinate (a b : DomainPair) (different : a ≠ b) :
    (b.val.1≠a.val.1 ∧ b.val.1≠a.val.2) ∨ (b.val.2≠a.val.1 ∧ b.val.2≠a.val.2) := by
  by_contra! absent
  have l : b.val.1=a.val.1 ∨ b.val.1=a.val.2 := by by_contra! no;exact no.2 (absent.1 no.1)
  have r : b.val.2=a.val.1 ∨ b.val.2=a.val.2 := by by_contra! no;exact no.2 (absent.2 no.1)
  have ha := a.property
  have hb := b.property
  rcases l with one|one <;> rcases r with two|two
  · rw [one,two] at hb;exact (lt_irrefl _ hb)
  · exact different (Subtype.ext (Prod.ext one.symm two.symm))
  · rw [one,two] at hb;exact (not_lt_of_ge ha.le hb)
  · rw [one,two] at hb;exact (lt_irrefl _ hb)

lemma threeValues {p r : Left} {a b c : F} (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (xa : eval p a=eval r a) (xb : eval p b=eval r b) (xc : eval p c=eval r c) : p=r := by
  unfold eval at xa xb xc
  have pair (z : F) (az : a≠z)
      (xz : p.1+p.2.1*z+p.2.2*z*z=r.1+r.2.1*z+r.2.2*z*z) :
      (p.2.1-r.2.1)+(z+a)*(p.2.2-r.2.2)=0 := by
    apply (mul_eq_zero.mp (show (z-a)*((p.2.1-r.2.1)+(z+a)*(p.2.2-r.2.2))=0 from by
      linear_combination xz-xa)).resolve_left (sub_ne_zero.mpr az.symm)
  have f := pair b ab xb
  have g := pair c ac xc
  have quad : p.2.2=r.2.2 := sub_eq_zero.mp ((mul_eq_zero.mp
    (show (b-c)*(p.2.2-r.2.2)=0 from by linear_combination f-g)).resolve_left (sub_ne_zero.mpr bc))
  have lin : p.2.1=r.2.1 := sub_eq_zero.mp (by simpa [quad] using f)
  have const : p.1=r.1 := by simpa [quad,lin] using xa
  exact Prod.ext const (Prod.ext lin quad)

lemma noRectangle {p r : Left} {z w : Right} (unequal : p≠r) (neq : z≠w)
    (pz : inc p z) (pw : inc p w) (rz : inc r z) (rw' : inc r w) : False := by
  have sets : z.1≠w.1 := by
    intro eq
    exact neq (Prod.ext eq (pz.symm.trans ((congrArg (prescribe p) eq).trans pw)))
  have f := congrArg Prod.fst (pz.trans rz.symm)
  have s := congrArg Prod.snd (pz.trans rz.symm)
  have ab : xval z.1.val.1≠xval z.1.val.2 := xval_inj.ne (ne_of_lt z.1.property)
  rcases freshCoordinate z.1 w.1 sets with extra|extra
  · exact unequal (threeValues ab (xval_inj.ne extra.1.symm) (xval_inj.ne extra.2.symm) f s
      (congrArg Prod.fst (pw.trans rw'.symm)))
  · exact unequal (threeValues ab (xval_inj.ne extra.1.symm) (xval_inj.ne extra.2.symm) f s
      (congrArg Prod.snd (pw.trans rw'.symm)))

lemma noFour (a b c d : V) (ac : a≠c) (bd : b≠d) :
    ¬ (graph.Adj a b ∧ graph.Adj b c ∧ graph.Adj c d ∧ graph.Adj d a) := by
  rintro ⟨ab,bc,cd,da⟩
  rcases a with a|a <;> rcases b with b|b <;> rcases c with c|c <;> rcases d with d|d <;>
    simp only [graph] at ab bc cd da <;> try contradiction
  · exact noRectangle (fun e => ac (congrArg Sum.inl e)) (fun e => bd (congrArg Sum.inr e)) ab da bc cd
  · exact noRectangle (fun e => bd (congrArg Sum.inl e)) (fun e => ac (congrArg Sum.inr e)) ab bc da cd

lemma domainCount : Fintype.card DomainPair=91 := by decide +kernel
lemma leftCount : Fintype.card Left=58863869 := by norm_num [Left,Fintype.card_prod,F,ZMod.card]
lemma rightCount : Fintype.card Right=13770211 := by
  rw [show Fintype.card Right=Fintype.card DomainPair*Fintype.card (F×F) from Fintype.card_prod _ _,domainCount]
  norm_num [F,Fintype.card_prod,ZMod.card]
lemma vertexCount : Fintype.card V=72634080 := by rw [Fintype.card_sum,leftCount,rightCount]
lemma labelCount : Fintype.card Label=212 := by norm_num [Label,Ix,Bits,Fintype.card_prod,Fintype.card_sum]

end PEqualNP.Outside.L_meta_3577

namespace PEqualNP.Outside.L_meta_3577
open scoped Classical

def triples : Finset (Finset Bits) := (Finset.univ : Finset Bits).powersetCard 3
abbrev Code := ↥triples

lemma tripleCount : Fintype.card Code=455 := by
  rw [Fintype.card_coe]
  simp only [triples,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]
  decide +kernel

def codeIndex (z : F) : Fin 455 := ⟨z.val,by have := ZMod.val_lt z;omega⟩

def member (Z : F → Finset Bits) : Label → V → Prop
  | .inl marker,.inl _ => marker=false
  | .inl marker,.inr _ => marker=true
  | .inr (i,b),.inl p => b ∉ Z (eval p (xval i))
  | .inr (i,b),.inr r =>
      (i=r.1.val.1 ∧ b∈Z r.2.1) ∨ (i=r.1.val.2 ∧ b∈Z r.2.2)

section AbstractFamily

variable (Z : F → Finset Bits) (B : Label → Finset V)
  (members : ∀ j v, v∈B j ↔ member Z j v)
  (separateSymbols : ∀ {x y : F}, x≠y → ∃ b ∈ Z y, b ∉ Z x)

lemma independentPair (label : Label) (p : Left) (r : Right)
    (hp : member Z label (.inl p)) (hr : member Z label (.inr r)) : ¬ inc p r := by
  intro eq
  rcases label with m | ⟨i,b⟩
  · change m=false at hp;change m=true at hr;simp [hp] at hr
  · change b ∉ Z (eval p (xval i)) at hp
    rcases hr with ⟨j,on⟩ | ⟨j,on⟩
    · subst i
      have h : eval p (xval r.1.val.1) = r.2.1 := congrArg Prod.fst eq
      rw [h] at hp;exact hp on
    · subst i
      have h : eval p (xval r.1.val.2) = r.2.2 := congrArg Prod.snd eq
      rw [h] at hp;exact hp on

include members in
theorem independent (label : Label) : ∀ a∈B label, ∀ b∈B label, ¬graph.Adj a b := by
  intro a ma b mb
  rcases a with p|r <;> rcases b with q|z
  · exact id
  · exact independentPair Z label p z ((members _ _).mp ma) ((members _ _).mp mb)
  · exact independentPair Z label q r ((members _ _).mp mb) ((members _ _).mp ma)
  · exact id

include members in
theorem someIn (v : V) : ∃j, v∈B j := by
  rcases v with p|r
  · exact ⟨.inl false,(members _ _).mpr rfl⟩
  · exact ⟨.inl true,(members _ _).mpr rfl⟩

include members in
theorem someOut (v : V) : ∃j, v∉B j := by
  rcases v with p|r
  · exact ⟨.inl true,fun h => Bool.noConfusion ((members _ _).mp h)⟩
  · exact ⟨.inl false,fun h => Bool.noConfusion ((members _ _).mp h)⟩

include members separateSymbols in
theorem inconsistent {p : Left} {r : Right} (bad : ¬ inc p r) :
    ∃ j, (.inl p : V)∈B j ∧ (.inr r : V)∈B j := by
  by_cases h : eval p (xval r.1.val.1) = r.2.1
  · have miss : eval p (xval r.1.val.2) ≠ r.2.2 := fun eq => bad (Prod.ext h eq)
    obtain ⟨b,on,off⟩ := separateSymbols miss
    exact ⟨.inr (r.1.val.2,b),(members _ _).mpr off,(members _ _).mpr (Or.inr ⟨rfl,on⟩)⟩
  · obtain ⟨b,on,off⟩ := separateSymbols h
    exact ⟨.inr (r.1.val.1,b),(members _ _).mpr off,(members _ _).mpr (Or.inl ⟨rfl,on⟩)⟩

include members separateSymbols in
theorem nonedges (a b : V) (_ : a≠b) (bad : ¬graph.Adj a b) : ∃j, a∈B j ∧ b∈B j := by
  rcases a with p|r <;> rcases b with q|z
  · exact ⟨.inl false,(members _ _).mpr rfl,(members _ _).mpr rfl⟩
  · exact inconsistent Z B members separateSymbols bad
  · obtain ⟨j,hq,hr⟩ := inconsistent Z B members separateSymbols bad;exact ⟨j,hr,hq⟩
  · exact ⟨.inl true,(members _ _).mpr rfl,(members _ _).mpr rfl⟩

lemma twoMissing {α : Type} [Fintype α] [DecidableEq α] (S : Finset α) {a b : α}
    (ne : a≠b) (ha : a∉S) (hb : b∉S) : S.card+2 ≤ Fintype.card α := by
  have sub : {a,b} ⊆ Finset.univ \ S := Finset.insert_subset (by simpa using ha)
    (Finset.singleton_subset_iff.mpr (by simpa using hb))
  have bound := Finset.card_le_card sub
  have total := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  rw [Finset.card_pair ne] at bound
  rw [Finset.card_univ] at total
  omega

include members in
theorem missesTwo (j : Label) : (B j).card+2 ≤ Fintype.card V := by
  let i : DomainPair := ⟨(0,1),by decide⟩
  let a : Left := (0,0,0)
  let b : Left := (1,0,0)
  let c : Right := (i,prescribe a i)
  let other : DomainPair := ⟨(2,3),by decide⟩
  let d : Right := (other,prescribe b other)
  have edge0 : graph.Adj (.inl a) (.inr c) := rfl
  have edge1 : graph.Adj (.inl b) (.inr d) := rfl
  have avoid {u v : V} (e : graph.Adj u v) : u∉B j ∨ v∉B j := by
    by_contra! both
    exact independent Z B members j _ both.1 _ both.2 e
  have left : a≠b := fun eq => zero_ne_one (congrArg (fun z : Left => z.1) eq)
  have right : c≠d := fun eq => (by decide : (0:ℕ)≠2) (congrArg (fun z : Right => z.1.val.1.val) eq)
  rcases avoid edge0 with x|x <;> rcases avoid edge1 with y|y
  · exact twoMissing _ (fun e => left (Sum.inl.inj e)) x y
  · exact twoMissing _ (fun e => by cases e) x y
  · exact twoMissing _ (fun e => by cases e) x y
  · exact twoMissing _ (fun e => right (Sum.inr.inj e)) x y

end AbstractFamily

end PEqualNP.Outside.L_meta_3577

namespace PEqualNP.Outside.L_meta_3577

-- Field elements use the first 389 triples in colexicographic order.
noncomputable def orderedTriples : Finset (Colex (Finset Bits)) := triples.map toColex.toEmbedding

lemma orderedCount : orderedTriples.card=455 := by
  rw [orderedTriples,Finset.card_map]
  exact (Fintype.card_coe triples).symm.trans tripleCount

noncomputable def chosenTriple (z : F) : ↥orderedTriples :=
  (orderedTriples.orderIsoOfFin orderedCount) (codeIndex z)

noncomputable def canonicalZeros (z : F) : Finset Bits := ofColex (chosenTriple z).val

lemma canonicalCard (z : F) : (canonicalZeros z).card=3 := by
  have mem : (chosenTriple z).val ∈ triples.map toColex.toEmbedding := (chosenTriple z).property
  obtain ⟨s,hs,eq⟩ := Finset.mem_map.mp mem
  have value : s = canonicalZeros z := congrArg (fun t : Colex (Finset Bits) => ofColex t) eq
  exact value ▸ (Finset.mem_powersetCard.mp hs).2

set_option maxRecDepth 4096 in
lemma canonicalDifferent {x y : F} (ne : x≠y) : ∃ b ∈ canonicalZeros y, b ∉ canonicalZeros x := by
  apply Finset.not_subset.mp
  intro sub
  have sets := Finset.eq_of_subset_of_card_le sub (by rw [canonicalCard,canonicalCard])
  have rep : (chosenTriple y).val=(chosenTriple x).val := ofColex.injective sets
  have index : codeIndex y = codeIndex x :=
    (orderedTriples.orderIsoOfFin orderedCount).injective (Subtype.ext rep)
  have values : y.val=x.val := congrArg (fun a : Fin 455 => a.val) index
  apply ne
  apply ZMod.val_injective 389
  exact values.symm

noncomputable def canonicalBlocks (j : Label) : Finset V := by
  classical exact Finset.univ.filter (member canonicalZeros j)

lemma memCanonical (j : Label) (v : V) : v∈canonicalBlocks j ↔ member canonicalZeros j v := by
  classical simp only [canonicalBlocks,Finset.mem_filter,Finset.mem_univ,true_and]

end PEqualNP.Outside.L_meta_3577

namespace PEqualNP.Outside.L_meta_3577

open scoped Classical

def coordLabel (i : Ix) : Bits ↪ Label :=
  ⟨fun b => .inr (i,b),fun _ _ h => congrArg Prod.snd (Sum.inr.inj h)⟩

lemma markerAbsent {i : Ix} (m : Bool) (S : Finset Bits) : (Sum.inl m : Label) ∉ S.map (coordLabel i) := by
  intro h;obtain ⟨b,_,eq⟩ := Finset.mem_map.mp h;cases eq

lemma coordinatesDisjoint {i j : Ix} (ne : i≠j) (S T : Finset Bits) :
    Disjoint (S.map (coordLabel i)) (T.map (coordLabel j)) := by
  apply Finset.disjoint_left.mpr
  intro k h g
  obtain ⟨a,_,ea⟩ := Finset.mem_map.mp h
  obtain ⟨b,_,eb⟩ := Finset.mem_map.mp g
  exact ne (congrArg Prod.fst (Sum.inr.inj (ea.trans eb.symm)))

def missed {K X : Type} [Fintype K] [DecidableEq X] (B : K → Finset X) (v : X) :=
  Finset.univ.filter fun j => v∉B j

lemma filterSum {X : Type} (S : Finset X) (p : X → Prop) [DecidablePred p] :
    (S.filter p).card = ∑ x ∈ S, if p x then (1:ℕ) else 0 := by
  rw [← Finset.sum_filter];simp

theorem transposeLoss {K X : Type} [Fintype K] [Fintype X] [DecidableEq X] (B : K → Finset X) :
    (∑ j, (Fintype.card X - (B j).card)) = ∑ v, (missed B v).card := by
  have row (j : K) : Fintype.card X - (B j).card = (Finset.univ.filter fun v => v∉B j).card := by
    have sub := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (B j))
    have eq : Finset.univ \ B j = Finset.univ.filter (fun v => v ∉ B j) := by ext; simp
    rw [eq,Finset.card_univ] at sub
    omega
  simp_rw [row,missed,filterSum]
  exact Finset.sum_comm

section Family
variable (Z : F → Finset Bits) (B : Label → Finset V)
    (members : ∀ j v, v∈B j ↔ member Z j v) (weight : ∀z, (Z z).card=3)

include members weight in
theorem leftLoss (p : Left) : (missed B (.inl p)).card ≤ 43 := by
  let part := fun i : Ix => (Z (eval p (xval i))).map (coordLabel i)
  let pool := Finset.univ.biUnion part
  have contained : missed B (.inl p) ⊆ insert (.inl true) pool := by
    intro j hj
    have absent := (Finset.mem_filter.mp hj).2
    rcases j with marker | ⟨i,b⟩
    · cases marker with
      | false => exact (absent ((members _ _).mpr rfl)).elim
      | true => exact Finset.mem_insert_self _ _
    · have inc : b∈Z (eval p (xval i)) := by
        by_contra out
        exact absent ((members _ _).mpr out)
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,
        Finset.mem_map.mpr ⟨b,inc,rfl⟩⟩)
  have bound : pool.card ≤ (Finset.univ : Finset Ix).card * 3 :=
    Finset.card_biUnion_le_card_mul _ part 3 (fun i _ => by simp [part,weight])
  have elems : (Finset.univ : Finset Ix).card=14 := by simp [Ix]
  rw [elems] at bound
  have plus := Finset.card_insert_le (.inl true : Label) pool
  have used := Finset.card_le_card contained
  omega

include members weight in
theorem rightLoss (r : Right) : (missed B (.inr r)).card ≤ 205 := by
  let S := (Z r.2.1).map (coordLabel r.1.val.1)
  let T := (Z r.2.2).map (coordLabel r.1.val.2)
  let selected := (Finset.univ : Finset Label).filter fun j => (.inr r : V) ∈ B j
  have dis : Disjoint S T := coordinatesDisjoint (ne_of_lt r.1.property) _ _
  have notMarked : (Sum.inl true : Label) ∉ S ∪ T := by
    intro inh
    rcases Finset.mem_union.mp inh with a|b
    · exact markerAbsent _ _ a
    · exact markerAbsent _ _ b
  have sub : insert (.inl true) (S ∪ T) ⊆ selected := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,(members _ _).mpr ?_⟩
    rcases Finset.mem_insert.mp hz with rfl | rest
    · exact rfl
    rcases Finset.mem_union.mp rest with a|b
    · obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp a
      exact Or.inl ⟨rfl,hk⟩
    · obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp b
      exact Or.inr ⟨rfl,hk⟩
  have bound := Finset.card_le_card sub
  have sc : S.card=3 := by simp [S,weight]
  have tc : T.card=3 := by simp [T,weight]
  rw [Finset.card_insert_of_notMem notMarked,Finset.card_union_of_disjoint dis,sc,tc] at bound
  have together := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Label))
    (fun j => (.inr r : V) ∈ B j)
  change selected.card + (missed B (.inr r)).card = _ at together
  rw [Finset.card_univ,labelCount] at together
  omega

include members weight in
theorem totalBound : (∑ j : Label, (Fintype.card V - (B j).card)) ≤ 5354039622 := by
  let price : V → ℕ := Sum.elim (fun _ => 43) (fun _ => 205)
  have each (v : V) : (missed B v).card ≤ price v := by
    rcases v with p|r
    · exact leftLoss Z B members weight p
    · exact rightLoss Z B members weight r
  rw [transposeLoss]
  refine (Finset.sum_le_sum (fun v _ => each v)).trans ?_
  rw [Fintype.sum_sum_type]
  simp only [price,Sum.elim_inl,Sum.elim_inr,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,leftCount,rightCount]
  decide

end Family
end PEqualNP.Outside.L_meta_3577

namespace PEqualNP.Outside.L_meta_3577

-- The edge injection and the transport to Fin use the same incidence model as kunalb541.
section
variable {L R I : Type} [Fintype L] [Fintype I]
theorem edgeInjection (mk : L → I → R) (proj : R → I) (hp : ∀ l i, proj (mk l i) = i)
    (G : SimpleGraph (L ⊕ R)) [Fintype G.edgeSet]
    (edges : ∀ l i, G.Adj (.inl l) (.inr (mk l i))) :
    ∀ k : Nat, Fintype.card I = k → Fintype.card L * k ≤ G.edgeFinset.card := by
  rintro _ rfl
  let emit (p : L × I) : G.edgeSet := ⟨s(.inl p.1,.inr (mk p.1 p.2)), edges p.1 p.2⟩
  have inject : Function.Injective emit := by
    rintro ⟨u,i⟩ ⟨v,j⟩ h
    have he : s((Sum.inl u : L ⊕ R),Sum.inr (mk u i)) =
              s((Sum.inl v : L ⊕ R),Sum.inr (mk v j)) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp he with ⟨hu,hm⟩ | ⟨bad,_⟩
    · exact Prod.ext (Sum.inl.inj hu) (by simpa only [hp] using congrArg proj (Sum.inr.inj hm))
    · cases bad
  calc
    Fintype.card L * Fintype.card I = Fintype.card (L × I) := (Fintype.card_prod L I).symm
    _ ≤ Fintype.card G.edgeSet := Fintype.card_le_of_injective emit inject
    _ = G.edgeFinset.card := G.card_edgeSet
end


lemma edgeBudget : 5356612079 ≤ graph.edgeFinset.card := by
  have h := edgeInjection (I := DomainPair) (fun p ij => (ij,prescribe p ij)) Prod.fst
    (fun _ _ => rfl) graph (fun _ _ => rfl) 91 domainCount
  rw [leftCount] at h
  exact h

-- Transport the actual sum of omitted vertices along the two finite relabelings.
theorem transfer {A K : Type} [Fintype A] [Fintype K] [DecidableEq A]
    (G : SimpleGraph A) [DecidableRel G.Adj] (side : A → Bool) (B : K → Finset A)
    (part : ∀ a b, G.Adj a b → side a ≠ side b)
    (sq : ∀ a b c d, a≠c → b≠d → ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (num : 2 ≤ Fintype.card K)
    (ind : ∀j, ∀a∈B j, ∀b∈B j, ¬G.Adj a b)
    (covered : ∀v, ∃j, v∈B j) (excluded : ∀v, ∃j, v∉B j)
    (miss : ∀j, (B j).card+2 ≤ Fintype.card A)
    (pair : ∀ a b, a≠b → ¬G.Adj a b → ∃j, a∈B j ∧ b∈B j)
    (tooManyEdges : (∑ j : K, (Fintype.card A - (B j).card)) < G.edgeFinset.card) :
    ¬ (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)), (∀ a b : Fin n, G.Adj a b → side a ≠ side b) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → 2 ≤ k → (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) → (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) → (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) → (∀ j : Fin k, (I j).card + 2 ≤ n) → (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) → ∃ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ G.edgeFinset.card + T.card + 1 ≤ ∑ j : Fin k, (n - (I j).card)) := by
  classical
  intro universal
  let e := Fintype.equivFin A
  let f := Fintype.equivFin K
  let H := G.comap e.symm
  let J := fun j : Fin (Fintype.card K) => (B (f.symm j)).map e.toEmbedding
  have mem (j v) : v ∈ J j ↔ e.symm v ∈ B (f.symm j) := by simp [J]
  obtain ⟨T,_,bound⟩ := universal _ _ H (fun v => side (e.symm v)) J
    (fun a b => part _ _) (fun a b c d ac bd => sq _ _ _ _ (e.symm.injective.ne ac) (e.symm.injective.ne bd)) num
    (fun j a ha b hb => ind _ _ ((mem _ _).mp ha) _ ((mem _ _).mp hb))
    (by intro v;obtain ⟨j,h⟩ := covered (e.symm v);exact ⟨f j,(mem _ _).mpr (by simpa using h)⟩)
    (by intro v;obtain ⟨j,h⟩ := excluded (e.symm v);exact ⟨f j,fun inside => h (by simpa using (mem _ _).mp inside)⟩)
    (fun j => by simpa only [J,Finset.card_map] using miss (f.symm j))
    (by intro a b ne no;obtain ⟨j,ha,hb⟩ := pair _ _ (e.symm.injective.ne ne) no
        exact ⟨f j,(mem _ _).mpr (by simpa using ha),(mem _ _).mpr (by simpa using hb)⟩)
  have edges : H.edgeFinset.card=G.edgeFinset.card := (SimpleGraph.Iso.comap e.symm G).card_edgeFinset_eq
  have loss : (∑ j : Fin (Fintype.card K), (Fintype.card A - (J j).card)) = ∑ j : K, (Fintype.card A - (B j).card) := by
    simp only [J,Finset.card_map]
    exact Equiv.sum_comp f.symm (fun j => Fintype.card A - (B j).card)
  rw [edges,loss] at bound
  omega

end PEqualNP.Outside.L_meta_3577

open PEqualNP.Outside.L_meta_3577 in
theorem PEqualNP.Outside.L_meta_3577 :
    ¬ (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)), (∀ a b : Fin n, G.Adj a b → side a ≠ side b) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → 2 ≤ k → (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) → (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) → (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) → (∀ j : Fin k, (I j).card + 2 ≤ n) → (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) → ∃ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ G.edgeFinset.card + T.card + 1 ≤ ∑ j : Fin k, (n - (I j).card)) := by
  classical
  let side : V → Bool := Sum.elim (fun _ => false) (fun _ => true)
  have part : ∀a b, graph.Adj a b → side a ≠ side b := by
    rintro (_|_) (_|_) h <;> first | exact h.elim | exact Bool.false_ne_true | exact Ne.symm Bool.false_ne_true
  have large : (∑ j : Label, (Fintype.card V - (canonicalBlocks j).card)) < graph.edgeFinset.card := by
    have cost := totalBound canonicalZeros canonicalBlocks memCanonical canonicalCard
    have count := edgeBudget
    omega
  exact transfer graph side canonicalBlocks part noFour (by rw [labelCount];decide)
    (independent canonicalZeros canonicalBlocks memCanonical) (someIn canonicalZeros canonicalBlocks memCanonical) (someOut canonicalZeros canonicalBlocks memCanonical)
    (missesTwo canonicalZeros canonicalBlocks memCanonical) (nonedges canonicalZeros canonicalBlocks memCanonical canonicalDifferent) large
