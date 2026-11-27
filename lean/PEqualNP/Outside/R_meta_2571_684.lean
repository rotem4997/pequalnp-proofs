import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- There are 36 input edges and three marked singletons. The negative checks use
-- the maximal independent sets of the graph and of its induced graph after the
-- three marked vertices have been removed.
set_option maxHeartbeats 900000 in
theorem PEqualNP.Outside.R_meta_2571_684
    (monotoneWire : ∀ (n : ℕ) (B : Circuit), Monotone2 B → ∀ (x y : Fin n → Bool),
      (∀ i,x i=true → y i=true) → ∀ a : ℕ,
        (B.wires (List.ofFn x)).getD a false=true → (B.wires (List.ofFn y)).getD a false=true)
    (boundary :
      let E := fun p l : Fin 25 => p.val<12 ∧ 12≤l.val ∧
        (p.val+l.val+2)%13∈([0,1,3,9] : List ℕ) ∧ p.val∉([0,2,8] : List ℕ)
      let J : Finset (Fin 25) := {13,15,21}
      let clear := fun S : Finset (Fin 25) => ¬∃ p∈S,∃ l∈S,E p l
      let cap := fun F S : Finset (Fin 25) => S⊆F ∧ clear S ∧ ∀ i∈F,i∉S → ¬clear (insert i S)
      ∃ (B : Circuit) (q : ℕ),Monotone2 B ∧ B.size≤45 ∧ B.output<25+B.size ∧ q<25+B.size ∧
        let read := fun (S : Finset (Fin 25)) (a : ℕ) => (B.wires (List.ofFn (fun i => decide (i∈S)))).getD a false
        (∀ p l,E p l → read {p,l} B.output=true) ∧
        (∀ S,cap Finset.univ S → read S B.output=false) ∧
        (∀ i∈J,read {i} q=true) ∧ (∀ S,cap (Finset.univ \ J) S → read S q=false)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (45 : ℕ) ∧ x1.output < (25 : ℕ) + x1.size ∧ x2 < (25 : ℕ) + x1.size ∧ ∀ (x3 : Fin (25 : ℕ) → Bool), (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (25 : ℕ)) (x5 : Fin (25 : ℕ)), ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x4 ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)] ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) ∧ (x1.eval (List.ofFn x3) = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  classical
  let E := fun p l : Fin 25 => p.val<12 ∧ 12≤l.val ∧
    (p.val+l.val+2)%13∈([0,1,3,9] : List ℕ) ∧ p.val∉([0,2,8] : List ℕ)
  let J : Finset (Fin 25) := {13,15,21}
  let clear := fun S : Finset (Fin 25) => ¬∃ p∈S,∃ l∈S,E p l
  let cap := fun F S : Finset (Fin 25) => S⊆F ∧ clear S ∧ ∀ i∈F,i∉S → ¬clear (insert i S)
  obtain ⟨B,q,hB,sz,out,qsize,y,n,mark,unmarked⟩ := boundary
  let read := fun (S : Finset (Fin 25)) (a : ℕ) => (B.wires (List.ofFn (fun i => decide (i∈S)))).getD a false
  change ∀ p l,E p l → read {p,l} B.output=true at y
  change ∀ S,cap Finset.univ S → read S B.output=false at n
  change ∀ i∈J,read {i} q=true at mark
  change ∀ S,cap (Finset.univ \ J) S → read S q=false at unmarked
  have increasing {A D : Finset (Fin 25)} (inc : A⊆D) (w : ℕ) : read A w=true → read D w=true := by
    apply monotoneWire 25 B hB
    intro i h
    exact decide_eq_true (inc (of_decide_eq_true h))
  have extend {F X : Finset (Fin 25)} (sub : X⊆F) (hx : clear X) :
      ∃ S,X⊆S ∧ cap F S := by
    let options := F.powerset.filter (fun S => X⊆S ∧ clear S)
    have start : X∈options := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr sub,Finset.Subset.refl _,hx⟩
    obtain ⟨S,hs,best⟩ := Finset.exists_max_image options Finset.card ⟨X,start⟩
    obtain ⟨sf,xs,cs⟩ := Finset.mem_filter.mp hs
    have inside := Finset.mem_powerset.mp sf
    refine ⟨S,xs,inside,cs,?_⟩
    intro i hi miss more
    have alt : insert i S∈options := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.insert_subset hi inside),xs.trans (Finset.subset_insert _ _),more⟩
    have wide := best _ alt
    rw [Finset.card_insert_of_notMem miss] at wide
    omega
  refine ⟨B,q,hB,sz,out,qsize,?_⟩
  intro x
  let X := Finset.univ.filter (fun i => x i=true)
  have support (i : Fin 25) : i∈X ↔ x i=true := by simp [X]
  have input : (fun i : Fin 25 => decide (i∈X))=x := by
    funext i
    simp [support]
  have same (w : ℕ) : read X w=(B.wires (List.ofFn x)).getD w false := by
    change (B.wires (List.ofFn (fun i => decide (i∈X)))).getD w false=_
    rw [input]
  have output : B.eval (List.ofFn x)=read X B.output := (same B.output).symm
  have yes {p l : Fin 25} (edge : E p l) (xp : x p=true) (xl : x l=true) : read X B.output=true := by
    apply increasing (A:={p,l}) (D:=X) _ B.output (y p l edge)
    exact Finset.insert_subset ((support _).mpr xp) (Finset.singleton_subset_iff.mpr ((support _).mpr xl))
  have no (cx : clear X) : read X B.output=false := by
    obtain ⟨S,sub,hs⟩ := extend (Finset.subset_univ X) cx
    exact Bool.eq_false_iff.mpr (fun t => by have val := increasing sub _ t; rw [n S hs] at val; contradiction)
  constructor
  · constructor
    · intro good
      by_contra miss
      have independent : clear X := by
        rintro ⟨p,hp,l,hl,pr,lr,modulo,sel⟩
        exact miss ⟨p,l,pr,lr,modulo,sel,(support _).mp hp,(support _).mp hl⟩
      rw [output,no independent] at good
      contradiction
    · rintro ⟨p,l,pr,lr,modulo,sel,hp,hl⟩
      rw [output]
      exact yes ⟨pr,lr,modulo,sel⟩ hp hl
  · intro zero
    have cx : clear X := by
      rintro ⟨p,hp,l,hl,edge⟩
      have on := yes edge ((support _).mp hp) ((support _).mp hl)
      rw [output,on] at zero
      contradiction
    rw [← same]
    by_cases chosen : ∃ i∈J,i∈X
    · obtain ⟨i,member,hi⟩ := chosen
      have one := increasing (Finset.singleton_subset_iff.mpr hi) q (mark i member)
      rw [one]
      have active := (support i).mp hi
      simp only [J,Finset.mem_insert,Finset.mem_singleton] at member
      rcases member with rfl|rfl|rfl <;> simp [active]
    · have sub : X ⊆ Finset.univ \ J := by
        intro i hi
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun h => chosen ⟨i,h,hi⟩⟩
      obtain ⟨S,small,maximal⟩ := extend sub cx
      have off : read X q=false := Bool.eq_false_iff.mpr (fun s => by
        have on := increasing small q s
        rw [unmarked S maximal] at on
        contradiction)
      have unset (i : Fin 25) (hi : i∈J) : x i=false := Bool.eq_false_iff.mpr
        (fun h => chosen ⟨i,hi,(support i).mpr h⟩)
      simp [off,unset 13 (by decide),unset 15 (by decide),unset 21 (by decide)]
