import Mathlib
import PEqualNP.Defs

open PEqualNP.GenericRejection

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_7758_618
    (patch :
      let step := fun (w : List ℕ) (g : Bool × ℕ × ℕ) => w ++ [if g.1 then
        w.getD g.2.1 0 ||| w.getD g.2.2 0 else w.getD g.2.1 0 &&& w.getD g.2.2 0]
      let target := fun (w : List ℕ) => ((List.range 13).map (fun j =>
        w.getD (13+j) 0 &&& (([0,1,3,9] : List ℕ).map (fun d => w.getD ((d+13-j)%13) 0)).foldl (· ||| ·) 0)).foldl (· ||| ·) 0
      ∃ (extra : List (Fin 13)) (tail : List (Bool × ℕ × ℕ)),
        extra.length=7 ∧ ((0 : Fin 13)::extra).Nodup ∧ tail.length≤24 ∧
        let front := (List.range 8).flatMap (fun i =>
        let j := ((0::extra).getD i 0).val
        let p := fun d : ℕ => (d+13-j)%13
        let k := 26+(5*i-1)
        ([(true,p 0,p 1),(true,p 3,p 9),(true,k,k+1),(false,13+j,k+2)] : List (Bool × ℕ × ℕ)) ++
          if i=0 then [] else [(true,k-1,k+3)])
        ∀ w : List ℕ,w.length=26 → (tail.foldl step (front.foldl step w)).getLastD 0=target w)
    (packLines :
      let hit := fun (x : List Bool) => (List.range 13).any (fun j =>
        x.getD (13+j) false && ([0,1,3,9] : List ℕ).any (fun d => x.getD ((d+13-j)%13) false))
      let target := fun (w : List ℕ) => ((List.range 13).map (fun j =>
        w.getD (13+j) 0 &&& (([0,1,3,9] : List ℕ).map (fun d => w.getD ((d+13-j)%13) 0)).foldl (· ||| ·) 0)).foldl (· ||| ·) 0
      ∀ rows : List (Bool × List Bool), (∀ r∈rows,r.1=hit r.2) →
        let w := List.ofFn (fun i : Fin 26 => (rows.map (fun r => r.2.getD i.val false)).foldr Nat.bit 0)
        target w=(rows.map Prod.fst).foldr Nat.bit 0) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, x4 + x3 ∉ x1}; have x3 : List (Bool × List Bool) := List.flatMap (fun (x3 : Fin (13 : ℕ)) => List.map (fun (x4 : Fin (13 : ℕ)) => (Bool.true, PEqualNP.GenericRejection.incidenceInput {x3} {x4 - x3})) [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))]) (List.finRange (13 : ℕ)); have x4 : List (Finset (Fin (13 : ℕ))) := List.flatMap (fun (x4 : ℕ) => List.map List.toFinset (List.sublistsLen x4 (List.finRange (13 : ℕ)))) (List.range (4 : ℕ)); have x5 : List (Bool × List Bool) := List.flatMap (fun (x5 : Finset (Fin (13 : ℕ))) => [(Bool.false, PEqualNP.GenericRejection.incidenceInput x5 (x2 x5)), (Bool.false, PEqualNP.GenericRejection.incidenceInput (x2 x5) x5)]) x4; have x6 : List (Bool × List Bool) := x3 ++ x5; have x7 : List ℕ := List.ofFn fun (x7 : Fin (26 : ℕ)) => List.foldr Nat.bit (0 : ℕ) (List.map (fun (x8 : Bool × List Bool) => x8.2.getD (↑x7) Bool.false) x6); ∃ (x8 : List (Bool × ℕ × ℕ)) (x9 : Bool × ℕ × ℕ), x8.length ≤ (63 : ℕ) ∧ x8.head? = Option.some x9 ∧ x9 ∈ [(Bool.false, (0 : ℕ), (13 : ℕ)), (Bool.true, (0 : ℕ), (1 : ℕ)), (Bool.true, (0 : ℕ), (13 : ℕ)), (Bool.true, (2 : ℕ), (13 : ℕ))] ∧ (List.foldl (fun (x10 : List ℕ) (x11 : Bool × ℕ × ℕ) => x10 ++ [if x11.1 = Bool.true then x10.getD x11.2.1 (0 : ℕ) ||| x10.getD x11.2.2 (0 : ℕ) else x10.getD x11.2.1 (0 : ℕ) &&& x10.getD x11.2.2 (0 : ℕ)]) x7 x8).getLastD (0 : ℕ) = List.foldr Nat.bit (0 : ℕ) (List.map Prod.fst x6) := by
  classical
  let D : Finset (Fin 13) := {0,1,3,9}
  let disj := fun S : Finset (Fin 13) => Finset.univ.filter (fun l : Fin 13 => ∀ p∈S,p+l∉D)
  let pos := (List.finRange 13).flatMap (fun p => ([0,1,3,9] : List (Fin 13)).map (fun d =>
    (true,incidenceInput {p} {d-p})))
  let sets := (List.range 4).flatMap (fun n => ((List.finRange 13).sublistsLen n).map List.toFinset)
  let neg := sets.flatMap (fun S => [(false,incidenceInput S (disj S)),(false,incidenceInput (disj S) S)])
  let rows := pos++neg
  let w := List.ofFn (fun i : Fin 26 => (rows.map (fun r => r.2.getD i.val false)).foldr Nat.bit 0)
  let hit := fun (x : List Bool) => (List.range 13).any (fun j =>
        x.getD (13+j) false && ([0,1,3,9] : List ℕ).any (fun d => x.getD ((d+13-j)%13) false))
  let target := fun (w : List ℕ) => ((List.range 13).map (fun j =>
        w.getD (13+j) 0 &&& (([0,1,3,9] : List ℕ).map (fun d => w.getD ((d+13-j)%13) 0)).foldl (· ||| ·) 0)).foldl (· ||| ·) 0
  let step := fun (w : List ℕ) (g : Bool × ℕ × ℕ) => w ++ [if g.1 then
        w.getD g.2.1 0 ||| w.getD g.2.2 0 else w.getD g.2.1 0 &&& w.getD g.2.2 0]
  obtain ⟨extra,tail,_,_,short,works⟩ := patch
  let front := (List.range 8).flatMap (fun i =>
        let j := ((0::extra).getD i 0).val
        let p := fun d : ℕ => (d+13-j)%13
        let k := 26+(5*i-1)
        ([(true,p 0,p 1),(true,p 3,p 9),(true,k,k+1),(false,13+j,k+2)] : List (Bool × ℕ × ℕ)) ++
          if i=0 then [] else [(true,k-1,k+3)])
  change ∀ xs : List ℕ,xs.length=26 → (tail.foldl step (front.foldl step xs)).getLastD 0=target xs at works
  have len : front.length=39 := by rfl
  have lead : (front++tail).head?=some (true,0,1) := by
    change some (true,(0+13-((0::extra).getD 0 0).val)%13,(1+13-((0::extra).getD 0 0).val)%13)=some (true,0,1)
    rw [show (0::extra).getD 0 0=0 by simp]
    rfl
  have decode (A B : Finset (Fin 13)) :
      hit (incidenceInput A B)=true ↔ ∃ p∈A,∃ l∈B,p+l∈D := by
    have pt (p : Fin 13) :
        (incidenceInput A B).getD p.val false=decide (p∈A) := by
      fin_cases p <;> rfl
    have li (l : Fin 13) :
        (incidenceInput A B).getD (13+l.val) false=decide (l∈B) := by
      fin_cases l <;> rfl
    have sub (d l : Fin 13) : (d.val+13-l.val)%13=(d-l).val := by
      revert d l
      decide +kernel
    have offsets (d : Fin 13) : d∈D ↔ d.val∈([0,1,3,9] : List ℕ) := by
      revert d
      decide +kernel
    change (List.range 13).any _=true ↔ _
    rw [List.any_eq_true]
    constructor
    · rintro ⟨j,hj,h⟩
      let l : Fin 13 := ⟨j,List.mem_range.mp hj⟩
      change (_ && _)=true at h
      rw [Bool.and_eq_true] at h
      obtain ⟨hl,inside⟩ := h
      rw [List.any_eq_true] at inside
      obtain ⟨d,hd,hp⟩ := inside
      have small : d<13 := by simp at hd;omega
      let off : Fin 13 := ⟨d,small⟩
      have eqn := sub off l
      change (d+13-j)%13=(off-l).val at eqn
      rw [eqn,pt] at hp
      have validL : l∈B := of_decide_eq_true ((li l).symm.trans hl)
      exact ⟨off-l,of_decide_eq_true hp,l,validL,by simpa using (offsets off).mpr hd⟩
    · rintro ⟨p,hp,l,hl,hd⟩
      refine ⟨l.val,List.mem_range.mpr l.isLt,?_⟩
      rw [Bool.and_eq_true]
      refine ⟨(li l).trans (decide_eq_true hl),List.any_eq_true.mpr ?_⟩
      refine ⟨(p+l).val,(offsets _).mp hd,?_⟩
      rw [sub,add_sub_cancel_right,pt]
      exact decide_eq_true hp
  have valid : ∀ r∈rows,r.1=hit r.2 := by
    intro r hr
    rcases List.mem_append.mp hr with positive|negative
    · obtain ⟨p,_,m⟩ := List.mem_flatMap.mp positive
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp m
      apply Eq.symm
      apply (decode _ _).mpr
      refine ⟨p,Finset.mem_singleton_self _,d-p,Finset.mem_singleton_self _,?_⟩
      have mem : d∈D := by simpa [D] using hd
      simpa [add_comm] using mem
    · obtain ⟨S,_,hm⟩ := List.mem_flatMap.mp negative
      rcases (show r=(false,incidenceInput S (disj S)) ∨ r=(false,incidenceInput (disj S) S) by simpa using hm) with rfl|rfl
      · apply Eq.symm
        apply Bool.eq_false_iff.mpr
        rintro hh
        obtain ⟨p,hp,l,hl,edge⟩ := (decode _ _).mp hh
        exact (Finset.mem_filter.mp hl).2 p hp edge
      · apply Eq.symm
        apply Bool.eq_false_iff.mpr
        rintro hh
        obtain ⟨p,hp,l,hl,edge⟩ := (decode _ _).mp hh
        exact (Finset.mem_filter.mp hp).2 l hl (by simpa [add_comm] using edge)
  have packed : target w=(rows.map Prod.fst).foldr Nat.bit 0 := packLines rows valid
  refine ⟨front++tail,(true,0,1),?_,lead,by decide,?_⟩
  · rw [List.length_append,len]
    omega
  · change ((front++tail).foldl step w).getLastD 0=(rows.map Prod.fst).foldr Nat.bit 0
    rw [List.foldl_append]
    exact (works w (by simp [w])).trans packed
