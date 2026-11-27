import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_7105_43
    (deleted : let A : List (BitVec 24) := [0,16777215,6852617,9715731,2203718,938500,3174560,222472,755760,13369792,15732224]
      ∀ P : List (BitVec 24), P.length ≤ 15 →
        (∀ i : Fin P.length, let U := A ++ P.take i.val
          ∃ a ∈ U, ∃ b ∈ U, P.get i = a &&& b ∨ P.get i = a ||| b) →
        (4095 : BitVec 24) ∉ P)
    (identified : let A : List (BitVec 25) := [0,33554431,8421463,23347233,5046538,3295244,4407952,1807392,3940544,27264768,29374464]
      ∀ P : List (BitVec 25), P.length ≤ 15 →
        (∀ i : Fin P.length, let U := A ++ P.take i.val
          ∃ a ∈ U, ∃ b ∈ U, P.get i = a &&& b ∨ P.get i = a ||| b) →
        (16383 : BitVec 25) ∉ P)
    (joint : let B := ([(0,0),(8796093022207,1073741823),(2207636148480,318767104),(6120337154624,157847561),(2207635996672,9715731),(1322919672136,69312582),(863828477569,101601796),(1155518180896,808480928),(473796971924,134440200),(1032990015938,537626672),(7147295588408,13369792),(7700339699719,15732224),(2207636148480,328482835)] : List (Nat × Nat)).map (fun t => ((BitVec.ofNat 73 t.1) <<< 30) ||| BitVec.ofNat 73 t.2)
      let count (L : List (BitVec 73)) (offset width : Nat) :=
        let f := fun w : BitVec 73 => w.extractLsb' offset width
        (((L.map f).toFinset) \ ((B.map f).toFinset)).card
      ∀ L : List (BitVec 73), L.length ≤ 18 →
        (∀ i : Fin L.length, let U := B ++ L.take i.val
          ∃ a ∈ U, ∃ b ∈ U, L.get i = a &&& b ∨ L.get i = a ||| b) →
        16 ≤ count L 0 24 → 16 ≤ count L 24 24 → 16 ≤ count L 48 25 →
        (((4294705215 : BitVec 73) <<< 30) ||| 1056968703) ∉ L) :
    (have x1 : List (Fin (10 : ℕ) × Fin (10 : ℕ)) := [((0 : Fin (10 : ℕ)), (1 : Fin (10 : ℕ))), ((1 : Fin (10 : ℕ)), (2 : Fin (10 : ℕ))), ((2 : Fin (10 : ℕ)), (3 : Fin (10 : ℕ))), ((3 : Fin (10 : ℕ)), (4 : Fin (10 : ℕ))), ((4 : Fin (10 : ℕ)), (0 : Fin (10 : ℕ))), ((0 : Fin (10 : ℕ)), (5 : Fin (10 : ℕ))), ((1 : Fin (10 : ℕ)), (6 : Fin (10 : ℕ))), ((2 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ))), ((3 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ))), ((4 : Fin (10 : ℕ)), (9 : Fin (10 : ℕ))), ((5 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ))), ((7 : Fin (10 : ℕ)), (9 : Fin (10 : ℕ))), ((9 : Fin (10 : ℕ)), (6 : Fin (10 : ℕ))), ((6 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ))), ((8 : Fin (10 : ℕ)), (5 : Fin (10 : ℕ)))]; ∀ (x2 : List ((Fin (10 : ℕ) → Bool) → Bool)),   x2.length ≤ (18 : ℕ) →     (∀ (x4 : Fin x2.length),         have x5 : List ((Fin (10 : ℕ) → Bool) → Bool) := ((fun (x5 : Fin (10 : ℕ) → Bool) => Bool.false) :: (fun (x5 : Fin (10 : ℕ) → Bool) => Bool.true) :: List.ofFn fun (x5 : Fin (10 : ℕ)) (x6 : Fin (10 : ℕ) → Bool) => x6 x5) ++ [fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ))] ++ List.take (↑x4) x2;         x2.get x4 ∉ x5 ∧ ∃ x6 ∈ x5, ∃ x7 ∈ x5, (x2.get x4 = fun (x8 : Fin (10 : ℕ) → Bool) => x6 x8 && x7 x8) ∨ x2.get x4 = fun (x8 : Fin (10 : ℕ) → Bool) => x6 x8 || x7 x8) →       (∀ x5 ∈ x2,           ∀ (x7 x8 : Fin (10 : ℕ)),             x7 ≠ x8 →               have x10 : Prop := (x1.any fun (x10 : Fin (10 : ℕ) × Fin (10 : ℕ)) => Decidable.decide ((x7, x8) = x10 ∨ (x8, x7) = x10)) = Bool.true;               (¬x10 → x5 ≠ fun (x12 : Fin (10 : ℕ) → Bool) => x12 x7 && x12 x8) ∧ (x10 → x5 ≠ fun (x12 : Fin (10 : ℕ) → Bool) => x12 x7 || x12 x8)) →         (fun (x6 : Fin (10 : ℕ) → Bool) => x1.any fun (x7 : Fin (10 : ℕ) × Fin (10 : ℕ)) => x6 x7.1 && x6 x7.2) ∉ x2) := by
  let E : List (Fin 10 × Fin 10) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
  let roots : List ((Fin 10 → Bool) → Bool) := ((fun _ => false) :: (fun _ => true) :: List.ofFn (fun (i : Fin 10) (x : Fin 10 → Bool) => x i)) ++ [fun x => x 0 || x 2]
  let F := fun x : Fin 10 → Bool => E.any (fun e => x e.1 && x e.2)
  let B : List (BitVec 73) := ([(0,0),(8796093022207,1073741823),(2207636148480,318767104),(6120337154624,157847561),(2207635996672,9715731),(1322919672136,69312582),(863828477569,101601796),(1155518180896,808480928),(473796971924,134440200),(1032990015938,537626672),(7147295588408,13369792),(7700339699719,15732224),(2207636148480,328482835)] : List (Nat × Nat)).map (fun t => ((BitVec.ofNat 73 t.1) <<< 30) ||| BitVec.ofNat 73 t.2)
  let A : List (BitVec 24) := [0,16777215,6852617,9715731,2203718,938500,3174560,222472,755760,13369792,15732224]
  let J : List (BitVec 25) := [0,33554431,8421463,23347233,5046538,3295244,4407952,1807392,3940544,27264768,29374464]
  let goal : BitVec 73 := (((4294705215 : BitVec 73) <<< 30) ||| 1056968703)
  let samples : Array Nat := #[6,12,24,66,132,160,264,288,320,528,576,640,50,104,116,138,200,208,276,402,548,554,770,772,3,17,24,66,33,160,528,640,576,264,320,288,138,208,201,50,112,104,521,554,385,402,770,769,7,13,21,24,37,66,133,160,264,288,320,528,576,640,50,69,104,112,138,200,208,402,554,773,770]
  let row (r : Fin 73) (i : Fin 10) := (samples[r.val]!).testBit i.val
  let obs (f : (Fin 10 → Bool) → Bool) : BitVec 73 :=
    (BitVec.ofBoolListLE (List.ofFn (fun r : Fin 73 => f (row r)))).cast (by simp)
  let legal {α : Type} (m j : α → α → α) (raw P : List α) :=
    ∀ i : Fin P.length, let U := raw ++ P.take i.val
      ∃ a ∈ U, ∃ b ∈ U, P.get i = m a b ∨ P.get i = j a b
  have mapRun {α β : Type} (m j : α → α → α) (m' j' : β → β → β)
      (f : α → β) (hm : ∀ a b, f (m a b)=m' (f a) (f b)) (hj : ∀ a b, f (j a b)=j' (f a) (f b))
      (raw : List α) (base : List β) (incl : ∀ t ∈ raw, f t ∈ base)
      (P : List α) (h : legal m j raw P) : legal m' j' base (P.map f) := by
    intro i
    let k : Fin P.length := ⟨i.val,by simpa using i.isLt⟩
    obtain ⟨a,ha,b,hb,eq⟩ := h k
    have lift (x : α) (hx : x ∈ raw++P.take k.val) : f x ∈ base++(P.map f).take i.val := by
      apply List.mem_append.mpr
      rcases List.mem_append.mp hx with hr|hp
      · exact Or.inl (incl x hr)
      · right; rw [←List.map_take]; exact List.mem_map_of_mem hp
    refine ⟨f a,lift a ha,f b,lift b hb,?_⟩
    have ev : (P.map f).get i=f (P.get k) := List.getElem_map f
    rw [ev]
    exact eq.imp (fun e => (congrArg f e).trans (hm a b)) (fun e => (congrArg f e).trans (hj a b))
  have addGate {α : Type} (m j : α→α→α) (raw Q : List α) (ok : legal m j raw Q) (z : α)
      (gen : ∃ a∈raw++Q, ∃ b∈raw++Q, z=m a b ∨ z=j a b) : legal m j raw (Q++[z]) := by
    intro i
    by_cases early : i.val<Q.length
    · obtain ⟨a,ha,b,hb,he⟩ := ok ⟨i.val,early⟩
      have eq : (Q++[z]).get i = Q[i.val] := List.getElem_append_left early
      simpa only [List.take_append_of_le_length (Nat.le_of_lt early),eq] using
        (show ∃ a∈raw++Q.take i.val, ∃ b∈raw++Q.take i.val, Q[i.val]=m a b ∨ Q[i.val]=j a b from ⟨a,ha,b,hb,he⟩)
    · have li := i.isLt
      simp only [List.length_append,List.length_cons,List.length_nil] at li
      have last : i.val=Q.length := by omega
      have eq : (Q++[z]).get i = z := by
        change (Q++[z])[i.val]=z
        rw [List.getElem_append_right (by omega)]
        simp [last]
      simpa only [eq,last,List.take_left] using gen
  have compress {α : Type} [DecidableEq α] (m j : α→α→α) (raw P : List α)
      (ok : legal m j raw P) : ∃ Q : List α, legal m j raw Q ∧
        (∀ w∈raw++P, w∈raw++Q) ∧ Q.length ≤ (P.toFinset \ raw.toFinset).card := by
    have grow (t : Nat) (bound : t≤P.length) : ∃ Q : List α, legal m j raw Q ∧ Q.Nodup ∧
        (∀ w∈Q, w∈P ∧ w∉raw) ∧ (∀ w∈raw++P.take t, w∈raw++Q) := by
      induction t with
      | zero =>
        exact ⟨[],by intro i; exact Fin.elim0 i,by simp,by simp,by simp⟩
      | succ t ih =>
        obtain ⟨Q,hq,nd,src,prior⟩ := ih (by omega)
        let z := P[t]
        have take : P.take (t+1)=P.take t++[z] := List.take_succ_eq_append_getElem (by omega)
        have lift (W : List α) (zW : z ∈ W) (inc : ∀ w∈raw++Q, w∈W) :
            ∀ w∈raw++P.take (t+1), w∈W := by
          intro w hw
          rw [take,←List.append_assoc] at hw
          rcases List.mem_append.mp hw with ho|he
          · exact inc w (prior w ho)
          · exact (List.mem_singleton.mp he) ▸ zW
        by_cases dup : z∈raw++Q
        · exact ⟨Q,hq,nd,src,lift _ dup (fun _ h => h)⟩
        · obtain ⟨a,ha,b,hb,eq⟩ := ok ⟨t,by omega⟩
          have nr : z∉raw := fun h => dup (List.mem_append.mpr (Or.inl h))
          have nq : z∉Q := fun h => dup (List.mem_append.mpr (Or.inr h))
          refine ⟨Q++[z],addGate m j raw Q hq z ⟨a,prior a ha,b,prior b hb,eq⟩,?_,?_,?_⟩
          · simp [List.nodup_append,nd]
            rintro a ha rfl
            exact nq ha
          · intro w hw
            rcases List.mem_append.mp hw with h|h
            · exact src w h
            · obtain rfl := List.mem_singleton.mp h
              exact ⟨List.getElem_mem _,nr⟩
          · apply lift
            · simp
            · intro w hw
              rw [←List.append_assoc]
              exact List.mem_append.mpr (Or.inl hw)
    obtain ⟨Q,valid,nd,src,all⟩ := grow P.length le_rfl
    refine ⟨Q,valid,by simpa using all,?_⟩
    have small : Q.toFinset ⊆ P.toFinset \ raw.toFinset := by
      intro w hw
      obtain ⟨hp,hr⟩ := src _ (List.mem_toFinset.mp hw)
      exact Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hp,fun h => hr (List.mem_toFinset.mp h)⟩
    simpa only [List.toFinset_card_of_nodup nd] using Finset.card_le_card small
  have bit (f : (Fin 10→Bool)→Bool) (r : Fin 73) : (obs f).getLsbD r.val=f (row r) := by
    let bits := List.ofFn (fun r : Fin 73 => f (row r))
    have h : r.val < bits.length := by simpa only [bits,List.length_ofFn] using r.isLt
    change (BitVec.ofBoolListLE bits).getLsbD r.val = _
    rw [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem _ _ h]
    exact List.getElem_ofFn (f:=fun i : Fin 73 => f (row i)) h
  have obsM (f g : (Fin 10→Bool)→Bool) : obs (fun x => f x && g x) = obs f &&& obs g := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have r := bit (fun x => f x && g x) ⟨i,hi⟩
    simpa only [BitVec.getLsbD_and,bit f ⟨i,hi⟩,bit g ⟨i,hi⟩] using r
  have obsJ (f g : (Fin 10→Bool)→Bool) : obs (fun x => f x || g x) = obs f ||| obs g := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have r := bit (fun x => f x || g x) ⟨i,hi⟩
    simpa only [BitVec.getLsbD_or,bit f ⟨i,hi⟩,bit g ⟨i,hi⟩] using r
  have rootsMatch : roots.map obs=B := by decide +kernel
  have goalMatch : obs F=goal := by decide +kernel
  intro E0 P budget gate _ safe
  have sameEdges : E0 = E := rfl
  subst E0
  have original : legal (fun f g x => f x && g x) (fun f g x => f x || g x) roots P :=
    fun i => (gate i).2
  let L := P.map obs
  let meet := fun a b : BitVec 73 => a &&& b
  let join := fun a b : BitVec 73 => a ||| b
  have inRoots (t : (Fin 10→Bool)→Bool) (ht : t∈roots) : obs t∈B :=
    (congrArg (fun ws : List (BitVec 73) => obs t∈ws) rootsMatch).mp (List.mem_map_of_mem (f:=obs) ht)
  have run : legal meet join B L := by
    change legal meet join B (P.map obs)
    with_reducible exact (@mapRun ((Fin 10 → Bool) → Bool) (BitVec 73) (fun f g x => f x && g x) (fun f g x => f x || g x) meet join obs obsM obsJ roots B inRoots P original)
  have observed : obs F∈L := List.mem_map_of_mem (f:=obs) (show F∈P from safe)
  have hit : goal∈L := (congrArg (fun w : BitVec 73 => w∈L) goalMatch).mp observed
  have bound : L.length≤18 := by simpa [L] using budget
  have slice {w : Nat} (start : Nat) (V : List (BitVec w)) (tg : BitVec w) (k : Nat)
      (rootsEq : (B.map (fun y => y.extractLsb' start w)).toFinset=V.toFinset)
      (goalEq : goal.extractLsb' start w=tg) (fresh : tg∉V)
      (hyp : ∀ Q : List (BitVec w), Q.length≤k →
        legal (fun a b => a &&& b) (fun a b => a ||| b) V Q → tg∉Q) :
      k+1 ≤ (((L.map (fun y => y.extractLsb' start w)).toFinset) \
        ((B.map (fun y => y.extractLsb' start w)).toFinset)).card := by
    let f := fun y : BitVec 73 => y.extractLsb' start w
    have incl (t : BitVec 73) (ht : t∈B) : f t∈V := by
      apply List.mem_toFinset.mp
      rw [←rootsEq]; exact List.mem_toFinset.mpr (List.mem_map_of_mem ht)
    have ok := mapRun meet join (fun a b => a &&& b) (fun a b => a ||| b) f
      (fun _ _ => BitVec.extractLsb'_and) (fun _ _ => BitVec.extractLsb'_or) B V incl L run
    obtain ⟨Q,q,inc,num⟩ := compress _ _ V (L.map f) ok
    have projected : f goal∈L.map f := List.mem_map_of_mem (f:=f) hit
    have witness := (congrArg (fun w : BitVec _ => w∈L.map f) goalEq).mp projected
    have existsQ := inc tg (List.mem_append.mpr (Or.inr witness))
    have yes := (List.mem_append.mp existsQ).resolve_left fresh
    have big : k<Q.length := by
      by_contra! small
      exact hyp Q small q yes
    rw [rootsEq]
    exact Nat.le_trans big num
  have left := slice 0 A 4095 15 (by decide +kernel) (by decide +kernel) (by decide +kernel) deleted
  have right := slice 24 A 4095 15 (by decide +kernel) (by decide +kernel) (by decide +kernel) deleted
  have same := slice 48 J 16383 15 (by decide +kernel) (by decide +kernel) (by decide +kernel) identified
  exact joint L bound run left right same hit
