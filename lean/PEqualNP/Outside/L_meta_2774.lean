import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2774.Tree

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Finset
open Relation (ReflTransGen)

-- The list evaluation and OR tree lemmas are adapted from the checked L_meta_540.

def stW (w : List Bool) (g : Gate) : List Bool :=
 w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def wV (n : ℕ) (C : Circuit) (x : Fin n->Bool) (w : ℕ) : Bool :=
 (C.wires (List.ofFn x)).getD w false
lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
 C.wires x=C.gates.foldl stW x:=rfl
lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
 (gs.foldl stW w).length=w.length+gs.length:=by
 induction gs generalizing w with
 | nil => simp
 | cons g gs ih =>
  rw [List.foldl_cons,ih]
  simp [stW]
  omega
lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
 (gs.foldl stW w).getD i false=w.getD i false:=by
 induction gs generalizing w with
 | nil => rfl
 | cons g gs ih =>
  simp only [List.foldl_cons]
  have hlt : i < (stW w g).length:=by simp [stW];omega
  rw [ih (stW w g) hlt]
  simp [stW,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length<=i) :
 w.getD i false=false:=by
 simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none hi]
lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n->Bool) :
 (C.wires (List.ofFn x)).length=n+C.gates.length:=by
 rw [wires_eq_foldl,foldl_stepWire_length,List.length_ofFn]
lemma wvO (n : ℕ) (C : Circuit) (x : Fin n->Bool) :
 wV n C x C.output=circuitFun n C x:=rfl
lemma wvI (n : ℕ) (C : Circuit) (x : Fin n->Bool) (i : Fin n) :
 wV n C x i.val=x i:=by
 unfold wV
 rw [wires_eq_foldl,foldl_stepWire_getD_lt C.gates (List.ofFn x) i.val (by simp)]
 simp [List.getD_eq_getElem?_getD]
lemma wireVal_ge (n : ℕ) (C : Circuit) (x : Fin n->Bool) (w : ℕ)
 (hw : n+C.gates.length<=w) : wV n C x w=false:=by
 unfold wV
 exact getD_ge_length _ _ (by rw [wires_length];exact hw)
lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
 ∃ (pre post : List Gate) (gj : Gate),
  gs=pre ++ gj :: post/\pre.length=j/\gs[j]'hj=gj:=by
 refine ⟨gs.take j,gs.drop (j+1),gs[j]'hj,?_,by simp;omega,rfl⟩
 rw [List.cons_getElem_drop_succ,List.take_append_drop]
lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
 gateAt C j=C.gates[j]'hj:=by
 simp [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
lemma wireVal_gate (n : ℕ) (C : Circuit) (x : Fin n->Bool) (j : ℕ)
 (hj : j < C.gates.length) :
 wV n C x (n+j) =
  (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
   if i < n+j then wV n C x i else false):=by
 obtain ⟨pre,post,gj,hgs,hpre_len,hget⟩:=split_gates C.gates j hj
 have hgj : gateAt C j=gj:=by rw [gateAt_eq_getElem C j hj,hget]
 rw [hgj]
 let w0:=pre.foldl stW (List.ofFn x)
 have hW0L : w0.length=n+j:=by
  simp [w0,foldl_stepWire_length,hpre_len]
 have hCj : wV n C x (n+j)=gj.op.eval (gj.inputs.map fun i => w0.getD i false):=by
  unfold wV
  rw [wires_eq_foldl,hgs,List.foldl_append,List.foldl_cons]
  rw [foldl_stepWire_getD_lt post (stW w0 gj) (n+j) (by simp [stW];omega)]
  simp [stW,List.getD_eq_getElem?_getD,hW0L]
 rw [hCj]
 congr 1
 refine List.map_congr_left fun i _ => ?_
 by_cases hi : i < n+j
 . rw [if_pos hi]
   unfold wV
   rw [wires_eq_foldl,hgs,List.foldl_append]
   exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
 . rw [if_neg hi]
   exact getD_ge_length w0 i (by omega)
lemma wvGR (n : ℕ) (C : Circuit) (hrb : ReadsBack n C)
 (x : Fin n->Bool) (j : ℕ) (hj : j < C.gates.length) :
 wV n C x (n+j) =
  (gateAt C j).op.eval ((gateAt C j).inputs.map (wV n C x)):=by
 rw [wireVal_gate n C x j hj]
 congr 1
 refine List.map_congr_left fun i hi => ?_
 rw [if_pos (hrb j hj i hi)]

lemma length_eq_sum_count (l : List ℕ) (S : Finset ℕ) (h : ∀ i ∈ l,i ∈ S) :
 l.length=∑ w ∈ S,l.count w:=by
 induction l with
 | nil => simp
 | cons a l ih =>
  have ha : a ∈ S:=h a (by simp)
  have ih':=ih (fun i hi => h i (by simp [hi]))
  simp only [List.length_cons,List.count_cons,sum_add_distrib]
  rw [← ih']
  simp [ha]
lemma tree_card (n : ℕ) (C : Circuit) (G L : Finset ℕ) (ρ : ℕ)
 (h : IsOrTree n C G L ρ) : L.card=G.card+1:=by
 obtain ⟨hg,hl,hgg,hroot⟩:=h
 by_cases hG : G=∅
 . rw [if_pos hG] at hroot
   rw [hroot,hG]
   simp
 . rw [if_neg hG] at hroot
   obtain ⟨j0,hj0,hρ⟩:=hroot
   have hρL : ρ ∉ L:=by
    intro hin
    apply (hl ρ hin).1
    rw [hρ]
    exact ⟨Nat.le_add_right _ _,by simpa using hj0⟩
   have hdisj : Disjoint L (G.image (fun k => n+k)):=by
    rw [disjoint_left]
    intro w hw hw'
    obtain ⟨k,hk,rfl⟩:=mem_image.mp hw'
    apply (hl _ hw).1
    exact ⟨Nat.le_add_right _ _,by simpa using hk⟩
   have hsum : ∑ j ∈ G,(gateAt C j).inputs.length=2 * G.card:=by
    rw [sum_congr rfl (fun j hj => (hg j hj).2.1)]
    simp [Nat.mul_comm]
   have hlen : ∀ j ∈ G,(gateAt C j).inputs.length
    = ∑ w ∈ L ∪ G.image (fun k => n+k),(gateAt C j).inputs.count w:=by
    intro j hj
    apply length_eq_sum_count
    intro i hi
    rcases (hg j hj).2.2 i hi with h1 | ⟨h1,h2⟩
    . exact mem_union_left _ h1
    . apply mem_union_right
      exact mem_image.mpr ⟨i - n,h2,by omega⟩
   have h1 : ∑ j ∈ G,(gateAt C j).inputs.length
    = ∑ w ∈ L ∪ G.image (fun k => n+k),readsIn C G w:=by
    rw [sum_congr rfl hlen,Finset.sum_comm]
    rfl
   have h2 : ∑ w ∈ L,readsIn C G w=L.card:=by
    rw [sum_congr rfl (fun w hw => (hl w hw).2)]
    rw [sum_congr rfl (fun w hw => if_neg (fun (e : w=ρ) => hρL (e ▸ hw)))]
    simp
   have h3 : ∑ w ∈ G.image (fun k => n+k),readsIn C G w+1=G.card:=by
    rw [sum_image (fun a _ b _ hab => by omega)]
    rw [sum_congr rfl (fun k hk => hgg k hk)]
    have e : ∀ k ∈ G,(if n+k=ρ then 0 else 1)=(if k=j0 then 0 else 1):=by
     intro k _
     by_cases hk : k=j0
     . simp [hk,hρ]
     . have : n+k ≠ ρ:=by omega
       simp [hk,this]
    rw [sum_congr rfl e]
    rw [← Finset.add_sum_erase G _ hj0]
    rw [sum_congr rfl (fun k hk => if_neg (Finset.ne_of_mem_erase hk))]
    simp only [if_true,sum_const,smul_eq_mul,Nat.mul_one,Nat.zero_add]
    have:=card_erase_add_one hj0
    omega
   rw [h1,Finset.sum_union hdisj,h2] at hsum
   omega
def OrStep (n : ℕ) (C : Circuit) (G : Finset ℕ) (u v : ℕ) : Prop :=
 ∃ j ∈ G,u=n+j/\v ∈ (gateAt C j).inputs
def OrReach (n : ℕ) (C : Circuit) (G : Finset ℕ) : ℕ->ℕ->Prop :=
 Relation.ReflTransGen (OrStep n C G)
lemma rInP (C : Circuit) (G : Finset ℕ) (w : ℕ) :
 0 < readsIn C G w↔∃ j ∈ G,w ∈ (gateAt C j).inputs:=by
 unfold readsIn
 rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
 constructor
 . rintro ⟨j,hj,hpos⟩
   exact ⟨j,hj,List.count_pos_iff.mp hpos⟩
 . rintro ⟨j,hj,hmem⟩
   exact ⟨j,hj,List.count_pos_iff.mpr hmem⟩

lemma otRR {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
 (hrb : ReadsBack n C) (hG : ∀ j ∈ G,j < C.gates.length)
 (ht : IsOrTree n C G L ρ) {w : ℕ} (hw : w ∈ L\/(n<=w/\w - n ∈ G)) :
 OrReach n C G ρ w:=by
 by_cases hEq0 : w=ρ
 . subst hEq0;exact ReflTransGen.refl
 have hbound : w<=n+C.gates.length:=by
  rcases hw with hwL | ⟨hwn,hwG⟩
  . have hr : readsIn C G w=1:=by rw [(ht.2.1 w hwL).2,if_neg hEq0]
    obtain ⟨j,hj,hmem⟩:=(rInP C G w).mp (by omega)
    have:=hrb j (hG j hj) w hmem
    have:=hG j hj
    omega
  . have:=hG (w - n) hwG;omega
 clear hEq0
 generalize hk : n+C.gates.length - w=k
 induction k using Nat.strong_induction_on generalizing w with
 | ind k ih =>
  by_cases hEq : w=ρ
  . subst hEq;exact ReflTransGen.refl
  . have hr : readsIn C G w=1:=by
     rcases hw with hwL | ⟨hwn,hwG⟩
     . rw [(ht.2.1 w hwL).2,if_neg hEq]
     . have hweq : n+(w - n)=w:=by omega
       have h:=ht.2.2.1 (w - n) hwG
       rw [hweq] at h;rw [h,if_neg hEq]
    obtain ⟨j,hj,hmem⟩:=(rInP C G w).mp (by omega)
    have hlt : w < n+j:=hrb j (hG j hj) w hmem
    have hjlt:=hG j hj
    have hreach_j : OrReach n C G ρ (n+j) :=
     ih (n+C.gates.length - (n+j)) (by omega) (Or.inr ⟨by omega,by simpa using hj⟩)
      (by omega) rfl
    exact ReflTransGen.tail hreach_j ⟨j,hj,rfl,hmem⟩
lemma otER {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
 (hrb : ReadsBack n C) (hG : ∀ j ∈ G,j < C.gates.length)
 (ht : IsOrTree n C G L ρ) (x : Fin n->Bool) {u v : ℕ}
 (hreach : OrReach n C G u v) (hv : wV n C x v=true) :
 wV n C x u=true:=by
 induction hreach with
 | refl => exact hv
 | tail h1 hstep ih =>
  apply ih
  obtain ⟨j,hj,rfl,hmem⟩:=hstep
  rw [wvGR n C hrb x j (hG j hj),(ht.1 j hj).1]
  simp only [GateOp.eval,List.any_eq_true]
  exact ⟨true,List.mem_map.mpr ⟨_,hmem,hv⟩,rfl⟩
lemma otEI {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
 (hrb : ReadsBack n C) (hG : ∀ j ∈ G,j < C.gates.length)
 (ht : IsOrTree n C G L ρ) (x : Fin n->Bool) {u : ℕ}
 (hu : u ∈ L\/(n<=u/\u - n ∈ G)) :
 wV n C x u=true↔∃ l ∈ L,OrReach n C G u l/\wV n C x l=true:=by
 constructor
 . intro htrue
   induction u using Nat.strong_induction_on with
   | ind u ih =>
    rcases hu with huL | ⟨hun,huG⟩
    . exact ⟨u,huL,ReflTransGen.refl,htrue⟩
    . have hj : u - n < C.gates.length:=hG (u - n) huG
      have hueq : n+(u - n)=u:=by omega
      rw [← hueq,wvGR n C hrb x (u - n) hj,(ht.1 (u - n) huG).1] at htrue
      simp only [GateOp.eval,List.any_eq_true,List.mem_map,id_eq] at htrue
      obtain ⟨_,⟨v,hvmem,hvt⟩,rfl⟩:=htrue
      have hvlt : v < u:=by have:=hrb (u - n) hj v hvmem;omega
      have hvnode : v ∈ L\/(n<=v/\v - n ∈ G):=(ht.1 (u - n) huG).2.2 v hvmem
      obtain ⟨l,hlL,hlreach,hlt⟩:=ih v hvlt hvnode hvt
      exact ⟨l,hlL,ReflTransGen.head ⟨u - n,huG,hueq.symm,hvmem⟩ hlreach,hlt⟩
 . rintro ⟨l,_,hreach,hlt⟩
   exact otER hrb hG ht x hreach hlt
lemma otRE {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
 (hrb : ReadsBack n C) (hG : ∀ j ∈ G,j < C.gates.length)
 (ht : IsOrTree n C G L ρ) (x : Fin n->Bool) :
 wV n C x ρ=true↔∃ l ∈ L,wV n C x l=true:=by
 have hρnode : ρ ∈ L\/(n <= ρ /\ ρ - n ∈ G):=by
  by_cases hGe : G=∅
  . have h:=ht.2.2.2;rw [if_pos hGe] at h;left;rw [h];simp
  . have h:=ht.2.2.2;rw [if_neg hGe] at h
    obtain ⟨j,hj,rfl⟩:=h;right;exact ⟨by omega,by simpa using hj⟩
 rw [otEI hrb hG ht x hρnode]
 constructor
 . rintro ⟨l,hlL,_,hlt⟩;exact ⟨l,hlL,hlt⟩
 . rintro ⟨l,hlL,hlt⟩;exact ⟨l,hlL,otRR hrb hG ht (Or.inl hlL),hlt⟩

theorem specs (n : ℕ) (C : Circuit) (T L : Finset ℕ)
    (hRB : ReadsBack n C) (hTree : IsOrTree n C T L C.output)
    (hLcard : 2 ≤ L.card) :
    T.card + 1 = L.card ∧
      (∀ k ∈ T, k < C.size) ∧
      (∀ i ∈ L, i < n + C.size) ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ i ∈ L, (C.wires (List.ofFn x)).getD i false = true := by
  have count := tree_card n C T L C.output hTree
  have hGate (k : ℕ) (hk : k ∈ T) : k < C.size := by
    by_contra! outside
    have hnone : (gateAt C k).inputs.length = 0 := by
      unfold gateAt
      rw [List.getD_eq_default _ _ (show C.gates.length ≤ k from outside)]
      rfl
    have htwo := (hTree.1 k hk).2.1
    omega
  have nonempty : T ≠ ∅ := by
    intro empty
    rw [empty, Finset.card_empty] at count
    omega
  have rootIn := hTree.2.2.2
  rw [if_neg nonempty] at rootIn
  obtain ⟨root, hroot, rootEq⟩ := rootIn
  have hLeaf (i : ℕ) (hi : i ∈ L) : i < n + C.size := by
    have notRoot : i ≠ C.output := by
      intro heq
      have hbad := (hTree.2.1 i hi).1
      rw [heq, rootEq] at hbad
      exact hbad ⟨by omega, by simpa using hroot⟩
    have positive : 0 < readsIn C T i := by
      rw [(hTree.2.1 i hi).2, if_neg notRoot]
      decide
    obtain ⟨j, hj, hread⟩ := (rInP C T i).mp positive
    exact (hRB j (hGate j hj) i hread).trans (Nat.add_lt_add_left (hGate j hj) n)
  exact ⟨count.symm, hGate, hLeaf, fun x => otRE hRB hGate hTree x⟩

end PEqualNP.Outside.L_meta_2774.Tree

namespace PEqualNP.Outside.L_meta_2774.Retain

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

private def slots (S : Finset ℕ) (k : ℕ) : List ℕ :=
  (List.range k).filter fun j => decide (j ∉ S)

private def rank (S : Finset ℕ) (k : ℕ) : ℕ := (slots S k).length

private lemma slots_succ (S : Finset ℕ) (k : ℕ) :
    slots S (k + 1) = slots S k ++ (if k ∈ S then [] else [k]) := by
  by_cases h : k ∈ S <;> simp [slots, List.range_succ, h]

private lemma rank_succ (S : Finset ℕ) (k : ℕ) :
    rank S (k + 1) = rank S k + (if k ∈ S then 0 else 1) := by
  by_cases h : k ∈ S <;> simp [rank, slots_succ, h]

private lemma rank_mono (S : Finset ℕ) : Monotone (rank S) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [rank_succ]
  omega

private lemma rank_lt {S : Finset ℕ} {j k : ℕ} (h : j < k) (hj : j ∉ S) :
    rank S j < rank S k := by
  have hle := rank_mono S (show j + 1 ≤ k by omega)
  rw [rank_succ, ite_eq_right hj] at hle
  omega

private lemma rank_add_card (S : Finset ℕ) (k : ℕ) :
    rank S k + (S ∩ Finset.range k).card = k := by
  induction k with
  | zero => simp [rank, slots]
  | succ k ih =>
    rw [Finset.range_add_one, rank_succ]
    by_cases hk : k ∈ S
    · have he : S ∩ insert k (Finset.range k) = insert k (S ∩ Finset.range k) := by
        ext v
        by_cases hv : v = k <;> simp [hv, hk]
      rw [ite_eq_left hk, he, Finset.card_insert_of_notMem (by simp)]
      omega
    · have he : S ∩ insert k (Finset.range k) = S ∩ Finset.range k := by
        ext v
        by_cases hv : v = k <;> simp [hv, hk]
      rw [ite_eq_right hk, he]
      omega

def rename (n : ℕ) (S : Finset ℕ) (i : ℕ) : ℕ :=
  if i < n then i else n + rank S (i - n)

lemma rename_lt {n k : ℕ} {S : Finset ℕ} {i : ℕ} (hi : i < n + k)
    (hKeep : i < n ∨ i - n ∉ S) : rename n S i < n + rank S k := by
  by_cases h : i < n
  · simp only [rename, ite_eq_left h]
    omega
  · have hz := rank_lt (show i - n < k by omega) (hKeep.resolve_left h)
    simp only [rename, ite_eq_right h]
    omega

lemma rename_mono (n : ℕ) (S : Finset ℕ) : Monotone (rename n S) := by
  intro i j hij
  by_cases hi : i < n <;> by_cases hj : j < n
  · simpa [rename, hi, hj] using hij
  · simp only [rename, ite_eq_left hi, ite_eq_right hj]
    omega
  · omega
  · simp only [rename, ite_eq_right hi, ite_eq_right hj]
    exact Nat.add_le_add_left (rank_mono S (Nat.sub_le_sub_right hij n)) n

lemma rename_strict {n : ℕ} {S : Finset ℕ} {i j : ℕ} (hij : i < j)
    (hiKeep : i < n ∨ i - n ∉ S) : rename n S i < rename n S j := by
  by_cases hi : i < n <;> by_cases hj : j < n
  · simpa [rename, hi, hj] using hij
  · simp only [rename, ite_eq_left hi, ite_eq_right hj]
    omega
  · omega
  · have h := rank_lt (show i - n < j - n by omega) (hiKeep.resolve_left hi)
    simp only [rename, ite_eq_right hi, ite_eq_right hj]
    omega

private def translate (n : ℕ) (S : Finset ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (rename n S)⟩

private def selected (n : ℕ) (C : Circuit) (S : Finset ℕ) (k : ℕ) : List Gate :=
  (slots S k).map fun j => translate n S (gateAt C j)

private lemma selected_length (n : ℕ) (C : Circuit) (S : Finset ℕ) (k : ℕ) :
    (selected n C S k).length = rank S k := by simp [selected, rank]

private lemma selected_succ (n : ℕ) (C : Circuit) (S : Finset ℕ) (k : ℕ) :
    selected n C S (k + 1) = selected n C S k ++
      (if k ∈ S then [] else [translate n S (gateAt C k)]) := by
  by_cases h : k ∈ S <;> simp [selected, slots_succ, h]

private lemma selected_origin (n : ℕ) (C : Circuit) (S : Finset ℕ) (k : ℕ) :
    ∀ j < rank S k, ∃ i < k, i ∉ S ∧ rank S i = j ∧
      (selected n C S k).getD j ⟨.or, []⟩ = translate n S (gateAt C i) := by
  induction k with
  | zero => simp [rank, slots]
  | succ k ih =>
    intro j hj
    rw [rank_succ] at hj
    rw [selected_succ]
    by_cases hS : k ∈ S
    · simp only [ite_eq_left hS, Nat.add_zero] at hj
      simp only [ite_eq_left hS, List.append_nil]
      obtain ⟨i, hi, hki, hr, hv⟩ := ih j hj
      exact ⟨i, by omega, hki, hr, hv⟩
    · simp only [ite_eq_right hS] at hj ⊢
      by_cases hlt : j < rank S k
      · obtain ⟨i, hi, hki, hr, hv⟩ := ih j hlt
        rw [List.getD_append _ _ _ _ (by rwa [selected_length])]
        exact ⟨i, by omega, hki, hr, hv⟩
      · have hjk : j = rank S k := by omega
        subst j
        refine ⟨k, by omega, hS, rfl, ?_⟩
        rw [List.getD_append_right _ _ _ _ (by simp [selected_length])]
        simp [selected_length]

private def run (gates : List Gate) (wires : List Bool) : List Bool :=
  gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wires

private lemma run_length (gates : List Gate) (wires : List Bool) :
    (run gates wires).length = wires.length + gates.length := by
  induction gates generalizing wires with
  | nil => simp [run]
  | cons g rest ih =>
    change (run rest (wires ++ [_])).length = _
    rw [ih]
    simp
    omega

private lemma run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs ++ [g]) w = run gs w ++ [g.op.eval (g.inputs.map fun i => (run gs w).getD i false)] := by
  simp [run, List.foldl_append]

private lemma at_gate_get (C : Circuit) {k : ℕ} (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := List.getD_eq_getElem _ _ hk

private lemma prefix_eval (n : ℕ) (C : Circuit) (S : Finset ℕ) (hAO : IsAO2 n C)
    (hKeep : ∀ k < C.size, k ∉ S → ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ S)
    (x : Fin n → Bool) : ∀ k ≤ C.size, ∀ i < n + k, (i < n ∨ i - n ∉ S) →
      (run (selected n C S k) (List.ofFn x)).getD (rename n S i) false =
        (run (C.gates.take k) (List.ofFn x)).getD i false := by
  intro k
  induction k with
  | zero =>
    intro _ i hi _
    have h : i < n := by omega
    simp [selected, slots, rename, h]
  | succ k ih =>
    intro hk i hi hki
    have hk' : k < C.gates.length := by change k + 1 ≤ C.gates.length at hk; omega
    have hkSize : k < C.size := hk'
    have hTake : C.gates.take (k + 1) = C.gates.take k ++ [gateAt C k] := by
      rw [List.take_succ_eq_append_getElem hk', at_gate_get C hk']
    have hOrigLen : (run (C.gates.take k) (List.ofFn x)).length = n + k := by
      rw [run_length, List.length_ofFn, List.length_take, Nat.min_eq_left hk'.le]
    have hNewLen : (run (selected n C S k) (List.ofFn x)).length = n + rank S k := by
      simp [run_length, selected_length]
    rw [hTake, run_snoc, selected_succ]
    by_cases hiOld : i < n + k
    · rw [List.getD_append _ _ _ _ (by rwa [hOrigLen])]
      by_cases hS : k ∈ S
      · simp only [ite_eq_left hS, List.append_nil]
        exact ih hkSize.le i hiOld hki
      · simp only [ite_eq_right hS]
        rw [run_snoc, List.getD_append _ _ _ _ (by rw [hNewLen]; exact rename_lt hiOld hki)]
        exact ih hkSize.le i hiOld hki
    · have hiEq : i = n + k := by omega
      subst i
      have hS : k ∉ S := by
        have ht := hki.resolve_left (by omega)
        simpa using ht
      have hRen : rename n S (n + k) = n + rank S k := by simp [rename]
      simp only [ite_eq_right hS]
      rw [hRen, run_snoc, List.getD_append_right _ _ _ _ (by rw [hNewLen]),
        List.getD_append_right _ _ _ _ (by rw [hOrigLen]), hOrigLen, hNewLen]
      simp only [Nat.sub_self, List.getD_cons_zero, translate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ih hkSize.le a (hAO.2.1 k hk' a ha) (hKeep k hkSize hS a ha)

theorem retain_gates (n : ℕ) (C : Circuit) (S : Finset ℕ) (hAO : IsAO2 n C)
    (hS : S ⊆ Finset.range C.size)
    (hKeep : ∀ k < C.size, k ∉ S → ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ S) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + S.card = C.size ∧ ∃ r : ℕ → ℕ,
      ∀ i < n + C.size, (i < n ∨ i - n ∉ S) → r i < n + D.size ∧
        ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (r i) false =
          (C.wires (List.ofFn x)).getD i false := by
  let D : Circuit := ⟨selected n C S C.size, 0⟩
  have hlen : D.size = rank S C.size := selected_length n C S C.size
  have hmem (g : Gate) (hg : g ∈ D.gates) :
      ∃ i < C.size, g = translate n S (gateAt C i) := by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (show g ∈ selected n C S C.size from hg)
    exact ⟨i, (List.mem_range.mp (List.mem_filter.mp hi).1), rfl⟩
  have atMem (i : ℕ) (hi : i < C.size) : gateAt C i ∈ C.gates := by
    rw [at_gate_get C hi]
    exact List.getElem_mem _
  refine ⟨D, ⟨?_, ?_, ?_⟩, ?_, rename n S, ?_⟩
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := hmem g hg
    simpa [translate] using hAO.1 _ (atMem i hi)
  · intro j hj i hi
    have hj' : j < rank S C.size := by rwa [← hlen]
    obtain ⟨k, hk, hks, hRank, hg⟩ := selected_origin n C S C.size j hj'
    change i ∈ ((selected n C S C.size).getD j ⟨.or, []⟩).inputs at hi
    rw [hg] at hi
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
    rw [← hRank]
    exact rename_lt (hAO.2.1 k hk a ha) (hKeep k hk hks a ha)
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := hmem g hg
    simpa [translate] using hAO.2.2 _ (atMem i hi)
  · have hCard := congrArg Finset.card (Finset.inter_eq_left.mpr hS)
    rw [hlen, ← hCard]
    exact rank_add_card S C.size
  · intro i hi hiKeep
    refine ⟨by rw [hlen]; exact rename_lt hi hiKeep, ?_⟩
    intro x
    have hv := prefix_eval n C S hAO hKeep x C.size le_rfl i hi hiKeep
    change (run D.gates (List.ofFn x)).getD (rename n S i) false =
      (run C.gates (List.ofFn x)).getD i false
    simpa only [D, Circuit.size, List.take_length] using hv

end PEqualNP.Outside.L_meta_2774.Retain

namespace PEqualNP.Outside.L_meta_2774.Append

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

private def appendBin (n : ℕ) (D : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨D.gates ++ [⟨op, [a, b]⟩], n + D.size⟩

private theorem wiresLength (D : Circuit) (x : List Bool) :
    (D.wires x).length = x.length + D.size := by
  unfold Circuit.wires Circuit.size
  generalize D.gates = gs
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem wiresAppend (n : ℕ) (D : Circuit) (op : GateOp) (a b : ℕ) (x : List Bool) :
    (appendBin n D op a b).wires x =
      D.wires x ++ [op.eval [(D.wires x).getD a false, (D.wires x).getD b false]] := by
  simp [appendBin, Circuit.wires, List.foldl_append]

private theorem sizeAppend (n : ℕ) (D : Circuit) (op : GateOp) (a b : ℕ) :
    (appendBin n D op a b).size = D.size + 1 := by
  simp [appendBin, Circuit.size]

private theorem appendRead (n : ℕ) (D : Circuit) (op : GateOp) (a b : ℕ)
    (x : Fin n → Bool) (i : ℕ) (hi : i < n + D.size) :
    ((appendBin n D op a b).wires (List.ofFn x)).getD i false =
      (D.wires (List.ofFn x)).getD i false := by
  rw [wiresAppend]
  apply List.getD_append
  simpa [wiresLength] using hi

private theorem evalAppend (n : ℕ) (D : Circuit) (op : GateOp) (a b : ℕ)
    (x : Fin n → Bool) :
    (appendBin n D op a b).eval (List.ofFn x) =
      op.eval [(D.wires (List.ofFn x)).getD a false, (D.wires (List.ofFn x)).getD b false] := by
  unfold Circuit.eval
  rw [wiresAppend]
  have hlen : (D.wires (List.ofFn x)).length = n + D.size := by
    simp [wiresLength]
  change (_ ++ [_]).getD (n + D.size) false = _
  rw [← hlen]
  simp

private theorem appendAO (n : ℕ) (D : Circuit) (op : GateOp) (a b : ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hAO : IsAO2 n D)
    (ha : a < n + D.size) (hb : b < n + D.size) :
    IsAO2 n (appendBin n D op a b) := by
  rcases hAO with ⟨hOps, hReads, hTwo⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [appendBin, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hOps g hg
    · exact hop
  · intro j hj i hi
    by_cases h : j < D.gates.length
    · have heq : gateAt (appendBin n D op a b) j = gateAt D j := by
        simp only [gateAt, appendBin]
        exact List.getD_append _ _ _ _ h
      rw [heq] at hi
      exact hReads j h i hi
    · have hj' : j = D.gates.length := by
        simp only [appendBin, List.length_append, List.length_singleton] at hj
        omega
      subst j
      simp only [gateAt, appendBin, List.getD_eq_getElem?_getD, List.getElem?_concat_length,
        Option.getD_some, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    simp only [appendBin, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hTwo g hg
    · rfl

private theorem appendOutput (n : ℕ) (D : Circuit) (op : GateOp) (a b : ℕ) :
    (appendBin n D op a b).output < n + (appendBin n D op a b).size := by
  rw [sizeAppend]
  change n + D.size < n + (D.size + 1)
  omega

private theorem anyMemCongr (L : List ℕ) (p q : ℕ → Bool)
    (h : ∀ i ∈ L, p i = q i) : L.any p = L.any q := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [List.any_cons]
    rw [h i (by simp), ih (fun j hj => h j (by simp [hj]))]

private theorem foldOr (n : ℕ) (L : List ℕ) (D : Circuit) (hAO : IsAO2 n D)
    (hout : D.output < n + D.size) (hL : ∀ i ∈ L, i < n + D.size) :
    ∃ E : Circuit, IsAO2 n E ∧ E.size = D.size + L.length ∧
      ∀ x : Fin n → Bool, E.eval (List.ofFn x) =
        (D.eval (List.ofFn x) || L.any (fun i => (D.wires (List.ofFn x)).getD i false)) := by
  induction L generalizing D with
  | nil => exact ⟨D, hAO, by simp, by intro x; simp⟩
  | cons i L ih =>
    let A := appendBin n D GateOp.or D.output i
    have hi : i < n + D.size := hL i (by simp)
    have hA : IsAO2 n A := appendAO n D GateOp.or D.output i (Or.inr rfl) hAO hout hi
    have hAs : A.size = D.size + 1 := sizeAppend ..
    have hAL (j : ℕ) (hj : j ∈ L) : j < n + A.size := by
      have h := hL j (by simp [hj])
      omega
    obtain ⟨E, hE, hEs, hEval⟩ := ih A hA (appendOutput ..) hAL
    refine ⟨E, hE, by simp only [List.length_cons]; omega, ?_⟩
    intro x
    have hTail : L.any (fun j => (A.wires (List.ofFn x)).getD j false) =
        L.any (fun j => (D.wires (List.ofFn x)).getD j false) := by
      apply anyMemCongr
      intro j hj
      exact appendRead n D GateOp.or D.output i x j (hL j (by simp [hj]))
    rw [hEval, hTail]
    change ((appendBin n D GateOp.or D.output i).eval (List.ofFn x) || _) = _
    rw [evalAppend]
    simp [GateOp.eval, Circuit.eval, Bool.or_assoc]

theorem merge_chain (n : ℕ) (D : Circuit) (a b c : ℕ) (L : List ℕ)
    (hAO : IsAO2 n D) (ha : a < n + D.size) (hb : b < n + D.size)
    (hc : c < n + D.size) (hL : ∀ i ∈ L, i < n + D.size) :
    ∃ E : Circuit, IsAO2 n E ∧ E.size = D.size + 2 + L.length ∧
      ∀ x : Fin n → Bool, E.eval (List.ofFn x) =
        (((D.wires (List.ofFn x)).getD a false &&
            ((D.wires (List.ofFn x)).getD b false || (D.wires (List.ofFn x)).getD c false)) ||
          L.any (fun i => (D.wires (List.ofFn x)).getD i false)) := by
  let A := appendBin n D GateOp.or b c
  let B := appendBin n A GateOp.and a A.output
  have hAs : A.size = D.size + 1 := sizeAppend ..
  have hBs : B.size = A.size + 1 := sizeAppend ..
  have hA : IsAO2 n A := appendAO n D GateOp.or b c (Or.inr rfl) hAO hb hc
  have haA : a < n + A.size := by omega
  have houtA : A.output < n + A.size := appendOutput ..
  have hB : IsAO2 n B := appendAO n A GateOp.and a A.output (Or.inl rfl) hA haA houtA
  have hBL (i : ℕ) (hi : i ∈ L) : i < n + B.size := by have h := hL i hi; omega
  obtain ⟨E, hE, hEs, hEval⟩ := foldOr n L B hB (appendOutput ..) hBL
  refine ⟨E, hE, by omega, ?_⟩
  intro x
  have hTail : L.any (fun i => (B.wires (List.ofFn x)).getD i false) =
      L.any (fun i => (D.wires (List.ofFn x)).getD i false) := by
    apply anyMemCongr
    intro i hi
    have hiD := hL i hi
    have hiA : i < n + A.size := by omega
    exact (appendRead n A GateOp.and a A.output x i hiA).trans
      (appendRead n D GateOp.or b c x i hiD)
  rw [hEval, hTail]
  change ((appendBin n A GateOp.and a A.output).eval (List.ofFn x) || _) = _
  rw [evalAppend]
  simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
  change (((A.wires (List.ofFn x)).getD a false && A.eval (List.ofFn x)) || _) = _
  rw [appendRead n D GateOp.or b c x a ha]
  change ((_ && (appendBin n D GateOp.or b c).eval (List.ofFn x)) || _) = _
  rw [evalAppend]
  simp [GateOp.eval]

end PEqualNP.Outside.L_meta_2774.Append

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_2774 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (T L : Finset ℕ) (i₁ i₂ a b c : ℕ),
  (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ PEqualNP.MetaComplexity.NestedCover.IsOrTree n C T L C.output ∧
  n + i₁ ∈ L ∧ n + i₂ ∈ L ∧ i₁ ≠ i₂ ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C i₁).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C i₁).inputs = [a, b] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C i₁).inputs = [b, a]) ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C i₂).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C i₂).inputs = [a, c] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C i₂).inputs = [c, a]) ∧
  (∀ k < C.gates.length, k ∉ T → n + i₁ ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs ∧ n + i₂ ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs ∧
    ∀ j ∈ T, n + j ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs)) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧
  PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧ D.size + 1 ≤ C.size := by
  classical
  intro n C T L i₁ i₂ a b c
  rintro ⟨hAO, hRB, hTree, leaf₁, leaf₂, hne, hop₁, hin₁, hop₂, hin₂, isolation⟩
  have wireNe : n + i₁ ≠ n + i₂ := by omega
  have atLeastTwo : 2 ≤ L.card :=
    Finset.one_lt_card.mpr ⟨n + i₁, leaf₁, n + i₂, leaf₂, wireNe⟩
  obtain ⟨treeCard, topLt, leafLt, treeEval⟩ := PEqualNP.Outside.L_meta_2774.Tree.specs n C T L hRB hTree atLeastTwo
  have firstLt : i₁ < C.size := by
    have := leafLt (n + i₁) leaf₁
    omega
  have secondLt : i₂ < C.size := by
    have := leafLt (n + i₂) leaf₂
    omega
  have leafNotTop {i : ℕ} (hi : n + i ∈ L) : i ∉ T := by
    intro hit
    exact (hTree.2.1 (n + i) hi).1 ⟨by omega, by simpa using hit⟩
  have firstNotTop := leafNotTop leaf₁
  have secondNotTop := leafNotTop leaf₂
  let removed := insert i₁ (insert i₂ T)
  have removedCard : removed.card = T.card + 2 := by
    have firstNotInner : i₁ ∉ insert i₂ T := by simp [hne, firstNotTop]
    change (insert i₁ (insert i₂ T)).card = T.card + 2
    rw [Finset.card_insert_of_notMem firstNotInner, Finset.card_insert_of_notMem secondNotTop]
  have removedRange : removed ⊆ Finset.range C.size := by
    intro k hk
    apply Finset.mem_range.mpr
    simp only [removed, Finset.mem_insert] at hk
    rcases hk with rfl | rfl | hk
    · exact firstLt
    · exact secondLt
    · exact topLt k hk
  have keptInput {k i : ℕ} (hk : k < C.size) (ht : k ∉ T)
      (hi : i ∈ (gateAt C k).inputs) : i < n ∨ i - n ∉ removed := by
    by_cases h : i < n
    · exact Or.inl h
    · right
      intro hit
      obtain ⟨noFirst, noSecond, noTop⟩ := isolation k hk ht
      have hidx : n + (i - n) = i := by omega
      have hread : n + (i - n) ∈ (gateAt C k).inputs := by rwa [hidx]
      simp only [removed, Finset.mem_insert] at hit
      rcases hit with hit | hit | hit
      · exact noFirst (by simpa only [hit] using hread)
      · exact noSecond (by simpa only [hit] using hread)
      · exact noTop (i - n) hit hread
  have keepAll : ∀ k < C.size, k ∉ removed →
      ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ removed := by
    intro k hk hkeep i hi
    apply keptInput hk _ hi
    intro ht
    exact hkeep (by simp [removed, ht])
  obtain ⟨D, hDAO, hDsize, ren, hren⟩ := PEqualNP.Outside.L_meta_2774.Retain.retain_gates n C removed hAO removedRange keepAll
  have aIn : a ∈ (gateAt C i₁).inputs := by rcases hin₁ with h | h <;> simp [h]
  have bIn : b ∈ (gateAt C i₁).inputs := by rcases hin₁ with h | h <;> simp [h]
  have cIn : c ∈ (gateAt C i₂).inputs := by rcases hin₂ with h | h <;> simp [h]
  have aBound : a < n + C.size := lt_trans (hRB i₁ firstLt a aIn) (by omega)
  have bBound : b < n + C.size := lt_trans (hRB i₁ firstLt b bIn) (by omega)
  have cBound : c < n + C.size := lt_trans (hRB i₂ secondLt c cIn) (by omega)
  have renA := hren a aBound (keptInput firstLt firstNotTop aIn)
  have renB := hren b bBound (keptInput firstLt firstNotTop bIn)
  have renC := hren c cBound (keptInput secondLt secondNotTop cIn)
  let remaining := (L.erase (n + i₁)).erase (n + i₂)
  have secondInFirstErased : n + i₂ ∈ L.erase (n + i₁) :=
    Finset.mem_erase.mpr ⟨wireNe.symm, leaf₂⟩
  have remainingCard : remaining.card + 2 = L.card := by
    change ((L.erase (n + i₁)).erase (n + i₂)).card + 2 = L.card
    rw [Finset.card_erase_of_mem secondInFirstErased, Finset.card_erase_of_mem leaf₁]
    omega
  have renLeaf (w : ℕ) (hw : w ∈ remaining) :
      ren w < n + D.size ∧ ∀ x : Fin n → Bool,
        (D.wires (List.ofFn x)).getD (ren w) false = (C.wires (List.ofFn x)).getD w false := by
    obtain ⟨neSecond, inFirstErased⟩ := Finset.mem_erase.mp hw
    obtain ⟨neFirst, inLeaves⟩ := Finset.mem_erase.mp inFirstErased
    apply hren w (leafLt w inLeaves)
    by_cases h : w < n
    · exact Or.inl h
    · right
      intro hit
      simp only [removed, Finset.mem_insert] at hit
      rcases hit with hit | hit | hit
      · exact neFirst (by omega)
      · exact neSecond (by omega)
      · exact (hTree.2.1 w inLeaves).1 ⟨by omega, hit⟩
  let leaves := remaining.toList.map ren
  have leavesLen : leaves.length = remaining.card := by simp [leaves]
  have leavesBound : ∀ i ∈ leaves, i < n + D.size := by
    intro i hi
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hi
    exact (renLeaf w (Finset.mem_toList.mp hw)).1
  obtain ⟨E, hEAO, hEsize, hEeval⟩ :=
    PEqualNP.Outside.L_meta_2774.Append.merge_chain n D (ren a) (ren b) (ren c) leaves hDAO renA.1 renB.1 renC.1 leavesBound
  refine ⟨E, hEAO, ?_, ?_⟩
  · funext x
    change E.eval (List.ofFn x) = C.eval (List.ofFn x)
    have bothAnd {k p q : ℕ} (hk : k < C.size) (hop : (gateAt C k).op = GateOp.and)
        (hin : (gateAt C k).inputs = [p, q] ∨ (gateAt C k).inputs = [q, p]) :
        PEqualNP.Outside.L_meta_2774.Tree.wV n C x (n + k) = (PEqualNP.Outside.L_meta_2774.Tree.wV n C x p && PEqualNP.Outside.L_meta_2774.Tree.wV n C x q) := by
      rw [PEqualNP.Outside.L_meta_2774.Tree.wvGR n C hRB x k hk, hop]
      rcases hin with h | h <;> simp [h, GateOp.eval, Bool.and_comm]
    have restTrue :
        leaves.any (fun i => (D.wires (List.ofFn x)).getD i false) = true ↔
          ∃ w ∈ remaining, (C.wires (List.ofFn x)).getD w false = true := by
      rw [List.any_eq_true]
      constructor
      · rintro ⟨i, hi, hval⟩
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hi
        have hw' := Finset.mem_toList.mp hw
        exact ⟨w, hw', ((renLeaf w hw').2 x).symm.trans hval⟩
      · rintro ⟨w, hw, hval⟩
        exact ⟨ren w, List.mem_map.mpr ⟨w, Finset.mem_toList.mpr hw, rfl⟩,
          ((renLeaf w hw).2 x).trans hval⟩
    apply Bool.eq_iff_iff.mpr
    rw [hEeval x, renA.2 x, renB.2 x, renC.2 x, treeEval x]
    simp only [Bool.or_eq_true, Bool.and_eq_true, restTrue]
    constructor
    · intro h
      rcases h with ⟨ha, hbc⟩ | ⟨w, hw, hval⟩
      · rcases hbc with hb | hc
        · refine ⟨n + i₁, leaf₁, ?_⟩
          change PEqualNP.Outside.L_meta_2774.Tree.wV n C x (n + i₁) = true
          rw [bothAnd firstLt hop₁ hin₁, Bool.and_eq_true]
          exact ⟨ha, hb⟩
        · refine ⟨n + i₂, leaf₂, ?_⟩
          change PEqualNP.Outside.L_meta_2774.Tree.wV n C x (n + i₂) = true
          rw [bothAnd secondLt hop₂ hin₂, Bool.and_eq_true]
          exact ⟨ha, hc⟩
      · exact ⟨w, (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).2, hval⟩
    · rintro ⟨w, hw, hval⟩
      by_cases heq₁ : w = n + i₁
      · subst w
        change PEqualNP.Outside.L_meta_2774.Tree.wV n C x (n + i₁) = true at hval
        rw [bothAnd firstLt hop₁ hin₁, Bool.and_eq_true] at hval
        exact Or.inl ⟨hval.1, Or.inl hval.2⟩
      · by_cases heq₂ : w = n + i₂
        · subst w
          change PEqualNP.Outside.L_meta_2774.Tree.wV n C x (n + i₂) = true at hval
          rw [bothAnd secondLt hop₂ hin₂, Bool.and_eq_true] at hval
          exact Or.inl ⟨hval.1, Or.inr hval.2⟩
        · exact Or.inr ⟨w, Finset.mem_erase.mpr ⟨heq₂, Finset.mem_erase.mpr ⟨heq₁, hw⟩⟩, hval⟩
  · omega

