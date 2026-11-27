import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9326
open Finset
abbrev V := Fin 21
abbrev Box := Finset V × Finset V
abbrev J := Fin 10
def rows : List ℕ := [1179809,262467,524934,1049868,2585,5170,10340,20680,41360,82720,165440,330880,661760,1323520,549889,1099778,102405,204810,409620,819240,1638480]
def bit (i j : V) := (rows.getD i.val 0).testBit j.val
def line (i : V) := univ.filter (fun j => bit i j=true)
def dual (j : V) := univ.filter (fun i => bit i j=true)
def good (b : Box) := ∀ i ∈ b.1, ∀ j ∈ b.2, bit i j=false
def clean (b : Box) : Box := if b.1.Nonempty ∧ b.2.Nonempty then b else (∅,∅)

theorem geometry : (∀ i, (line i).card=5) ∧ (∀ i j, i≠j → (line i ∩ line j).card≤1) ∧
    (∀ j, (dual j).card=5) ∧ (∀ i j, i≠j → (dual i ∩ dual j).card≤1) := by decide

-- Count the union by adding one five-element neighborhood at a time.
theorem unionCount (N : V → Finset V) (five : ∀ i, (N i).card=5)
    (inter : ∀ i j, i≠j → (N i ∩ N j).card≤1) (S : Finset V) :
    5*S.card≤(S.biUnion N).card+Nat.choose S.card 2 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have sub : N a ∩ S.biUnion N ⊆ S.biUnion (fun j => N a ∩ N j) := by
      intro t ht
      obtain ⟨j,hj,mem⟩ := mem_biUnion.mp (mem_inter.mp ht).2
      exact mem_biUnion.mpr ⟨j,hj,mem_inter.mpr ⟨(mem_inter.mp ht).1,mem⟩⟩
    have cap : (N a ∩ S.biUnion N).card ≤ S.card := calc
      _ ≤ _ := card_le_card sub
      _ ≤ ∑ j ∈ S, (N a ∩ N j).card := card_biUnion_le
      _ ≤ ∑ _ ∈ S, 1 := sum_le_sum fun j hj => inter a j (fun e => ha (e ▸ hj))
      _ = _ := by simp
    have eq := card_union_add_card_inter (N a) (S.biUnion N)
    rw [five] at eq
    rw [card_insert_of_notMem ha,biUnion_insert]
    have choose : (S.card+1).choose 2=S.card.choose 2+S.card := by
      rw [Nat.choose_succ_succ]; simp [Nat.add_comm]
    omega

theorem limit (N : V → Finset V) (five : ∀ i, (N i).card=5)
    (inter : ∀ i j, i≠j → (N i ∩ N j).card≤1) (U W : Finset V)
    (off : ∀ i ∈ U, Disjoint (N i) W) (k : ℕ) (hk : k≤U.card) :
    5*k+W.card≤21+Nat.choose k 2 := by
  obtain ⟨T,sub,ct⟩ := exists_subset_card_eq hk
  have dj : Disjoint (T.biUnion N) W := by
    apply Finset.disjoint_left.mpr
    intro j hj wj
    obtain ⟨i,ti,ij⟩ := mem_biUnion.mp hj
    exact Finset.disjoint_left.mp (off i (sub ti)) ij wj
  have bound := card_le_card (subset_univ (T.biUnion N ∪ W))
  rw [card_union_of_disjoint dj] at bound
  have total : (univ : Finset V).card=21 := by decide
  rw [total] at bound
  have lower := unionCount N five inter T
  rw [ct] at lower
  omega

-- Every nonempty rectangle fits inside one of these nine pairs of size bounds.
-- This comparison is numerical and does not require extending the rectangle.
def shapes : Fin 9 → ℕ × ℕ := ![(1,16),(2,12),(3,9),(4,7),(6,6),(7,4),(9,3),(12,2),(16,1)]
def coords (i : Fin 9) := (shapes i).1
def width (i : Fin 9) := (shapes i).2

theorem shapePossible (b : Box) (ok : good b) :
    ∃ i : Fin 9, (clean b).1.card≤coords i ∧ (clean b).2.card≤width i := by
  unfold clean
  split
  · rename_i nonempty
    have byRow := limit line geometry.1 geometry.2.1 b.1 b.2 (fun i hi => by
      apply Finset.disjoint_left.mpr
      intro j hj hb
      have e := (mem_filter.mp hj).2
      rw [ok i hi j hb] at e; contradiction)
    have byCol := limit dual geometry.2.2.1 geometry.2.2.2 b.2 b.1 (fun j hj => by
      apply Finset.disjoint_left.mpr
      intro i hi hb
      have e := (mem_filter.mp hi).2
      rw [ok i hb j hj] at e; contradiction)
    let p : Fin 22 := ⟨b.1.card,by have h := b.1.card_le_univ; change _≤21 at h; omega⟩
    let q : Fin 22 := ⟨b.2.card,by have h := b.2.card_le_univ; change _≤21 at h; omega⟩
    have small : ∀ p q : Fin 22, 0<p.val → 0<q.val →
      (∀ k : Fin 6, k.val≤p.val → 5*k.val+q.val≤21+k.val.choose 2) →
      (∀ k : Fin 6, k.val≤q.val → 5*k.val+p.val≤21+k.val.choose 2) →
      ∃ i : Fin 9, p.val≤coords i ∧ q.val≤width i := by decide
    exact small p q (card_pos.mpr nonempty.1) (card_pos.mpr nonempty.2)
      (fun k hk => byRow k.val hk) (fun k hk => byCol k.val hk)
  · exact ⟨4,by simp,by simp⟩

def loadRow (A : J → Finset V) (w : J → ℕ) (u : V) := ∑ j, if u∈A j then w j else 0

theorem countRows (A : J → Finset V) (w : J → ℕ) (S : Finset J) :
    (∑ u : V, ∑ j ∈ S, if u∈A j then w j else 0) = ∑ j ∈ S, (A j).card*w j := by
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  simp [sum_ite_mem]

theorem loadFromCover (A B : J → Finset V) (Z : V → Finset V)
    (den : ∀ u, (Z u).card=16) (cov : ∀ u v, v∈Z u → ∃ j, u∈A j ∧ v∈B j)
    (w : J → ℕ) (ww : ∀ j, (B j).card≤w j) (u : V) : 16≤loadRow A w u := by
  let S := univ.filter (fun j => u∈A j)
  have sub : Z u ⊆ S.biUnion B := by
    intro v hv; obtain ⟨j,ha,hb⟩ := cov u v hv
    exact mem_biUnion.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,ha⟩,hb⟩
  calc
    16 = (Z u).card := (den u).symm
    _ ≤ _ := card_le_card sub
    _ ≤ ∑ j ∈ S, (B j).card := card_biUnion_le
    _ ≤ ∑ j ∈ S, w j := sum_le_sum fun j _ => ww j
    _ = _ := by simp only [S,loadRow,sum_filter]

theorem aggregate (A : J → Finset V) (p q : J → ℕ) (cap : ∀ j, (A j).card≤p j)
    (h : ∀ u, 16≤loadRow A q u) : 336≤∑ j, p j*q j := calc
  336 = ∑ _ : V, 16 := by decide
  _ ≤ ∑ u, loadRow A q u := sum_le_sum fun u _ => h u
  _ = ∑ j, (A j).card*q j := countRows A q univ
  _ ≤ _ := sum_le_sum fun j _ => Nat.mul_le_mul_right _ (cap j)

theorem threeReaders (A : J → Finset V) (p q : J → ℕ) (cap : ∀ j, (A j).card≤p j)
    (h : ∀ u, 16≤loadRow A q u) (short : ∀ j, q j≤7) : 63≤∑ j, p j := by
  have pt (u : V) : 3≤loadRow A (fun _ => 1) u := by
    have small : loadRow A q u ≤ 7*loadRow A (fun _ => 1) u := by
      unfold loadRow
      rw [mul_sum]
      apply sum_le_sum
      intro j _; by_cases mem : u∈A j <;> simp [mem,short]
    have high := h u
    omega
  calc
    63 = ∑ _ : V, 3 := by decide
    _ ≤ ∑ u, loadRow A (fun _ => 1) u := sum_le_sum fun u _ => pt u
    _ = ∑ j, (A j).card*1 := countRows A (fun _ => 1) univ
    _ ≤ _ := sum_le_sum fun j _ => by simpa using cap j

-- After ordinary rectangles supply six entries apiece, covering sixteen entries
-- needs at least three of them, less the credit earned by the two exceptions.
def credit (d : ℕ) := (d+2)/6
def extra (q s : ℕ) := credit (q+s)-(credit q+credit s)
def gain (p q r s : ℕ) := p*credit q+r*credit s+min p r*extra q s

theorem bookkeep (A : J → Finset V) (p q : J → ℕ) (cap : ∀ j, (A j).card≤p j)
    (h : ∀ u, 16≤loadRow A q u) (a b : J) (ab : a≠b)
    (usual : ∀ j, j≠a → j≠b → p j≤6 ∧ q j≤6) :
    15≤gain (p a) (q a) (p b) (q b) := by
  let S := (univ.erase a).erase b
  have bin : b∈(univ : Finset J).erase a := mem_erase.mpr ⟨ab.symm,mem_univ _⟩
  have eight : S.card=8 := by simp [S,card_erase_of_mem bin,card_erase_of_mem (mem_univ a)]
  have regular {j} (hj : j∈S) : p j≤6 ∧ q j≤6 :=
    usual j (mem_erase.mp (mem_erase.mp hj).2).1 (mem_erase.mp hj).1
  have splitSum (f : J → ℕ) : (∑ j, f j)=(∑ j ∈ S, f j)+f a+f b := by
    have h1 := sum_erase_add univ f (mem_univ a)
    have h2 := sum_erase_add _ f bin
    change (∑ j ∈ S, f j)+f b=_ at h2
    omega
  let t (u : V) := ∑ j ∈ S, if u∈A j then 1 else 0
  have total : (∑ u, t u)≤48 := calc
    _ = ∑ j ∈ S, (A j).card*1 := countRows A (fun _ => 1) S
    _ ≤ ∑ _ ∈ S, 6 := sum_le_sum fun j hj => by simpa using (cap j).trans (regular hj).1
    _ = _ := by simp [eight]
  have point (u : V) : 3≤t u+
      (if u∈A a then credit (q a) else 0)+(if u∈A b then credit (q b) else 0)+
      (if u∈(A a ∩ A b) then extra (q a) (q b) else 0) := by
    have upper : (∑ j ∈ S, if u∈A j then q j else 0)≤6*t u := by
      unfold t
      rw [mul_sum]
      apply sum_le_sum; intro j hj
      by_cases hj' : u∈A j <;> simp [hj',(regular hj).2]
    have need := h u
    unfold loadRow at need
    rw [splitSum] at need
    by_cases ha : u∈A a <;> by_cases hb : u∈A b <;>
      simp only [mem_inter,ha,hb,and_self,false_and,and_false,ite_true,ite_false,add_zero] at need ⊢ <;>
      (try simp only [extra,credit]) <;> omega
  have all := sum_le_sum (s := (univ : Finset V)) (fun u _ => point u)
  simp only [sum_add_distrib] at all
  have ident (T : Finset V) (z : ℕ) : (∑ u, if u∈T then z else 0)=T.card*z := by simp [sum_ite_mem]
  simp only [ident,show (∑ _ : V, 3)=63 by decide] at all
  have hmin : (A a ∩ A b).card ≤ min (p a) (p b) :=
    le_min ((card_le_card inter_subset_left).trans (cap a)) ((card_le_card inter_subset_right).trans (cap b))
  have h1 := Nat.mul_le_mul_right (credit (q a)) (cap a)
  have h2 := Nat.mul_le_mul_right (credit (q b)) (cap b)
  have h3 := Nat.mul_le_mul_right (extra (q a) (q b)) hmin
  unfold gain; omega

-- Check the 81 ordered pairs of exceptional shapes against their area and
-- the credits they can supply for both rows and columns.
theorem tableCheck : ∀ a b : Fin 9,
    336≤288+coords a*width a+coords b*width b →
    15≤gain (coords a) (width a) (coords b) (width b) →
    15≤gain (width a) (coords a) (width b) (coords b) → False := by decide

-- A long side forces a loss of nine from area 36. Every other exceptional
-- rectangle loses at least eight. The total permissible loss is only 24.
theorem impossible (A B : J → Finset V) (sh : J → Fin 9)
    (ca : ∀ j, (A j).card≤coords (sh j)) (cb : ∀ j, (B j).card≤width (sh j))
    (leftLoad : ∀ u, 16≤loadRow A (fun j => width (sh j)) u)
    (rightLoad : ∀ u, 16≤loadRow B (fun j => coords (sh j)) u) : False := by
  let p := fun j => coords (sh j)
  let q := fun j => width (sh j)
  let c := fun j => p j*q j
  let loss := fun j => 36-c j
  have allArea : 336≤∑ j, c j := aggregate A p q ca leftLoad
  have maxArea : ∀ i : Fin 9, coords i*width i≤36 := by decide
  have balance : (∑ j, c j)+(∑ j, loss j)=360 := by
    rw [←sum_add_distrib]
    calc
      _ = ∑ _ : J, 36 := sum_congr rfl fun j _ => by
        have h := maxArea (sh j); change c j≤36 at h
        dsimp only [loss]; omega
      _ = _ := by decide
  have slack : (∑ j, loss j)≤24 := by omega
  by_cases large : ∃ a, 8≤p a ∨ 8≤q a
  · obtain ⟨a,ha⟩ := large
    have big : 9≤loss a :=
      (show ∀ i : Fin 9, 8≤coords i ∨ 8≤width i → 9≤36-coords i*width i by decide) (sh a) ha
    have missed (j : J) (hj : sh j≠4) : 8≤loss j :=
      (show ∀ i : Fin 9, i≠4 → 8≤36-coords i*width i by decide) (sh j) hj
    have only (u v : J) (ua : u≠a) (va : v≠a) (uv : u≠v) (hu : sh u≠4) (hv : sh v≠4) : False := by
      have le := sum_le_sum_of_subset_of_nonneg (f := loss) (subset_univ ({a,u,v} : Finset J))
        (fun _ _ _ => Nat.zero_le _)
      rw [sum_insert (by simp [ua.symm,va.symm]),sum_pair uv] at le
      have x := missed u hu
      have y := missed v hv
      omega
    have pair : ∃ b : J, a≠b ∧ ∀ j, j≠a → j≠b → sh j=4 := by
      by_cases has : ∃ b, b≠a ∧ sh b≠4
      · obtain ⟨b,ba,hb⟩ := has
        refine ⟨b,ba.symm,fun j ja jb => ?_⟩
        by_contra bad
        exact only j b ja ba jb bad hb
      · obtain ⟨b,ab⟩ := (show ∀ a : J, ∃ b, a≠b by decide) a
        refine ⟨b,ab,fun j ja _ => ?_⟩
        by_contra bad
        exact has ⟨j,ja,bad⟩
    obtain ⟨b,ab,fixed⟩ := pair
    have reg (j) (ja : j≠a) (jb : j≠b) : p j=6 ∧ q j=6 := by
      change coords (sh j)=6 ∧ width (sh j)=6
      rw [fixed j ja jb]; decide
    have l := bookkeep A p q ca leftLoad a b ab (fun j ja jb => ⟨(reg j ja jb).1.le,(reg j ja jb).2.le⟩)
    have r := bookkeep B q p cb rightLoad a b ab (fun j ja jb => ⟨(reg j ja jb).2.le,(reg j ja jb).1.le⟩)
    let T := ((univ : Finset J).erase a).erase b
    have bin : b∈(univ : Finset J).erase a := mem_erase.mpr ⟨ab.symm,mem_univ _⟩
    have nT : T.card=8 := by simp [T,card_erase_of_mem bin,card_erase_of_mem (mem_univ a)]
    have first := sum_erase_add univ c (mem_univ a)
    have second := sum_erase_add _ c bin
    change (∑ j ∈ T,c j)+c b=_ at second
    have eq : (∑ j ∈ T, c j)=288 := calc
      _ = ∑ _ ∈ T, 36 := sum_congr rfl fun j hj => by
        obtain ⟨hp,hq⟩ := reg j (mem_erase.mp (mem_erase.mp hj).2).1 (mem_erase.mp hj).1
        change p j*q j=36
        rw [hp,hq]
      _ = _ := by simp [nT]
    exact tableCheck (sh a) (sh b) (by change 336≤288+c a+c b; omega) l r
  · have short (j : J) : p j≤7 ∧ q j≤7 := by
      have h := not_exists.mp large j; omega
    have l := threeReaders A p q ca leftLoad (fun j => (short j).2)
    have r := threeReaders B q p cb rightLoad (fun j => (short j).1)
    have total : (∑ j, p j)+(∑ j, q j)≤120 := calc
      _ = ∑ j, (p j+q j) := sum_add_distrib.symm
      _ ≤ ∑ _ : J, 12 := sum_le_sum fun j _ =>
        (show ∀ i : Fin 9, coords i≤7 → width i≤7 → coords i+width i≤12 by decide)
          (sh j) (short j).1 (short j).2
      _ = _ := by decide
    omega

theorem noTen (L : List Box) (size : L.length≤10) (ok : ∀ z∈L, good z)
    (cov : ∀ u v, bit u v=false → ∃ z∈L, u∈z.1 ∧ v∈z.2) : False := by
  let box (j : J) := L.getD j.val (∅,∅)
  have valid (j : J) : good (box j) := by
    by_cases h : j.val<L.length
    · unfold box; rw [List.getD_eq_getElem _ _ h]; exact ok _ (List.getElem_mem h)
    · unfold box; rw [List.getD_eq_default _ _ (by omega)]; simp [good]
  choose sh hs using fun j => shapePossible (box j) (valid j)
  let A := fun j => (clean (box j)).1
  let B := fun j => (clean (box j)).2
  have hits (u v : V) (z : bit u v=false) : ∃ j, u∈A j ∧ v∈B j := by
    obtain ⟨r,mem,hu,hv⟩ := cov u v z
    obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp mem
    let j : J := ⟨i,by omega⟩
    have pick : box j=r := (List.getD_eq_getElem _ _ hi).trans e
    have keep : r.1.Nonempty ∧ r.2.Nonempty := ⟨⟨u,hu⟩,⟨v,hv⟩⟩
    have chosen : clean r=r := ite_eq_left keep
    refine ⟨j,?_⟩; simpa only [A,B,pick,chosen] using And.intro hu hv
  let Z (u : V) := univ.filter (fun v => bit u v=false)
  let Z' (v : V) := univ.filter (fun u => bit u v=false)
  have deg : ∀ u, (Z u).card=16 := by decide
  have deg' : ∀ v, (Z' v).card=16 := by decide
  apply impossible A B sh (fun j => (hs j).1) (fun j => (hs j).2)
  · exact loadFromCover A B Z deg (fun u v h => hits u v (mem_filter.mp h).2)
      (fun j => width (sh j)) (fun j => (hs j).2)
  · apply loadFromCover B A Z' deg' _ (fun j => coords (sh j)) (fun j => (hs j).1)
    intro v u h
    obtain ⟨j,ha,hb⟩ := hits u v (mem_filter.mp h).2
    exact ⟨j,hb,ha⟩

end PEqualNP.Outside.L_meta_9326

theorem PEqualNP.Outside.L_meta_9326 : ¬ (∃ L : List (Finset (Fin 21) × Finset (Fin 21)), L.length ≤ 10 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 21) (j : Fin 21), (([1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L,hl,ok,cov⟩
  exact PEqualNP.Outside.L_meta_9326.noTen L hl ok cov
