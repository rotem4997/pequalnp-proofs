import Mathlib
import PEqualNP.Defs

open PEqualNP.Defs.LratEncoding

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5052_251
  (terminal : let cols : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
    ∀ V : ℕ → Finset (Fin 58),
    let S := fun (j : ℕ) (B : Finset (Fin 58)) =>
      B=∅ ∨ B=Finset.univ ∨ (∃ z∈cols, ∀ i : Fin 58, i∈B ↔ z.testBit i.val=true) ∨ ∃ k<j, B=V k
    (∀ j<24, ∃ a b, S j a ∧ S j b ∧ (V j=a∩b ∨ V j=a∪b)) →
    ∀ a b c, S 24 a → S 24 b → S 24 c → ∀ d∈[b∩c,b∪c],
      a∩d ≠ Finset.Iio (21 : Fin 58) ∧ a∪d ≠ Finset.Iio (21 : Fin 58))
  (decode : ∀ (g : ℕ → Bool) (rows : List ℕ), FormulaSat (enc2 14 26 g rows) →
    ∃ F : ℕ → ℕ → Bool,
    let read := fun (j w r : ℕ) => if w<14 then r.testBit w else if w<14+j then F (w-14) r else false
    (∀ j<26, (∀ r∈rows, F j r=true) ∨ ∃ u v, (∀ r∈rows, F j r=(read j u r && read j v r)) ∨
      (∀ r∈rows, F j r=(read j u r || read j v r))) ∧
    ∃ k, ∀ r∈rows, read 26 k r=g r)
  : have x1 : List ℕ := [(129 : ℕ), (257 : ℕ), (1025 : ℕ), (130 : ℕ), (514 : ℕ), (8194 : ℕ), (260 : ℕ), (4100 : ℕ), (8196 : ℕ), (136 : ℕ), (2056 : ℕ), (4104 : ℕ), (1040 : ℕ), (2064 : ℕ), (8208 : ℕ), (544 : ℕ), (1056 : ℕ), (4128 : ℕ), (320 : ℕ), (576 : ℕ), (2112 : ℕ)]; have x2 : List ℕ :=   have x2 : List ℕ :=     have x2 : List ℕ :=       have x2 : List ℕ := [(10656 : ℕ), (12353 : ℕ), (13504 : ℕ), (14849 : ℕ), (16256 : ℕ)];       (8488 : ℕ) :: (8713 : ℕ) :: (9288 : ℕ) :: (9992 : ℕ) :: (10273 : ℕ) :: x2;     have x3 : List ℕ := (5186 : ℕ) :: (6147 : ℕ) :: (7426 : ℕ) :: (8297 : ℕ) :: (8416 : ℕ) :: x2;     (4304 : ℕ) :: (4370 : ℕ) :: (4625 : ℕ) :: (5008 : ℕ) :: x3;   have x3 : List ℕ :=     have x3 : List ℕ := (2338 : ℕ) :: (2565 : ℕ) :: (3078 : ℕ) :: (3716 : ℕ) :: (4179 : ℕ) :: x2;     (1290 : ℕ) :: (1548 : ℕ) :: (2087 : ℕ) :: (2212 : ℕ) :: x3;   have x4 : List ℕ := (541 : ℕ) :: (660 : ℕ) :: (792 : ℕ) :: (1102 : ℕ) :: (1220 : ℕ) :: x3;   (127 : ℕ) :: (244 : ℕ) :: (314 : ℕ) :: (432 : ℕ) :: x4; ∀ x3 < PEqualNP.Defs.LratEncoding.enc2CubeCount (14 : ℕ) (26 : ℕ), ¬PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc2 (14 : ℕ) (26 : ℕ) (fun (x5 : ℕ) => Decidable.decide (x5 ∈ x1)) (x1 ++ x2) ++ PEqualNP.Defs.LratEncoding.enc2Cube (14 : ℕ) (26 : ℕ) x3) := by
  classical
  intro positive negative cube _ sat
  let rows := positive ++ negative
  let g := fun r : ℕ => decide (r∈positive)
  obtain ⟨asgn,h⟩ := sat
  obtain ⟨F,steps,out⟩ := decode g rows ⟨asgn,fun c hc => h c (List.mem_append_left _ hc)⟩
  let row := fun i : Fin 58 => rows.getD i 0
  let sig := fun (f : ℕ → Bool) => Finset.univ.filter fun i : Fin 58 => f (row i)
  let V := fun j => sig (F j)
  let cols : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
  let S := fun (j : ℕ) (B : Finset (Fin 58)) =>
      B=∅ ∨ B=Finset.univ ∨ (∃ z∈cols, ∀ i : Fin 58, i∈B ↔ z.testBit i.val=true) ∨ ∃ k<j, B=V k
  have checks : (∀ i : Fin 58, row i∈rows) ∧
      (∀ i : Fin 58,g (row i)=decide (i.val<21)) ∧
      (∀ w : Fin 14, cols.getD w 0∈cols ∧ ∀ i : Fin 58, (row i).testBit w.val=(cols.getD w 0).testBit i.val) := by
    decide +kernel
  let read := fun (j w r : ℕ) => if w<14 then r.testBit w else if w<14+j then F (w-14) r else false
  have wire (j w : ℕ) : S j (sig (read j w)) := by
    by_cases raw : w<14
    · obtain ⟨key,ok⟩ := checks.2.2 ⟨w,raw⟩
      refine Or.inr (Or.inr (Or.inl ⟨_,key,?_⟩))
      intro i
      simp [sig,read,raw,ok i]
    · by_cases old : w<14+j
      · exact Or.inr (Or.inr (Or.inr ⟨w-14,by omega,by simp [sig,V,read,raw,old]⟩))
      · exact Or.inl (by simp [sig,read,raw,old])
  have buildStep (j : ℕ) (hj : j<26) : ∃ a b, S j a ∧ S j b ∧ (V j=a∩b ∨ V j=a∪b) := by
    rcases steps j hj with full|⟨u,v,mul|add⟩
    · refine ⟨Finset.univ,Finset.univ,Or.inr (Or.inl rfl),Or.inr (Or.inl rfl),Or.inl ?_⟩
      ext i
      simp [V,sig,full (row i) (checks.1 i)]
    · refine ⟨_,_,wire j u,wire j v,Or.inl ?_⟩
      ext i
      have eq : F j (row i)=(read j u (row i) && read j v (row i)) := mul _ (checks.1 i)
      simp [V,sig,eq]
    · refine ⟨_,_,wire j u,wire j v,Or.inr ?_⟩
      ext i
      have eq : F j (row i)=(read j u (row i) || read j v (row i)) := add _ (checks.1 i)
      simp [V,sig,eq]
  obtain ⟨w,output⟩ := out
  let T := Finset.Iio (21 : Fin 58)
  have wanted : S 26 T := by
    have eq : sig (read 26 w)=T := by
      ext i
      have val : read 26 w (row i)=decide (i.val<21) := (output _ (checks.1 i)).trans (checks.2.1 i)
      simp [sig,T,val,Fin.lt_def]
    rw [←eq];exact wire 26 w
  have sep (j : ℕ) (B : Finset (Fin 58)) (belongs : S (j+1) B) : S j B ∨ B=V j := by
    rcases belongs with z|o|raw|⟨k,hk,eq⟩
    · exact Or.inl (Or.inl z)
    · exact Or.inl (Or.inr (Or.inl o))
    · exact Or.inl (Or.inr (Or.inr (Or.inl raw)))
    · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with lt|rfl
      · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨k,lt,eq⟩)))
      · exact Or.inr eq
  have budget := terminal V (fun j hj => buildStep j (by omega))
  obtain ⟨b,c,hb,hc,inner⟩ := buildStep 24 (by decide)
  have pair (A B : Finset (Fin 58)) (ha : S 24 A) (hB : S 25 B) : A∩B≠T ∧ A∪B≠T := by
    rcases sep 24 B hB with old|rfl
    · apply budget A B B ha old old B
      simp
    · apply budget A b c ha hb hc (V 24)
      simpa only [List.mem_cons,List.not_mem_nil,or_false] using inner
  have absent (A : Finset (Fin 58)) (ha : S 25 A) : A≠T := by
    simpa using (pair Finset.univ A (Or.inr (Or.inl rfl)) ha).1
  rcases sep 25 T wanted with old|final
  · exact absent T old rfl
  obtain ⟨l,r,hl,hr,op⟩ := buildStep 25 (by decide)
  have stop (eqs : l∩r≠T ∧ l∪r≠T) : False := by
    rcases op with h|h
    · exact eqs.1 (h.symm.trans final.symm)
    · exact eqs.2 (h.symm.trans final.symm)
  rcases sep 24 l hl with left|left
  · exact stop (pair l r left hr)
  rcases sep 24 r hr with right|right
  · have h := pair r l right hl
    exact stop ⟨by simpa only [Finset.inter_comm l r] using h.1,by simpa only [Finset.union_comm l r] using h.2⟩
  · have eq : l=r := left.trans right.symm
    apply stop
    rw [←eq]
    simpa using And.intro (absent l hl) (absent l hl)
