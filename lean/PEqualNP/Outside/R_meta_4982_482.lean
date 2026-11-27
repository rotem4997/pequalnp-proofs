import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

-- Two directions name the points by their coordinates. Values on the first
-- vertical line name the symbols, and the value at the unit point names the slopes.
theorem PEqualNP.Outside.R_meta_4982_482
    (axes : ∀ (q : ℕ) [NeZero q] (b : Fin (q+1) → Fin (q*q) → Fin q),
      (∀ i j, i≠j → Function.Bijective fun z => (b i z,b j z)) →
      ∃ (point : (Fin q × Fin q) ≃ Fin (q*q)) (symbol : Fin (q+1) → Fin q ≃ Fin q),
        (∀ z, symbol 0 (b 0 (point z)) = z.1 ∧ symbol 1 (b 1 (point z)) = z.2) ∧
        ∀ i, i≠0 → ∀ y, symbol i (b i (point (0,y))) = y)
    (slopes : ∀ (q : ℕ) [NeZero q] (b : Fin (q+1) → Fin q × Fin q → Fin q),
      2 ≤ q → (∀ i j, i≠j → Function.Bijective fun z => (b i z,b j z)) →
      (∀ z, b 0 z = z.1 ∧ b 1 z = z.2) →
      (∀ i, i≠0 → ∀ y, b i (0,y)=y) →
      ∃ dir : Fin (q+1) ≃ Fin (q+1), dir 0=0 ∧ dir 1=1 ∧ ∀ m : Fin q, b (dir m.succ) (1,0)=m)
    (normalized : ∀ (q : ℕ) [NeZero q] (N : ℕ) (P : Fin q × Fin q ↪ Fin N)
      (L : Fin (q+1) × Fin q ↪ Fin N) (b : Fin (q+1) → Fin q × Fin q → Fin q) (C : Circuit),
      300 ≤ q → (∀ i j, i≠j → Function.Bijective fun z => (b i z,b j z)) →
      (∀ z, b 0 z = z.1 ∧ b 1 z = z.2) → (∀ i, i≠0 → ∀ y, b i (0,y)=y) →
      (∀ m : Fin q, b m.succ (1,0)=m) → Monotone2 C →
      (∀ z i, C.eval (incidenceInput {P z} {L (i,b i z)})=true) →
      (∀ (X : Finset (Fin q × Fin q)) (Y : Finset (Fin (q+1) × Fin q)), Y.card ≤ q →
        (∀ z ∈ X, ∀ i, (i,b i z) ∉ Y) → C.eval (incidenceInput (X.map P) (Y.map L))=false) →
      q^2*(q+1) ≤ 99*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin (x1 * x1) ↪ Fin x2) (x4 : Fin (x1 + (1 : ℕ)) × Fin x1 ↪ Fin x2) (x5 : Fin (x1 + (1 : ℕ)) → Fin (x1 * x1) → Fin x1) (x6 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → (∀ (x8 x9 : Fin (x1 + (1 : ℕ))), x8 ≠ x9 → Function.Bijective fun (x11 : Fin (x1 * x1)) => (x5 x8 x11, x5 x9 x11)) → PEqualNP.MetaComplexity.Monotone2 x6 → (∀ (x10 : Fin (x1 * x1)) (x11 : Fin (x1 + (1 : ℕ))), x6.eval (PEqualNP.GenericRejection.incidenceInput {x3 x10} {x4 (x11, x5 x11 x10)}) = Bool.true) → (∀ (x11 : Finset (Fin (x1 * x1))) (x12 : Finset (Fin (x1 + (1 : ℕ)) × Fin x1)), x12.card ≤ x1 → (∀ x14 ∈ x11, ∀ (x16 : Fin (x1 + (1 : ℕ))), (x16, x5 x16 x14) ∉ x12) → x6.eval (PEqualNP.GenericRejection.incidenceInput (Finset.map x3 x11) (Finset.map x4 x12)) = Bool.false) → x1 ^ (2 : ℕ) * (x1 + (1 : ℕ)) ≤ (99 : ℕ) * x6.size := by
  classical
  intro q N P L b C large orth mono yes no
  let _ : NeZero q := ⟨by omega⟩
  obtain ⟨point,symbol,onAxes,onZero⟩ := axes q b orth
  let w (i : Fin (q+1)) (z : Fin q × Fin q) := symbol i (b i (point z))
  have wOrth (i j : Fin (q+1)) (ij : i≠j) : Function.Bijective (fun z => (w i z,w j z)) := by
    exact ((symbol i).prodCongr (symbol j)).bijective.comp ((orth i j ij).comp point.bijective)
  obtain ⟨dir,d0,d1,calibrate⟩ := slopes q w (by omega) wOrth onAxes onZero
  let v (i : Fin (q+1)) := w (dir i)
  let encode : (Fin (q+1) × Fin q) ↪ (Fin (q+1) × Fin q) :=
    { toFun := fun t => (dir t.1, (symbol (dir t.1)).symm t.2)
      inj' := by
        rintro ⟨i,a⟩ ⟨j,c⟩ h
        have ij : i=j := dir.injective (congrArg Prod.fst h)
        subst j
        exact Prod.ext rfl ((symbol (dir i)).symm.injective (congrArg Prod.snd h)) }
  have code (i) (z) : encode (i,v i z) = (dir i,b (dir i) (point z)) := by
    apply Prod.ext
    · rfl
    · exact (symbol (dir i)).symm_apply_apply _
  apply normalized q N (point.toEmbedding.trans P) (encode.trans L) v C large
  · intro i j different
    exact wOrth _ _ (dir.injective.ne different)
  · intro z
    simpa only [v,d0,d1] using onAxes z
  · intro i different y
    apply onZero (dir i) _ y
    intro eq
    exact different (dir.injective (eq.trans d0.symm))
  · exact calibrate
  · exact mono
  · intro z i
    change C.eval (incidenceInput {P (point z)} {L (encode (i,v i z))})=true
    rw [code]
    exact yes _ _
  · intro X Y small avoids
    rw [← Finset.map_map, ← Finset.map_map]
    apply no (X.map point.toEmbedding) (Y.map encode) (by simpa using small)
    intro raw hraw i mem
    obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp hraw
    obtain ⟨⟨j,t⟩,ht,eq⟩ := Finset.mem_map.mp mem
    have direction : dir j=i := congrArg Prod.fst eq
    subst i
    have pair : encode (j,t)=encode (j,v j z) := eq.trans (code j z).symm
    have value : t=v j z := congrArg Prod.snd (encode.injective pair)
    exact avoids z hz j (value ▸ ht)
