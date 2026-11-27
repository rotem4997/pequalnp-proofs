import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_4865_665
  (compileChart :
    ∀ (n : ℕ) (T : List ((Fin n → Bool) → Bool)),
        let avail := fun (S : List ((Fin n → Bool) → Bool)) (f : (Fin n → Bool) → Bool) =>
          f = (fun _ => false) ∨ (∃ v : Fin n, f = (fun x => x v)) ∨ f ∈ S
        (∀ i : Fin T.length,
          let B := avail (T.take i.val)
          let h := T.get i
          (∃ f, B f ∧ h = fun x => !(f x)) ∨
          (∃ f g, B f ∧ B g ∧ ((h = fun x => f x && g x) ∨ (h = fun x => f x || g x)))) →
        ∀ F, avail T F → PEqualNP.MetaComplexity.HasCircuitSize n F T.length)
  (obstruction :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)),
    let H : Type := (Fin n → Bool) → Bool
    have X : Fin n → H := Function.eval
    let free : H → Prop := fun (f : H) => f = ⊥ ∨ ∃ (v : Fin n), f = X v
    have av : Finset H → H → Prop := fun (U : Finset H) (f : H) => free f ∨ f ∈ U
    have bin : Finset H → H → Prop := fun (U : Finset H) (h : H) =>
      ∃ (b c : H), av U b ∧ av U c ∧ (h = b ⊓ c ∨ h = b ⊔ c)
    have reach : Finset H → H → Prop := fun (B : Finset H) (f : H) =>
      av B f ∧ ∀ U ⊂ B, ∃ h ∈ B, h ∉ U ∧ ((∃ (b : H), av U b ∧ h = bᶜ) ∨ bin U h)
    have cut : Fin n → H → (Fin n → Bool) → Bool := fun (v : Fin n) (f : H) (x : Fin n → Bool) =>
      f (Function.update x v Bool.false)
    let live : H → Prop := fun (f : H) => f ≠ ⊤ ∧ ¬ free f
    have F : (Fin n → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun G A
    (∀ (v : Fin n), G.degree v = if v ∈ A then (0 : ℕ) else (3 : ℕ)) →
    (7 : ℕ∞) ≤ G.egirth →
    ∀ (B M : Finset H) (d : Fin n → ℕ),
    reach B F → (∀ b ∈ B, live b) →
    (∀ (D : Finset H), reach D F → B.card ≤ D.card) →
    M ⊆ B → (∀ U ⊂ B, M ⊆ U → ∃ h ∈ B, h ∉ U ∧ bin U h) →
    (∃ v ∉ A, d v = (2 : ℕ) ∧ (X v)ᶜ ∈ M) →
    (∀ I ⊆ Aᶜ, G.IsIndepSet ↑I →
      (2 : ℕ) * ({v ∉ A | d v = (3 : ℕ)}.card + M.card + I.card + (1 : ℕ)) ≤ Aᶜ.card) →
    (∀ v ∉ A, have k : ℕ := (Finset.filter live (Finset.image (cut v) B)).card
              (2 : ℕ) ≤ d v ∧ k + d v ≤ B.card ∧ B.card ≤ k + (3 : ℕ)) →
    ∃ v ∉ A, ∃ (D : Finset H), reach D (cut v F) ∧ D.card + (4 : ℕ) ≤ B.card) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [_x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ x17 ⊆ x4ᶜ, (∀ (x19 x20 : Fin x1), x2.Adj x19 x20 → x19 ∈ x17 ∨ x20 ∈ x17) → ∑ x20 ∈ x4ᶜ, (x7 x20).length + (List.filter (fun (x20 : PEqualNP.CircuitLowerBounds.Gate) => x20.op.eval [Bool.false]) x5.gates).length < x2.edgeFinset.card + x17.card) → ∃ x18 ∉ x4, ∃ (x19 : ℕ), x19 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x20 : Fin x1 → Bool) => x6 (Function.update x20 x18 Bool.false)) x19 := by
  -- Charge the NOT rows and the third reads to the independent-set deficit, using cubic parity.
  have counting {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (d : Fin n → ℕ) (N : ℕ)
      (hd : ∀ v ∉ A, 2 ≤ d v ∧ d v ≤ 3)
      (hdeg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
      (hoff : ∀ u v, G.Adj u v → u ∉ A)
      (hbudget : ∀ C ⊆ Aᶜ, (∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C) →
        (∑ v ∈ Aᶜ, d v) + N < G.edgeFinset.card + C.card)
      (I : Finset (Fin n)) (hI : I ⊆ Aᶜ)
      (hind : ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) :
      2 * ((Aᶜ.filter (fun v => d v = 3)).card + N + I.card + 1) ≤ Aᶜ.card := by
    have hz : (∑ v ∈ A, G.degree v) = 0 :=
      Finset.sum_eq_zero fun u hu => (G.degree_eq_zero u).mpr fun v huv => hoff u v huv hu
    have hthree : (∑ v ∈ Aᶜ, G.degree v) = Aᶜ.card * 3 := calc
      _ = ∑ _v ∈ Aᶜ, 3 := Finset.sum_congr rfl fun v hv =>
        (G.ncard_neighborSet v).symm.trans (hdeg v (Finset.mem_compl.mp hv))
      _ = _ := by simp
    have he := G.sum_degrees_eq_twice_card_edges
    rw [← A.sum_add_sum_compl, hz, zero_add, hthree] at he
    have hreads : (∑ v ∈ Aᶜ, d v) = Aᶜ.card * 2 + (Aᶜ.filter (fun v => d v = 3)).card := calc
      _ = ∑ v ∈ Aᶜ, (2 + if d v = 3 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro v hv
        obtain ⟨hl, hh⟩ := hd v (Finset.mem_compl.mp hv)
        split <;> omega
      _ = _ := by simp [Finset.sum_add_distrib]
    have hcover := hbudget (Aᶜ \ I) Finset.sdiff_subset (by
      intro u v huv
      by_cases hu : u ∈ I
      · exact Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr (hoff v u huv.symm),
          fun hv => hind u hu v hv huv⟩)
      · exact Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr (hoff u v huv), hu⟩))
    rw [hreads] at hcover
    have hcard := Finset.card_sdiff_add_card_eq_card hI
    omega
  -- Tabulate the actual wires. Each direct reader becomes a trivial or repeated row on its input's zero slice.
  have extractChart : ∀ (n : ℕ) (C : Circuit) (v : Fin n),
      FanInTwo C → (∃ g ∈ C.gates, g.op = GateOp.not ∧ g.inputs.head? = some v.val) →
      let avail := fun (S : List ((Fin n → Bool) → Bool)) (f : (Fin n → Bool) → Bool) =>
        f = (fun _ => false) ∨ (∃ u : Fin n, f = (fun x => x u)) ∨ f ∈ S
      ∃ T : List ((Fin n → Bool) → Bool), T.length = C.size ∧ (fun x => !(x v)) ∈ T ∧
        (∀ i : Fin T.length, let B := avail (T.take i.val); let h := T.get i
          (∃ f, B f ∧ h = fun x => !(f x)) ∨
          (∃ f g, B f ∧ B g ∧ ((h = fun x => f x && g x) ∨ (h = fun x => f x || g x)))) ∧
        avail T (circuitFun n C) ∧
        (∀ w : Fin n, let cut := fun (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) =>
                                f (Function.update x w false)
          ∃ R : Finset (Fin T.length),
            R.card = (C.gates.filter (fun q =>
              (q.inputs.take (bif q.op.eval [false] then 1 else 2)).contains w.val)).length ∧
            ∀ i ∈ R, cut (T.get i) = (fun _ => true) ∨ cut (T.get i) = (fun _ => false) ∨
              (∃ u : Fin n, cut (T.get i) = (fun x => x u)) ∨
              ∃ j : Fin T.length, j < i ∧ cut (T.get i) = cut (T.get j)) ∧
        ∀ x : Fin n → Bool, List.ofFn x ++ T.map (fun f => f x) = C.wires (List.ofFn x) := by
    intro n C v hfan hnot
    classical
    let F := (Fin n → Bool) → Bool
    let z : F := fun _ => false
    let inp : List F := List.ofFn fun (u : Fin n) (x : Fin n → Bool) => x u
    let avail (S : List F) (f : F) := f = z ∨ (∃ u : Fin n, f = (fun x => x u)) ∨ f ∈ S
    let legal (S : List F) (h : F) :=
      (∃ f, avail S f ∧ h = fun x => !(f x)) ∨
      (∃ f g, avail S f ∧ avail S g ∧ ((h = fun x => f x && g x) ∨ (h = fun x => f x || g x)))
    let read (T : List F) (j : ℕ) : F := (inp ++ T).getD j z
    have hra (T : List F) (j : ℕ) : avail T (read T j) := by
      by_cases hj : j < (inp ++ T).length
      · have hm : read T j ∈ inp ++ T := by
          change (inp ++ T).getD j z ∈ _
          rw [List.getD_eq_getElem _ _ hj]
          exact List.getElem_mem _
        rcases List.mem_append.mp hm with h | h
        · obtain ⟨u, hu⟩ := List.mem_ofFn.mp h
          exact Or.inr (Or.inl ⟨u, hu.symm⟩)
        · exact Or.inr (Or.inr h)
      · exact Or.inl (List.getD_eq_default _ _ (by omega))
    have hrv (T : List F) (v : Fin n) : read T v.val = fun x => x v := by
      have hi : v.val < inp.length := by simp [inp]
      change (inp ++ T).getD v.val z = _
      rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
      exact List.getElem_ofFn _
    let gate (T : List F) (q : Gate) : F := fun x =>
      q.op.eval (q.inputs.map fun j => read T j x)
    let step (w : List Bool) (q : Gate) := w ++ [q.op.eval (q.inputs.map fun j => w.getD j false)]
    let basis (q : Gate) := (q.op = .and ∨ q.op = .or ∨ q.op = .not) ∧ q.inputs.length ≤ 2
    have hlegal (T : List F) (q : Gate) (hq : basis q) : legal T (gate T q) := by
      obtain ⟨op, ins⟩ := q
      obtain ⟨hb, hl⟩ := hq
      change op = .and ∨ op = .or ∨ op = .not at hb
      change ins.length ≤ 2 at hl
      have hz : avail T z := Or.inl rfl
      cases ins with
      | nil =>
        rcases hb with rfl | rfl | rfl
        · exact Or.inl ⟨z, hz, rfl⟩
        · exact Or.inr ⟨z, z, hz, hz, Or.inl rfl⟩
        · exact Or.inl ⟨z, hz, rfl⟩
      | cons a tl =>
        cases tl with
        | nil =>
          rcases hb with rfl | rfl | rfl
          · refine Or.inr ⟨_, _, hra T a, hra T a, Or.inl ?_⟩
            funext x
            change (read T a x && true) = (read T a x && read T a x)
            simp
          · refine Or.inr ⟨_, _, hra T a, hra T a, Or.inr ?_⟩
            funext x
            change (read T a x || false) = (read T a x || read T a x)
            simp
          · exact Or.inl ⟨_, hra T a, rfl⟩
        | cons b tail =>
          cases tail with
          | nil =>
            rcases hb with rfl | rfl | rfl
            · refine Or.inr ⟨_, _, hra T a, hra T b, Or.inl ?_⟩
              funext x
              change (read T a x && (read T b x && true)) = _
              simp
            · refine Or.inr ⟨_, _, hra T a, hra T b, Or.inr ?_⟩
              funext x
              change (read T a x || (read T b x || false)) = _
              simp
            · exact Or.inl ⟨_, hra T a, rfl⟩
          | cons c s => simp at hl
    let hit (w : Fin n) (q : Gate) :=
      (q.inputs.take (bif q.op.eval [false] then 1 else 2)).contains w.val
    let cut (w : Fin n) (f : F) : F := fun x => f (Function.update x w false)
    let coll (w : Fin n) (S : List F) (h : F) :=
      cut w h = (fun _ => true) ∨ cut w h = z ∨ (∃ u : Fin n, cut w h = (fun x => x u)) ∨
      ∃ f ∈ S, cut w h = cut w f
    have hgate (T : List F) (q : Gate) (hq : basis q) (w : Fin n) (hh : hit w q) :
        coll w T (gate T q) := by
      have hv (x : Fin n → Bool) : read T w.val (Function.update x w false) = false := by
        rw [hrv]
        exact Function.update_self ..
      have other (f : F) (k : ℕ) (he : cut w f = cut w (read T k)) : coll w T f := by
        rcases hra T k with hz | ⟨u, hu⟩ | hm
        · rw [hz] at he
          exact Or.inr (Or.inl he)
        · rw [hu] at he
          by_cases eu : u = w
          · subst u
            exact Or.inr (Or.inl (he.trans (funext fun x => Function.update_self ..)))
          · exact Or.inr (Or.inr (Or.inl ⟨u, he.trans (funext fun x => Function.update_of_ne eu ..)⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨_, hm, he⟩))
      obtain ⟨op, ins⟩ := q
      obtain ⟨hb, hl⟩ := hq
      change op = .and ∨ op = .or ∨ op = .not at hb
      change ins.length ≤ 2 at hl
      cases ins with
      | nil =>
        rcases hb with rfl | rfl | rfl <;> contradiction
      | cons a tail =>
        cases tail with
        | nil =>
          rcases hb with rfl | rfl | rfl
          all_goals
            change ([a] : List ℕ).contains w.val = true at hh
            have ha : a = w.val := by simpa [eq_comm] using hh
            subst a
          · refine Or.inr (Or.inl (funext fun x => ?_))
            change (read T w.val (Function.update x w false) && true) = false
            rw [hv]; rfl
          · refine Or.inr (Or.inl (funext fun x => ?_))
            change (read T w.val (Function.update x w false) || false) = false
            rw [hv]; rfl
          · refine Or.inl (funext fun x => ?_)
            change (!(read T w.val (Function.update x w false))) = true
            rw [hv]; rfl
        | cons b tail =>
          cases tail with
          | cons c tail => simp at hl
          | nil =>
            rcases hb with rfl | rfl | rfl
            · change ([a,b] : List ℕ).contains w.val = true at hh
              have hab : w.val = a ∨ w.val = b := by simpa using hh
              refine Or.inr (Or.inl (funext fun x => ?_))
              change (read T a (Function.update x w false) &&
                (read T b (Function.update x w false) && true)) = false
              rcases hab with e | e <;> rw [← e, hv] <;> simp
            · change ([a,b] : List ℕ).contains w.val = true at hh
              have hab : w.val = a ∨ w.val = b := by simpa using hh
              rcases hab with e | e
              · apply other _ b
                funext x
                change (read T a (Function.update x w false) ||
                  (read T b (Function.update x w false) || false)) = _
                rw [← e, hv]; simp [cut]
              · apply other _ a
                funext x
                change (read T a (Function.update x w false) ||
                  (read T b (Function.update x w false) || false)) = _
                rw [← e, hv]; simp [cut]
            · change ([a] : List ℕ).contains w.val = true at hh
              have ha : a = w.val := by simpa [eq_comm] using hh
              refine Or.inl (funext fun x => ?_)
              change (!(read T a (Function.update x w false))) = true
              rw [ha, hv]; rfl
    have build (gs : List Gate) (hgs : ∀ g ∈ gs, basis g) :
        ∃ T : List F, T.length = gs.length ∧
          ((∃ g ∈ gs, g.op = GateOp.not ∧ g.inputs.head? = some v.val) → (fun x => !(x v)) ∈ T) ∧
          (∀ i : Fin T.length, legal (T.take i.val) (T.get i)) ∧
          (∀ k (hg : k < gs.length) (ht : k < T.length) (w : Fin n),
            hit w gs[k] → coll w (T.take k) T[k]) ∧
          ∀ x, (inp ++ T).map (fun f => f x) = gs.foldl step (List.ofFn x) := by
      induction gs using List.reverseRecOn with
      | nil =>
        refine ⟨[], rfl, by simp, fun i => Fin.elim0 i, by simp, ?_⟩
        intro x
        simp [inp, List.map_ofFn, Function.comp_def]
      | append_singleton gs q ih =>
        obtain ⟨T, hlen, hmark, hadm, htag, hmap⟩ := ih (fun g hg => hgs g (List.mem_append_left _ hg))
        refine ⟨T ++ [gate T q], by simp [hlen], ?_, ?_, ?_, ?_⟩
        · rintro ⟨r, hr, hop, hhead⟩
          rcases List.mem_append.mp hr with h | h
          · exact List.mem_append_left _ (hmark ⟨r, h, hop, hhead⟩)
          · have e : r = q := List.mem_singleton.mp h
            subst r
            have eqn : gate T q = (fun x => !(x v)) := by
              funext x
              change q.op.eval (q.inputs.map _) = _
              rw [hop]
              cases he : q.inputs with
              | nil => simp [he] at hhead
              | cons a tl =>
                have ha : a = v.val := by simpa [he] using hhead
                subst a
                change (!(read T v.val x)) = _
                rw [hrv]
            exact List.mem_append_right _ (List.mem_singleton.mpr eqn.symm)
        · intro i
          change legal ((T ++ [_]).take i.val) ((T ++ [_])[i.val])
          by_cases hi : i.val < T.length
          · rw [List.take_append_of_le_length (Nat.le_of_lt hi), List.getElem_append_left hi]
            exact hadm ⟨_, hi⟩
          · have he : i.val = T.length := by
              have := i.isLt
              simp only [List.length_append, List.length_singleton] at this
              omega
            simp [List.getElem_append_right, he]
            exact hlegal T q (hgs q (by simp))
        · intro k hg ht w hh
          by_cases hk : k < T.length
          · have hk' : k < gs.length := hlen ▸ hk
            rw [List.getElem_append_left hk'] at hh
            rw [List.getElem_append_left hk, List.take_append_of_le_length hk.le]
            exact htag k hk' hk w hh
          · have he : k = T.length := by simp at ht; omega
            subst k
            have hq : hit w q := by simpa [hlen, List.getElem_append_right] using hh
            simpa [List.getElem_append_right] using hgate T q (hgs q (by simp)) w hq
        · intro x
          rw [← List.append_assoc, List.map_append, hmap, List.foldl_append]
          change _ ++ [gate T q x] = _ ++ [q.op.eval (q.inputs.map _)]
          congr 2
          change q.op.eval (q.inputs.map _) = _
          congr 1
          apply List.map_congr_left
          intro j _
          rw [← hmap x]
          exact (List.getD_map (inp ++ T) z (fun f => f x)).symm
    obtain ⟨T, hlen, hmark, hadm, htag, hmap⟩ := build C.gates (fun g hg => hfan g hg)
    have wires (x : Fin n → Bool) :
        List.ofFn x ++ T.map (fun f => f x) = C.wires (List.ofFn x) := by
      change _ = C.gates.foldl step (List.ofFn x)
      simpa only [List.map_append, inp, List.map_ofFn, Function.comp_def] using hmap x
    refine ⟨T, hlen, hmark hnot, hadm, ?_, ?_, wires⟩
    swap
    · intro w
      let p (i : Fin T.length) := hit w (C.gates.get (Fin.cast hlen i))
      refine ⟨Finset.univ.filter (fun i => p i = true), ?_, ?_⟩
      · have count (S : List Gate) (k : ℕ) (hk : k = S.length) :
            (Finset.univ.filter (fun i : Fin k => hit w (S.get (Fin.cast hk i)) = true)).card =
            (S.filter (hit w)).length := by
          let V : List.Vector Gate k := ⟨S, hk.symm⟩
          rw [← List.countP_eq_length_filter]
          exact (List.Vector.countP_toList (hit w) V).symm
        exact count C.gates T.length hlen
      · intro i hi
        have hc := htag i.val (hlen ▸ i.isLt) i.isLt w (Finset.mem_filter.mp hi).2
        rcases hc with ht | hz | hp | ⟨f, hf, he⟩
        · exact Or.inl ht
        · exact Or.inr (Or.inl hz)
        · exact Or.inr (Or.inr (Or.inl hp))
        · obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hf
          exact Or.inr (Or.inr (Or.inr ⟨⟨j, (lt_min_iff.mp hj).2⟩, (lt_min_iff.mp hj).1, he⟩))
    have he : circuitFun n C = read T C.output := by
      funext x
      change (C.gates.foldl step (List.ofFn x)).getD C.output false = _
      rw [← hmap]
      exact List.getD_map _ z (fun f => f x)
    rw [he]
    exact hra T C.output
  -- Keep a row only when it adds a new function. The same sweep works after coordinate restriction.
  have pruneChart (n : ℕ) :
      let T := (Fin n → Bool) → Bool
      let avail := fun (S : List T) (f : T) =>
        f = (fun _ => false) ∨ (∃ v : Fin n, f = (fun x => x v)) ∨ f ∈ S
      let step := fun (S : List T) (h : T) =>
        (∃ f, avail S f ∧ h = (fun x => !(f x))) ∨
        (∃ f g, avail S f ∧ avail S g ∧
          (h = (fun x => f x && g x) ∨ h = (fun x => f x || g x)))
      let admissible := fun (S : List T) => ∀ i : Fin S.length, step (S.take i.val) (S.get i)
      let clean := fun (S : List T) (F : T) =>
        ∃ U, admissible U ∧ avail U F ∧ U.Nodup ∧ (∀ f ∈ U, ¬avail [] f) ∧ U.Sublist S
      (∀ S F, admissible S → avail S F → clean S F) ∧
        (∀ S F, admissible S → avail S F → ∀ v : Fin n,
          let slice := fun (f : T) (x : Fin n → Bool) => f (Function.update x v false)
          clean (S.map slice) (slice F)) := by
    classical
    intro T avail step admissible clean
    have snoc (S : List T) (a : T) :
        admissible (S ++ [a]) ↔ admissible S ∧ step S a := by
      have left (j : ℕ) (hj : j < S.length) (hk : j < (S ++ [a]).length) :
          step ((S ++ [a]).take j) ((S ++ [a]).get ⟨j, hk⟩) ↔
            step (S.take j) (S.get ⟨j, hj⟩) := by
        simp only [List.get_eq_getElem, List.getElem_append_left hj,
          List.take_append_of_le_length hj.le]
      have last (hk : S.length < (S ++ [a]).length) :
          step ((S ++ [a]).take S.length) ((S ++ [a]).get ⟨S.length, hk⟩) ↔ step S a := by
        simp [List.get_eq_getElem, List.getElem_append_right (Nat.le_refl S.length)]
      constructor
      · intro h
        exact ⟨fun i => (left i.val i.isLt (by simp)).mp (h ⟨i.val, by simp⟩),
          (last (by simp)).mp (h ⟨S.length, by simp⟩)⟩
      · rintro ⟨hs, ha⟩ ⟨i, hi⟩
        by_cases h : i < S.length
        · exact (left i h hi).mpr (hs ⟨i, h⟩)
        · have he : i = S.length := by simp at hi; omega
          subst i
          exact (last hi).mpr ha
    have push (S : List T) (a f : T) : avail (S ++ [a]) f ↔ avail S f ∨ f = a := by
      simp only [avail, List.mem_append, List.mem_singleton]
      tauto
    have transfer (S U : List T) (a : T) (h : ∀ f, avail S f → avail U f) :
        step S a → step U a := by
      rintro (⟨f, hf, he⟩ | ⟨f, g, hf, hg, he⟩)
      · exact Or.inl ⟨f, h f hf, he⟩
      · exact Or.inr ⟨f, g, h f hf, h g hg, he⟩
    have sweep (S : List T) : admissible S →
        ∃ U, admissible U ∧ (∀ f, avail S f → avail U f) ∧ U.Nodup ∧
          (∀ f ∈ U, ¬avail [] f) ∧ U.Sublist S := by
      induction S using List.reverseRecOn with
      | nil =>
        intro hs
        exact ⟨[], hs, fun _ h => h, by simp, by simp, .refl _⟩
      | append_singleton S a ih =>
        intro hs
        obtain ⟨hS, ha⟩ := (snoc S a).mp hs
        obtain ⟨U, hu, hmap, hnd, hfree, hsub⟩ := ih hS
        by_cases h : avail U a
        · refine ⟨U, hu, ?_, hnd, hfree, List.sublist_append_of_sublist_left hsub⟩
          intro f hf
          rcases (push S a f).mp hf with hf | rfl
          · exact hmap f hf
          · exact h
        · have hnot : a ∉ U := fun hm => h (Or.inr (Or.inr hm))
          have hnf : ¬avail [] a := by
            rintro (hc | hv | hm)
            · exact h (Or.inl hc)
            · exact h (Or.inr (Or.inl hv))
            · exact List.not_mem_nil hm
          refine ⟨U ++ [a], (snoc U a).mpr ⟨hu, transfer S U a hmap ha⟩, ?_,
            ?_, ?_, hsub.append_right [a]⟩
          · intro f hf
            exact (push U a f).mpr (((push S a f).mp hf).imp_left (hmap f))
          · refine List.nodup_append.mpr ⟨hnd, by simp, ?_⟩
            intro b hb c hc e
            exact hnot ((e.trans (List.mem_singleton.mp hc)) ▸ hb)
          · intro f hf
            rcases List.mem_append.mp hf with hm | hm
            · exact hfree f hm
            · exact (List.mem_singleton.mp hm) ▸ hnf
    have prune (S : List T) (F : T) (hs : admissible S) (hf : avail S F) : clean S F := by
      obtain ⟨U, hu, hmap, hnd, hfree, hsub⟩ := sweep S hs
      exact ⟨U, hu, hmap F hf, hnd, hfree, hsub⟩
    refine ⟨prune, ?_⟩
    intro S F hs hf v slice
    have liftAvail (L : List T) (f : T) : avail L f → avail (L.map slice) (slice f) := by
      rintro (rfl | ⟨w, rfl⟩ | hm)
      · exact Or.inl rfl
      · by_cases hw : w = v
        · subst w
          exact Or.inl (funext fun x => Function.update_self ..)
        · exact Or.inr (Or.inl ⟨w, funext fun x => Function.update_of_ne hw ..⟩)
      · exact Or.inr (Or.inr (List.mem_map_of_mem hm))
    apply prune _ _ _ (liftAvail S F hf)
    intro i
    let j : Fin S.length := ⟨i.val, by simpa using i.isLt⟩
    have he : (S.map slice).get i = slice (S.get j) := by simp [j, List.get_eq_getElem]
    rw [he, ← List.map_take]
    rcases hs j with ⟨f, h, e⟩ | ⟨f, g, h, k, e | e⟩
    · exact Or.inl ⟨slice f, liftAvail _ _ h, congrArg slice e⟩
    · exact Or.inr ⟨slice f, slice g, liftAvail _ _ h, liftAvail _ _ k, Or.inl (congrArg slice e)⟩
    · exact Or.inr ⟨slice f, slice g, liftAvail _ _ h, liftAvail _ _ k, Or.inr (congrArg slice e)⟩
  -- An unordered family is generable exactly when every proper subset admits a legal new row.
  have frontier {α : Type} [DecidableEq α]
      (D : Finset α → α → Prop)
      (mono : ∀ {U V : Finset α} {f : α}, U ⊆ V → D U f → D V f) :
      (∀ S : List α, (∀ i : Fin S.length, D (S.take i.val).toFinset (S.get i)) →
        ∀ U ⊂ S.toFinset, ∃ f ∈ S.toFinset, f ∉ U ∧ D U f) ∧
      (∀ B : Finset α, (∀ U ⊂ B, ∃ f ∈ B, f ∉ U ∧ D U f) →
        ∃ T : List α, T.Nodup ∧ T.toFinset = B ∧
          ∀ i : Fin T.length, D (T.take i.val).toFinset (T.get i)) := by
    classical
    constructor
    · intro S hS U hU
      let P (j : ℕ) := ∃ hj : j < S.length, S[j] ∉ U
      have hex : ∃ j, P j := by
        obtain ⟨f, hf, hu⟩ := Finset.exists_mem_notMem_of_card_lt_card (Finset.card_lt_card hU)
        obtain ⟨j, hj, heq⟩ := List.getElem_of_mem (List.mem_toFinset.mp hf)
        exact ⟨j, hj, heq ▸ hu⟩
      let k := Nat.find hex
      obtain ⟨hk, hout⟩ := Nat.find_spec hex
      refine ⟨S[k], List.mem_toFinset.mpr (List.getElem_mem _), hout, mono ?_ (hS ⟨k, hk⟩)⟩
      intro a ha
      obtain ⟨j, hj, heq⟩ := List.mem_take_iff_getElem.mp (List.mem_toFinset.mp ha)
      change j < min k S.length at hj
      subst a
      by_contra hn
      exact Nat.find_min hex (show j < k by omega) ⟨by omega, hn⟩
    · intro B frontier
      let legal (S : List α) := ∀ i : Fin S.length, D (S.take i.val).toFinset (S.get i)
      suffices extend : ∀ n (S : List α), B.card - S.length = n →
          S.Nodup → S.toFinset ⊆ B → legal S →
          ∃ T : List α, T.Nodup ∧ T.toFinset = B ∧ legal T by
        exact extend B.card [] (by simp) (by simp) (by simp) (fun i => Fin.elim0 i)
      intro n
      induction n using Nat.strong_induction_on with
      | ind n ih =>
        intro S hn hnod hsub hlegal
        by_cases heq : S.toFinset = B
        · exact ⟨S, hnod, heq, hlegal⟩
        have hlt := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, heq⟩
        obtain ⟨f, hf, hnew, hD⟩ := frontier S.toFinset hlt
        have hfresh : f ∉ S := by simpa using hnew
        have hlen : S.length < B.card := by
          simpa [List.toFinset_card_of_nodup hnod] using Finset.card_lt_card hlt
        apply ih (B.card - (S ++ [f]).length) (by simp; omega) (S ++ [f]) rfl
        · exact List.nodup_append.mpr ⟨hnod, by simp, by
            intro a ha b hb
            simp only [List.mem_singleton] at hb
            intro hab
            exact hfresh (by simpa only [hab, hb] using ha)⟩
        · intro a ha
          rcases List.mem_append.mp (List.mem_toFinset.mp ha) with ha | ha
          · exact hsub (List.mem_toFinset.mpr ha)
          · simp only [List.mem_singleton] at ha
            exact ha ▸ hf
        · intro i
          change D ((S ++ [f]).take i.val).toFinset (S ++ [f])[i.val]
          by_cases hi : i.val < S.length
          · rw [List.take_append_of_le_length (Nat.le_of_lt hi), List.getElem_append_left hi]
            exact hlegal ⟨i.val, hi⟩
          · have hbound := i.isLt
            simp only [List.length_append, List.length_cons, List.length_nil] at hbound
            have he : i.val = S.length := by omega
            rw [List.take_append_of_le_length (by omega), List.getElem_append_right (by omega)]
            simpa [he] using hD
  -- The graph function and its zero slices reject the zero assignment, so constant true need not be stored.
  have pruneTrue (n : ℕ) :
      let H := (Fin n → Bool) → Bool
      let avail := fun (S : List H) (f : H) =>
        f = (fun _ => false) ∨ (∃ v : Fin n, f = (fun x => x v)) ∨ f ∈ S
      let step := fun (S : List H) (h : H) =>
        (∃ f, avail S f ∧ h = (fun x => !(f x))) ∨
        (∃ f g, avail S f ∧ avail S g ∧
          (h = (fun x => f x && g x) ∨ h = (fun x => f x || g x)))
      let admissible := fun (S : List H) => ∀ i : Fin S.length, step (S.take i.val) (S.get i)
      ∀ S F, admissible S → avail S F → F ≠ (fun _ => true) →
        ∃ U, admissible U ∧ avail U F ∧ U.Sublist S ∧ ∀ b ∈ U, b ≠ (fun _ => true) := by
    classical
    intro H avail step admissible
    have snoc (S : List H) (a : H) :
        admissible (S ++ [a]) ↔ admissible S ∧ step S a := by
      have left (j : ℕ) (hj : j < S.length) (hk : j < (S ++ [a]).length) :
          step ((S ++ [a]).take j) ((S ++ [a]).get ⟨j, hk⟩) ↔
            step (S.take j) (S.get ⟨j, hj⟩) := by
        simp only [List.get_eq_getElem, List.getElem_append_left hj,
          List.take_append_of_le_length hj.le]
      have last (hk : S.length < (S ++ [a]).length) :
          step ((S ++ [a]).take S.length) ((S ++ [a]).get ⟨S.length, hk⟩) ↔ step S a := by
        simp [List.get_eq_getElem, List.getElem_append_right (Nat.le_refl S.length)]
      constructor
      · intro h
        exact ⟨fun i => (left i.val i.isLt (by simp)).mp (h ⟨i.val, by simp⟩),
          (last (by simp)).mp (h ⟨S.length, by simp⟩)⟩
      · rintro ⟨hs, ha⟩ ⟨i, hi⟩
        by_cases h : i < S.length
        · exact (left i h hi).mpr (hs ⟨i, h⟩)
        · have he : i = S.length := by simp at hi; omega
          subst i
          exact (last hi).mpr ha
    have push (S : List H) (a f : H) : avail (S ++ [a]) f ↔ avail S f ∨ f = a := by
      simp only [avail, List.mem_append, List.mem_singleton]
      tauto
    let top : H := fun _ => true
    have transfer (S U : List H) (a : H) (ha : a ≠ top)
        (keep : ∀ f, avail S f → f ≠ top → avail U f) :
        step S a → avail U a ∨ step U a := by
      rintro (⟨f, hf, e⟩ | ⟨f, g, hf, hg, e⟩)
      · by_cases h : f = top
        · exact Or.inl (Or.inl (by simpa [h, top] using e))
        · exact Or.inr (Or.inl ⟨f, keep f hf h, e⟩)
      · by_cases h : f = top
        · rcases e with e | e
          · have eq : a = g := by simpa [h, top] using e
            exact Or.inl (eq ▸ keep g hg (eq ▸ ha))
          · exact (ha (by simpa [h, top] using e)).elim
        · by_cases k : g = top
          · rcases e with e | e
            · have eq : a = f := by simpa [k, top] using e
              exact Or.inl (eq ▸ keep f hf (eq ▸ ha))
            · exact (ha (by simpa [k, top] using e)).elim
          · exact Or.inr (Or.inr ⟨f, g, keep f hf h, keep g hg k, e⟩)
    have sweep (S : List H) : admissible S →
        ∃ U, admissible U ∧ (∀ f, avail S f → f ≠ top → avail U f) ∧
          U.Sublist S ∧ ∀ b ∈ U, b ≠ top := by
      induction S using List.reverseRecOn with
      | nil =>
        exact fun hs => ⟨[], hs, fun _ hf _ => hf, .refl _, by simp⟩
      | append_singleton S a ih =>
        intro hs
        obtain ⟨hs, hstep⟩ := (snoc S a).mp hs
        obtain ⟨U, hu, keep, sub, clean⟩ := ih hs
        by_cases add : a ≠ top ∧ ¬avail U a
        · have legal := (transfer S U a add.1 keep hstep).resolve_left add.2
          refine ⟨U ++ [a], (snoc U a).mpr ⟨hu, legal⟩, ?_, sub.append_right _, ?_⟩
          · intro f hf hne
            exact (push U a f).mpr (((push S a f).mp hf).imp_left (fun h => keep f h hne))
          · intro b hb
            rcases List.mem_append.mp hb with h | h
            · exact clean b h
            · exact (List.mem_singleton.mp h) ▸ add.1
        · refine ⟨U, hu, ?_, List.sublist_append_of_sublist_left sub, clean⟩
          intro f hf hne
          rcases (push S a f).mp hf with h | rfl
          · exact keep f h hne
          · by_contra h
            exact add ⟨hne, h⟩
    intro S F hs hf hne
    obtain ⟨U, hu, keep, sub, clean⟩ := sweep S hs
    exact ⟨U, hu, keep F hf hne, sub, clean⟩
  -- Charge each surviving slice function to its first occurrence; none can be charged to a direct reader.
  have leastRows {α β : Type} [DecidableEq α] [DecidableEq β]
      (T : List α) (cut : α → β) (p : β → Prop) [DecidablePred p]
      (R : Finset (Fin T.length))
      (hR : ∀ i ∈ R, ¬p (cut (T.get i)) ∨
        ∃ j < i, cut (T.get j) = cut (T.get i)) :
      ((T.toFinset.image cut).filter p).card + R.card ≤ T.length := by
    classical
    let f (i : Fin T.length) := cut (T.get i)
    have sub : (T.toFinset.image cut).filter p ⊆ Rᶜ.image f := by
      intro b hb
      obtain ⟨him, hp⟩ := Finset.mem_filter.mp hb
      obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp him
      obtain ⟨k, hk⟩ := List.get_of_mem (List.mem_toFinset.mp ha)
      let S := Finset.univ.filter fun i => f i = b
      have hS : S.Nonempty :=
        ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (congrArg cut hk).trans hab⟩⟩
      let i := S.min' hS
      have hi : f i = b := (Finset.mem_filter.mp (S.min'_mem hS)).2
      refine Finset.mem_image.mpr ⟨i, Finset.mem_compl.mpr ?_, hi⟩
      intro hir
      rcases hR i hir with hn | ⟨j, hj, he⟩
      · exact hn ((congrArg p hi).mpr hp)
      · exact (not_lt_of_ge (S.min'_le j (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, he.trans hi⟩))) hj
    calc
      _ ≤ (Rᶜ.image f).card + R.card := Nat.add_le_add_right (Finset.card_le_card sub) _
      _ ≤ Rᶜ.card + R.card := Nat.add_le_add_right Finset.card_image_le _
      _ = T.length := by simp only [Finset.card_compl_add_card, Fintype.card_fin]
  -- Only NOT outputs need be supplied as seeds to generate the family by binary lattice operations.
  have seedRows (n : ℕ) (C : Circuit) (T : List ((Fin n → Bool) → Bool))
      (hfan : FanInTwo C)
      (hcanon : ∀ x, List.ofFn x ++ T.map (fun f => f x) = C.wires (List.ofFn x)) :
      let H := (Fin n → Bool) → Bool
      let av := fun (U : Finset H) (f : H) =>
        f = (fun _ => false) ∨ (∃ u : Fin n, f = (fun x => x u)) ∨ f ∈ U
      let bin := fun (U : Finset H) (h : H) =>
        ∃ f g, av U f ∧ av U g ∧ ((h = fun x => f x && g x) ∨ (h = fun x => f x || g x))
      ∃ R : List H, R.length = (C.gates.filter (fun q => q.op.eval [false])).length ∧
        R ⊆ T ∧
        (∀ (v : Fin n), (∃ g ∈ C.gates, g.op = GateOp.not ∧ g.inputs.head? = some v.val) →
          (fun x => !(x v)) ∈ R) ∧
        (∀ i : Fin T.length, T.get i ∈ R ∨ T.get i = (fun _ => true) ∨
          bin (T.take i.val).toFinset (T.get i)) ∧
        R.toFinset.card ≤ (C.gates.filter (fun q => q.op.eval [false])).length ∧
        ((fun _ => true) ∉ T →
          ∀ U ⊂ T.toFinset, R.toFinset ⊆ U → ∃ h ∈ T.toFinset, h ∉ U ∧ bin U h) := by
    classical
    let H := (Fin n → Bool) → Bool
    let z : H := fun _ => false
    let inp : List H := List.ofFn fun (u : Fin n) (x : Fin n → Bool) => x u
    let av (U : Finset H) (f : H) := f = z ∨ (∃ u : Fin n, f = (fun x => x u)) ∨ f ∈ U
    let bin (U : Finset H) (h : H) :=
      ∃ f g, av U f ∧ av U g ∧ ((h = fun x => f x && g x) ∨ (h = fun x => f x || g x))
    let read (S : List H) (j : ℕ) : H := (inp ++ S).getD j z
    have hra (S : List H) (j : ℕ) : av S.toFinset (read S j) := by
      by_cases hj : j < (inp ++ S).length
      · have hm : read S j ∈ inp ++ S := by
          change (inp ++ S).getD j z ∈ _
          rw [List.getD_eq_getElem _ _ hj]
          exact List.getElem_mem _
        rcases List.mem_append.mp hm with h | h
        · obtain ⟨u, hu⟩ := List.mem_ofFn.mp h
          exact Or.inr (Or.inl ⟨u, hu.symm⟩)
        · exact Or.inr (Or.inr (List.mem_toFinset.mpr h))
      · exact Or.inl (List.getD_eq_default _ _ (by omega))
    have hrv (S : List H) (v : Fin n) : read S v.val = fun x => x v := by
      have hi : v.val < inp.length := by simp [inp]
      change (inp ++ S).getD v.val z = _
      rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
      exact List.getElem_ofFn _
    let gate (S : List H) (q : Gate) : H := fun x =>
      q.op.eval (q.inputs.map fun j => read S j x)
    let step (w : List Bool) (q : Gate) := w ++ [q.op.eval (q.inputs.map fun j => w.getD j false)]
    let basis (q : Gate) := (q.op = .and ∨ q.op = .or ∨ q.op = .not) ∧ q.inputs.length ≤ 2
    let neg (q : Gate) := q.op.eval [false]
    have hlegal (S : List H) (q : Gate) (hq : basis q) (hn : neg q = false) :
        gate S q = (fun _ => true) ∨ bin S.toFinset (gate S q) := by
      obtain ⟨op, ins⟩ := q
      obtain ⟨hb, hl⟩ := hq
      change op = .and ∨ op = .or ∨ op = .not at hb
      change ins.length ≤ 2 at hl
      have hz : av S.toFinset z := Or.inl rfl
      have hb' : op = .and ∨ op = .or := by
        rcases hb with h | h | rfl
        · exact Or.inl h
        · exact Or.inr h
        · contradiction
      cases ins with
      | nil =>
        rcases hb' with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr ⟨z, z, hz, hz, Or.inl rfl⟩
      | cons a tl =>
        cases tl with
        | nil =>
          rcases hb' with rfl | rfl
          · refine Or.inr ⟨_, _, hra S a, hra S a, Or.inl ?_⟩
            funext x
            change (read S a x && true) = (read S a x && read S a x)
            simp
          · refine Or.inr ⟨_, _, hra S a, hra S a, Or.inr ?_⟩
            funext x
            change (read S a x || false) = (read S a x || read S a x)
            simp
        | cons b tail =>
          cases tail with
          | nil =>
            rcases hb' with rfl | rfl
            · refine Or.inr ⟨_, _, hra S a, hra S b, Or.inl ?_⟩
              funext x
              change (read S a x && (read S b x && true)) = _
              simp
            · refine Or.inr ⟨_, _, hra S a, hra S b, Or.inr ?_⟩
              funext x
              change (read S a x || (read S b x || false)) = _
              simp
          | cons c s => simp at hl
    have build (gs : List Gate) (hgs : ∀ g ∈ gs, basis g) :
        ∃ S R : List H, R.length = (gs.filter neg).length ∧ R ⊆ S ∧
          (∀ (v : Fin n), (∃ g ∈ gs, g.op = GateOp.not ∧ g.inputs.head? = some v.val) →
            (fun x => !(x v)) ∈ R) ∧
          (∀ i : Fin S.length, S.get i ∈ R ∨ S.get i = (fun _ => true) ∨
            bin (S.take i.val).toFinset (S.get i)) ∧
          ∀ x, (inp ++ S).map (fun f => f x) = gs.foldl step (List.ofFn x) := by
      induction gs using List.reverseRecOn with
      | nil =>
        refine ⟨[], [], rfl, fun _ h => h, by simp, fun i => Fin.elim0 i, ?_⟩
        intro x
        simp [inp, List.map_ofFn, Function.comp_def]
      | append_singleton gs q ih =>
        obtain ⟨S, R, hlen, hsub, hmark, hadm, hmap⟩ := ih (fun g hg => hgs g (List.mem_append_left _ hg))
        let D : List H := if neg q then [gate S q] else []
        have old {a : H} (h : a ∈ R) : a ∈ R ++ D := List.mem_append_left _ h
        have new (hn : neg q = true) : gate S q ∈ R ++ D := by simp [D, hn]
        refine ⟨S ++ [gate S q], R ++ D, ?_, ?_, ?_, ?_, ?_⟩
        · cases hn : neg q <;> simp [D, List.filter_append, hn, hlen]
        · intro a ha
          rcases List.mem_append.mp ha with h | h
          · exact List.mem_append_left _ (hsub h)
          · cases hn : neg q <;> simp [D, hn] at h
            simp [h]
        · rintro v ⟨r, hr, hop, hhead⟩
          rcases List.mem_append.mp hr with h | h
          · exact old (hmark v ⟨r, h, hop, hhead⟩)
          · have e : r = q := List.mem_singleton.mp h
            subst r
            have eqn : gate S q = (fun x => !(x v)) := by
              funext x
              change q.op.eval (q.inputs.map _) = _
              rw [hop]
              cases he : q.inputs with
              | nil => simp [he] at hhead
              | cons a tl =>
                have ha : a = v.val := by simpa [he] using hhead
                subst a
                change (!(read S v.val x)) = _
                rw [hrv]
            rw [← eqn]
            apply new
            change q.op.eval [false] = true
            rw [hop]
            rfl
        · intro i
          change (S ++ [_])[i.val] ∈ R ++ D ∨ (S ++ [_])[i.val] = _ ∨
            bin ((S ++ [_]).take i.val).toFinset (S ++ [_])[i.val]
          by_cases hi : i.val < S.length
          · rw [List.take_append_of_le_length (Nat.le_of_lt hi), List.getElem_append_left hi]
            exact (hadm ⟨_, hi⟩).imp old id
          · have he : i.val = S.length := by
              have := i.isLt
              simp only [List.length_append, List.length_singleton] at this
              omega
            simp [he, List.getElem_append_right]
            cases hn : neg q with
            | true => exact Or.inl (List.mem_append.mp (new hn))
            | false => exact Or.inr (hlegal S q (hgs q (by simp)) hn)
        · intro x
          rw [← List.append_assoc, List.map_append, hmap, List.foldl_append]
          change _ ++ [gate S q x] = _ ++ [q.op.eval (q.inputs.map _)]
          congr 2
          change q.op.eval (q.inputs.map _) = _
          congr 1
          apply List.map_congr_left
          intro j _
          rw [← hmap x]
          exact (List.getD_map (inp ++ S) z (fun f => f x)).symm
    obtain ⟨S, R, hlen, hsub, hmark, hadm, hmap⟩ := build C.gates (fun g hg => hfan g hg)
    have eqmap (x : Fin n → Bool) : S.map (fun f => f x) = T.map (fun f => f x) := by
      apply List.append_cancel_left (as := List.ofFn x)
      rw [hcanon x]
      change _ = C.gates.foldl step (List.ofFn x)
      simpa only [List.map_append, inp, List.map_ofFn, Function.comp_def] using hmap x
    have eqST : S = T := by
      apply List.ext_getElem
      · simpa using congrArg List.length (eqmap (fun _ => false))
      · intro i hi hj
        funext x
        have hh := congrArg (fun s : List Bool => s.getD i false) (eqmap x)
        simpa [List.getD_eq_getElem, hi, hj] using hh
    subst S
    refine ⟨R, hlen, hsub, hmark, hadm, (List.toFinset_card_le R).trans_eq hlen, ?_⟩
    intro htop U hU hRU
    let P (j : ℕ) := ∃ hj : j < T.length, T[j] ∉ U
    have hex : ∃ j, P j := by
      obtain ⟨f, hf, hu⟩ := Finset.exists_mem_notMem_of_card_lt_card (Finset.card_lt_card hU)
      obtain ⟨j, hj, heq⟩ := List.getElem_of_mem (List.mem_toFinset.mp hf)
      exact ⟨j, hj, heq ▸ hu⟩
    let k := Nat.find hex
    obtain ⟨hk, hout⟩ := Nat.find_spec hex
    have inc : (T.take k).toFinset ⊆ U := by
      intro a ha
      obtain ⟨j, hj, heq⟩ := List.mem_take_iff_getElem.mp (List.mem_toFinset.mp ha)
      change j < min k T.length at hj
      subst a
      by_contra hn
      exact Nat.find_min hex (show j < k by omega) ⟨by omega, hn⟩
    have lift (a : H) : av (T.take k).toFinset a → av U a :=
      fun h => h.imp_right (Or.imp_right (fun ha => inc ha))
    refine ⟨T[k], List.mem_toFinset.mpr (List.getElem_mem _), hout, ?_⟩
    rcases hadm ⟨k, hk⟩ with h | h | ⟨a, b, ha, hb, hh⟩
    · exact False.elim (hout (hRU (List.mem_toFinset.mpr h)))
    · exact False.elim (htop (h ▸ List.get_mem T ⟨k, hk⟩))
    · exact ⟨a, b, lift _ ha, lift _ hb, hh⟩
  intro n G inst A C F readers hdeg hgirth hoff hedge hfan hfun hmin hdegR hneg hbudget
  classical
  obtain ⟨v, hv, htwo, g, hg, hop⟩ := hneg
  change g ∈ C.gates.filter _ at hg
  obtain ⟨hgates, hread⟩ := List.mem_filter.mp hg
  have hd : g.inputs.head? = some v.val := by
    rw [hop] at hread
    change (g.inputs.take 1).contains v.val = true at hread
    cases e : g.inputs with
    | nil => simp [e] at hread
    | cons a t => simpa [e, eq_comm] using hread
  obtain ⟨T, ht, htneg, htstep, htout, hprofile, hcanon⟩ := extractChart n C v hfan ⟨g, hgates, hop, hd⟩
  rw [hfun] at htout
  let H := (Fin n → Bool) → Bool
  let free := fun (f : H) => f = (fun _ => false) ∨ ∃ v : Fin n, f = (fun x => x v)
  let av := fun (U : Finset H) (f : H) => free f ∨ f ∈ U
  let rule := fun (U : Finset H) (h : H) =>
    (∃ b, av U b ∧ h = fun x => !(b x)) ∨
      (∃ b c, av U b ∧ av U c ∧ ((h = fun x => b x && c x) ∨ (h = fun x => b x || c x)))
  let reach := fun (B : Finset H) (f : H) =>
    av B f ∧ ∀ U ⊂ B, ∃ h ∈ B, h ∉ U ∧ rule U h
  let available := fun (S : List H) (f : H) =>
    f = (fun _ => false) ∨ (∃ u : Fin n, f = (fun x => x u)) ∨ f ∈ S
  let leg := fun (S : List H) (h : H) =>
    (∃ b, available S b ∧ h = fun x => !(b x)) ∨
      (∃ b c, available S b ∧ available S c ∧
        ((h = fun x => b x && c x) ∨ (h = fun x => b x || c x)))
  have avEq (S : List H) (b : H) : av S.toFinset b ↔ available S b := by
    simp only [av, free, available, List.mem_toFinset, or_assoc]
  have legEq (S : List H) (b : H) : rule S.toFinset b ↔ leg S b := by
    simp only [rule, leg, avEq]
  have mono {U V : Finset H} {f : H} (hu : U ⊆ V) : rule U f → rule V f := by
    have inc (b : H) : av U b → av V b := fun h => Or.imp_right (fun hb => hu hb) h
    rintro (⟨b, hb, e⟩ | ⟨b, c, hb, hc, e⟩)
    · exact Or.inl ⟨b, inc _ hb, e⟩
    · exact Or.inr ⟨b, c, inc _ hb, inc _ hc, e⟩
  have compileSet (B : Finset H) (f : H) (h : reach B f) : HasCircuitSize n f B.card := by
    obtain ⟨L, hnod, rfl, hL⟩ := (frontier rule mono).2 B h.2
    rw [List.toFinset_card_of_nodup hnod]
    exact compileChart n L (fun i => (legEq _ _).mp (hL i)) f ((avEq L f).mp h.1)
  have reachT : reach T.toFinset F :=
    ⟨(avEq _ _).mpr htout, (frontier rule mono).1 T (fun i => (legEq _ _).mpr (htstep i))⟩
  have minT := hmin _ (compileSet _ _ reachT)
  have hcard : T.toFinset.card = C.size := by
    have := List.toFinset_card_le T
    omega
  obtain ⟨U, hU, hoU, hnU, hnfU, hsubU⟩ := (pruneChart n).1 T F htstep htout
  have hlenU := hmin _ (compileChart n U hU F hoU)
  have heU := hsubU.eq_of_length_le (show T.length ≤ U.length by omega)
  subst U
  have nofree (b : H) (hb : b ∈ T.toFinset) : ¬ free b := by
    intro h
    apply hnfU b (List.mem_toFinset.mp hb)
    exact h.elim Or.inl (fun hv => Or.inr (Or.inl hv))
  let live := fun (b : H) => b ≠ (fun _ => true) ∧ ¬ free b
  have hzero : F (fun _ => false) = false := by
    change (decide (∃ a ∈ A, false = true) ||
            decide (∃ a b, G.Adj a b ∧ false = true ∧ false = true)) = false
    simp
  have notop : F ≠ (fun _ => true) := by
    intro he
    have hh := congrFun he (fun _ => false)
    simp only [hzero] at hh
    contradiction
  obtain ⟨Q, hQ, hoQ, hsQ, hntQ⟩ := pruneTrue n T F htstep htout notop
  have hlenQ := hmin _ (compileChart n Q hQ F hoQ)
  have heQ := hsQ.eq_of_length_le (show T.length ≤ Q.length by omega)
  subst Q
  let cut := fun (v : Fin n) (f : H) (x : Fin n → Bool) => f (Function.update x v false)
  let K := fun w => ((T.toFinset.image (cut w)).filter live).card
  have debt (w : Fin n) : K w + (readers w).length ≤ T.toFinset.card := by
    obtain ⟨R, hcardR, hR⟩ := hprofile w
    have cert (i : Fin T.length) (hi : i ∈ R) :
        ¬ live (cut w (T.get i)) ∨ ∃ j < i, cut w (T.get j) = cut w (T.get i) := by
      rcases hR i hi with a | a | a | ⟨j, hj, he⟩
      · exact Or.inl (fun h => h.1 a)
      · exact Or.inl (fun h => h.2 (Or.inl a))
      · exact Or.inl (fun h => h.2 (Or.inr a))
      · exact Or.inr ⟨j, hj, he.symm⟩
    have bnd := leastRows T (cut w) live R cert
    rw [hcard, ← ht, ← hcardR]
    exact bnd
  by_contra no
  have sliceLower (w : Fin n) (hw : w ∉ A) : T.toFinset.card ≤ K w + 3 := by
    obtain ⟨L, hlegal, hout, hnod, hfree, hsub⟩ :=
      (pruneChart n).2 T F htstep htout w
    have cut0 : cut w F (fun _ => false) = false := by
      change F (Function.update (fun _ => false) w false) = false
      simpa only [Function.update_eq_self] using hzero
    have nt : cut w F ≠ (fun _ => true) := by
      intro he
      have hh := congrFun he (fun _ => false)
      simp only [cut0] at hh
      contradiction
    obtain ⟨V, hV, hVo, hVL, hVt⟩ := pruneTrue n L (cut w F) hlegal hout nt
    have sub : V.toFinset ⊆ (T.toFinset.image (cut w)).filter live := by
      intro b hb
      have hvb := List.mem_toFinset.mp hb
      have hmem := hVL.subset hvb
      obtain ⟨a, ha, he⟩ := List.mem_map.mp (hsub.subset hmem)
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, he⟩,
        hVt b hvb, ?_⟩
      intro h
      exact hfree b hmem (h.elim Or.inl (fun e => Or.inr (Or.inl e)))
    have bound := Finset.card_le_card sub
    rw [List.toFinset_card_of_nodup (hnod.sublist hVL)] at bound
    change V.length ≤ K w at bound
    by_contra hh
    have lt := lt_of_le_of_lt (Nat.add_le_add_right bound 3) (Nat.lt_of_not_ge hh)
    exact no ⟨w, hw, V.length, by omega, compileChart n V hV _ hVo⟩
  have girth : 7 ≤ G.egirth := SimpleGraph.le_egirth.mpr (fun a p hp => by
    exact_mod_cast hgirth a p hp)
  let N := (C.gates.filter (fun q => q.op.eval [false])).length
  have gap (I : Finset (Fin n)) (hI : I ⊆ Aᶜ) (hi : ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) :=
    counting G A (fun w => (readers w).length) N
      (fun w hw => ⟨(hdegR w hw).1, (hdegR w hw).2.1⟩) hdeg hoff hbudget I hI hi
  obtain ⟨R, _, hRT, hmark, _, hcardR, hbinary⟩ := seedRows n C T hfan hcanon
  have notopT : (fun _ => true) ∉ T := fun hm => hntQ _ hm rfl
  have binary (U : Finset H) (hU : U ⊂ T.toFinset) (hRU : R.toFinset ⊆ U) :
      ∃ h ∈ T.toFinset, h ∉ U ∧
        ∃ b c : H, av U b ∧ av U c ∧ (h = b ⊓ c ∨ h = b ⊔ c) := by
    obtain ⟨h, ht, hnot, b, c, hb, hc, he⟩ := hbinary notopT U hU hRU
    have coeAv (b : H) :
        (b = (fun _ => false) ∨ (∃ u : Fin n, b = (fun x => x u)) ∨ b ∈ U) → av U b := by
      simp only [av, free, or_assoc, imp_self]
    exact ⟨h, ht, hnot, b, c, coeAv b hb, coeAv c hc, he⟩
  have hbnd : R.toFinset.card ≤ N := hcardR
  have degree (u : Fin n) : G.degree u = if u ∈ A then 0 else 3 := by
    split
    · rename_i h
      exact (G.degree_eq_zero u).mpr (fun w e => hoff u w e h)
    · rename_i h
      exact (G.ncard_neighborSet u).symm.trans (hdeg u h)
  have ind (I : Finset (Fin n)) (hi : G.IsIndepSet (I : Set (Fin n))) :
      ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b := by
    intro a ha b hb e
    exact hi ha hb e.ne e
  obtain ⟨w, hw, D, hD, hc⟩ := obstruction n G A degree girth T.toFinset R.toFinset
    (fun w => (readers w).length) reachT
    (fun b hb => ⟨hntQ b (List.mem_toFinset.mp hb), nofree b hb⟩)
    (fun D h => hcard ▸ hmin _ (compileSet D F h))
    (fun _ h => List.mem_toFinset.mpr (hRT (List.mem_toFinset.mp h))) binary
    ⟨v, hv, htwo, List.mem_toFinset.mpr (hmark v ⟨g, hgates, hop, hd⟩)⟩
    (fun I hi hi' => (Nat.mul_le_mul_left 2 (Nat.succ_le_succ
      (Nat.add_le_add_right (Nat.add_le_add_left hbnd _) _))).trans (gap I hi (ind I hi')))
    (fun w hw => ⟨(hdegR w hw).1, debt w, sliceLower w hw⟩)
  exact no ⟨w, hw, D.card, by omega, compileSet D _ hD⟩
