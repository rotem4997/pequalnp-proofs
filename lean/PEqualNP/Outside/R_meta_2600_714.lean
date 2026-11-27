import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_2600_714
    (symmetry : let F := fun (x : Fin 26 → Bool) => ∃ p l : Fin 13, (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
                ∀ i j : Fin 26, i ≠ j → ∃ σ : Equiv.Perm (Fin 26),
                  σ i = 0 ∧ (σ j = 1 ∨ σ j = 13 ∨ σ j = 14) ∧ ∀ x, F x ↔ F (fun v => x (σ v)))
    (lower : let F := fun (x : Fin 26 → Bool) => ∃ p l : Fin 13, (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
             let G := fun (C : Circuit) => ∀ (n : ℕ) (g : Gate), C.gates[n]? = some g → (g.op = .and ∨ g.op = .or) ∧ ∃ i j : ℕ, g.inputs = [i,j] ∧ i ≠ j ∧ i < 26+n ∧ j < 26+n
             let E := fun (C : Circuit) => ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ F x
             let H := fun (g : Gate) => g = ⟨.and,[0,13]⟩ ∨ ∃ d ∈ ([1,13,14] : List ℕ), g = ⟨.or,[0,d]⟩
             ∀ C : Circuit, G C → E C → (∀ g, C.gates.head? = some g → H g) →
               (∀ w v : Fin 26, w ≠ v → ∃ q ∈ C.gates, w.val ∈ q.inputs ∧ v.val ∉ q.inputs) → 63 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (63 : ℕ) ≤ x1.size := by
  let F := fun (x : Fin 26 → Bool) => ∃ p l : Fin 13, (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
  let G := fun (C : Circuit) => ∀ (n : ℕ) (g : Gate), C.gates[n]? = some g → (g.op = .and ∨ g.op = .or) ∧ ∃ i j : ℕ, g.inputs = [i,j] ∧ i ≠ j ∧ i < 26+n ∧ j < 26+n
  let E := fun (C : Circuit) => ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ F x
  let H := fun (g : Gate) => g = ⟨.and,[0,13]⟩ ∨ ∃ d ∈ ([1,13,14] : List ℕ), g = ⟨.or,[0,d]⟩
  change ∀ C : Circuit, G C → E C → 63 ≤ C.size
  -- An AND on a nonincident pair is false on every minimal positive input.
  let R (x y : Bool) := x = true → y = true
  let appendGate (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have readMono {x y : List Bool} (rel : List.Forall₂ R x y) (i : ℕ) :
        R (x.getD i false) (y.getD i false) := by
      induction rel generalizing i with
      | nil => simp [List.getD, R]
      | cons h _ ih => cases i with
        | zero => exact h
        | succ j => exact ih j

  have foldMono (gs : List Gate) (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
        {x y : List Bool} (rel : List.Forall₂ R x y) :
        List.Forall₂ R (gs.foldl appendGate x) (gs.foldl appendGate y) := by
      induction gs generalizing x y with
      | nil => exact rel
      | cons g gs ih =>
        apply ih (fun k hk => ops k (List.mem_cons_of_mem _ hk))
        apply List.rel_append rel
        apply List.Forall₂.cons _ List.Forall₂.nil
        rcases ops g (by simp) with hand | hor
        · rw [hand]
          change (g.inputs.map (fun i => x.getD i false)).all id = true →
            (g.inputs.map (fun i => y.getD i false)).all id = true
          simp only [List.all_map, Function.comp_def, List.all_eq_true, id_eq]
          intro hx i hi
          exact readMono rel i (hx i hi)
        · rw [hor]
          change (g.inputs.map (fun i => x.getD i false)).any id = true →
            (g.inputs.map (fun i => y.getD i false)).any id = true
          simp only [List.any_map, Function.comp_def, List.any_eq_true, id_eq]
          rintro ⟨i, hi, hx⟩
          exact ⟨i, hi, readMono rel i hx⟩

  have block (x y : Fin 26 → Bool) (h : ∀ i, R (x i) (y i)) :
      List.Forall₂ R (List.ofFn x) (List.ofFn y) := by
    apply List.forall₂_of_length_eq_of_get (by simp)
    intro i hi hj
    have bound : i < 26 := by simpa using hi
    simpa only [List.get_eq_getElem,List.getElem_ofFn] using h ⟨i,bound⟩

  let raw (d : Fin 26) : Gate := ⟨.and,[0,d.val]⟩

  have first_step (d : Fin 26) (x : Fin 26 → Bool) :
      appendGate (List.ofFn x) (raw d) = List.ofFn x ++ [x 0 && x d] := by
    have rd (i : Fin 26) : (List.ofFn x).getD i.val false = x i := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    change _ ++ [GateOp.and.eval ([0,d.val].map fun i => (List.ofFn x).getD i false)] = _
    simp only [List.map_cons,List.map_nil]
    change _ ++ [((List.ofFn x).getD 0 false && ((List.ofFn x).getD d.val false && true))] = _
    have r0 : (List.ofFn x).getD 0 false = x 0 := rd (0 : Fin 26)
    rw [r0,rd d,Bool.and_true]

  have compare_tail (a b : Fin 26) (gs : List Gate) (o : ℕ)
      (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (x y : Fin 26 → Bool) (bits : ∀ i, R (x i) (y i)) (seed : R (x 0 && x a) (y 0 && y b)) :
      R ((Circuit.mk (raw a :: gs) o).eval (List.ofFn x))
        ((Circuit.mk (raw b :: gs) o).eval (List.ofFn y)) := by
    change R ((gs.foldl appendGate (appendGate (List.ofFn x) (raw a))).getD o false)
      ((gs.foldl appendGate (appendGate (List.ofFn y) (raw b))).getD o false)
    rw [first_step,first_step]
    exact readMono (foldMono gs ops (List.rel_append (block x y bits) (.cons seed .nil))) o

  let flag (p l : Fin 13) (i : Fin 26) := decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)

  have dead : ∀ p l : Fin 13, (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) →
      (flag p l 0 && flag p l 1) = false ∧ (flag p l 0 && flag p l 14) = false := by
    dsimp only [flag]
    decide

  have fixed (d : Fin 26) (hd : d = 1 ∨ d = 14) (gs : List Gate) (o : ℕ)
      (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (old : ∀ x, (Circuit.mk (raw d :: gs) o).eval (List.ofFn x) = true ↔ F x) :
      ∀ x, (Circuit.mk (raw 13 :: gs) o).eval (List.ofFn x) = true ↔ F x := by
    intro x
    constructor
    · intro hout
      by_contra hn
      have seed : R (x 0 && x 13) (x 0 && x d) := by
        intro h
        obtain ⟨hp,hl⟩ := Bool.and_eq_true_iff.mp h
        exact (hn ⟨0,0,Or.inl rfl,hp,hl⟩).elim
      exact hn ((old x).mp (compare_tail 13 d gs o ops x x (fun _ h => h) seed hout))
    · rintro ⟨p,l,pl,hp,hl⟩
      have hf : F (flag p l) := ⟨p,l,pl,by simp [flag],by simp [flag]⟩
      have less (i : Fin 26) : R (flag p l i) (x i) := by
        intro h
        rcases of_decide_eq_true h with h|h
        · exact h ▸ hp
        · exact h ▸ hl
      have hz : (flag p l 0 && flag p l d) = false := by
        rcases hd with rfl|rfl
        · exact (dead p l pl).1
        · exact (dead p l pl).2
      apply compare_tail d 13 gs o ops (flag p l) x less _ ((old _).mpr hf)
      simp [R,hz]

  have repair (C : Circuit) (good : G C) (correct : E C)
      (hh : ∃ d ∈ ([1,14] : List ℕ), C.gates.head? = some ⟨.and,[0,d]⟩) :
      ∃ D : Circuit, D.size = C.size ∧ G D ∧ E D ∧ D.gates.head? = some ⟨.and,[0,13]⟩ := by
    obtain ⟨d,hd,hhead⟩ := hh
    cases C with
    | mk gs o =>
      cases gs with
      | nil => simp at hhead
      | cons g gs =>
        simp only [List.head?_cons,Option.some.injEq] at hhead
        subst g
        have hd' : d = 1 ∨ d = 14 := by simpa using hd
        let u : Fin 26 := ⟨d,by omega⟩
        have hu : u = 1 ∨ u = 14 := by
          rcases hd' with h|h
          · exact Or.inl (Fin.ext h)
          · exact Or.inr (Fin.ext h)
        have ops (q : Gate) (hq : q ∈ gs) : q.op = .and ∨ q.op = .or := by
          obtain ⟨n,hn,eq⟩ := List.mem_iff_getElem.mp hq
          exact (good (n+1) q (by simpa only [List.getElem?_cons_succ, List.getElem?_eq_getElem hn] using congrArg some eq)).1
        refine ⟨⟨raw 13 :: gs,o⟩,rfl,?_,fixed u hu gs o ops correct,rfl⟩
        intro n q h
        cases n with
        | zero =>
          change some (raw 13) = some q at h
          have eq := Option.some.inj h
          subst q
          exact ⟨Or.inl rfl,0,13,rfl,by decide,by decide,by decide⟩
        | succ n => exact good (n+1) q h

  -- Each input has a private neighbor relative to every other input.
  -- If every reader of w also read v, swapping the two on that neighbor would
  -- preserve the order of all outputs except the raw input w itself.
  let inc (p l : Fin 13) : Prop := p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
  letI (p l : Fin 13) : Decidable (inc p l) := by dsimp only [inc]; infer_instance
  let edge (i j : Fin 26) : Bool := Fin.addCases (m := 13) (n := 13)
    (fun p : Fin 13 => Fin.addCases (m := 13) (n := 13) (fun _ : Fin 13 => false) (fun l : Fin 13 => decide (inc p l)) j)
    (fun l : Fin 13 => Fin.addCases (m := 13) (n := 13) (fun p : Fin 13 => decide (inc p l)) (fun _ : Fin 13 => false) j) i

  have goal_pairs (x : Fin 26 → Bool) :
      F x ↔ ∃ i j : Fin 26, edge i j = true ∧ x i = true ∧ x j = true := by
    constructor
    · rintro ⟨p,l,h,hp,hl⟩
      exact ⟨Fin.castAdd 13 p, Fin.natAdd 13 l, by simp only [edge,Fin.addCases_left,Fin.addCases_right,decide_eq_true_eq]; exact h,hp,hl⟩
    · rintro ⟨i,j,h,hi,hj⟩
      cases i using Fin.addCases (m := 13) (n := 13) <;> cases j using Fin.addCases (m := 13) (n := 13) <;> simp only [edge,Fin.addCases_left,Fin.addCases_right,decide_eq_true_eq,Bool.false_eq_true] at h
      · exact ⟨_,_,h,hi,hj⟩
      · exact ⟨_,_,h,hj,hi⟩

  have raw_read (gs : List Gate) (xs : List Bool) (w : ℕ) (bound : w < xs.length) :
      (gs.foldl appendGate xs).getD w false = xs.getD w false := by
    induction gs generalizing xs with
    | nil => rfl
    | cons q gs ih =>
      rw [List.foldl_cons,ih _ (by simp [appendGate]; omega)]
      exact List.getD_append _ _ _ _ bound

  have singleton_negative : ∀ w : Fin 26, ¬ F (fun i => decide (i=w)) := by
    intro w h
    obtain ⟨p,l,_,hp,hl⟩ := h
    have eq := congrArg Fin.val ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
    change p.val = 13 + l.val at eq
    have lim := p.isLt
    omega

  have separates : ∀ w v : Fin 26, w ≠ v → ∃ t : Fin 26, t ≠ v ∧ t ≠ w ∧ edge w t = true ∧ edge v t = false := by
    dsimp only [edge,inc]
    decide +kernel
  have loopfree : ∀ v : Fin 26, edge v v = false := by
    dsimp only [edge,inc]
    decide +kernel
  have symmetric : ∀ v t : Fin 26, edge v t = edge t v := by
    dsimp only [edge,inc]
    decide +kernel

  let two (u t : Fin 26) (i : Fin 26) := decide (i = u ∨ i = t)

  have two_exact (u t : Fin 26) : F (two u t) ↔ edge u t = true := by
    rw [goal_pairs]
    constructor
    · rintro ⟨i,j,he,hi,hj⟩
      rcases of_decide_eq_true hi with rfl|rfl <;> rcases of_decide_eq_true hj with rfl|rfl
      · simp [loopfree] at he
      · exact he
      · rwa [symmetric] at he
      · simp [loopfree] at he
    · exact fun h => ⟨u,t,h,by simp [two],by simp [two]⟩

  let inv (w v : ℕ) (x y : List Bool) := x.length = y.length ∧ v < x.length ∧
    x.getD v false = false ∧ y.getD v false = true ∧ ∀ i, i ≠ w → R (x.getD i false) (y.getD i false)

  have extend (w v : ℕ) (x y : List Bool) (h : inv w v x y) (a b : Bool) (hab : R a b) :
      inv w v (x ++ [a]) (y ++ [b]) := by
    obtain ⟨len,hv,hx,hy,ord⟩ := h
    have hvy : v < y.length := by omega
    refine ⟨by simp [len],by simp; omega,?_,?_,?_⟩
    · rwa [List.getD_append _ _ _ _ hv]
    · rwa [List.getD_append _ _ _ _ hvy]
    · intro i ne
      by_cases small : i < x.length
      · rw [List.getD_append _ _ _ _ small,List.getD_append _ _ _ _ (by omega)]
        exact ord i ne
      · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),← len]
        cases i-x.length with
        | zero => exact hab
        | succ n => simp [R,List.getD]

  have propagate (w v : ℕ) (gs : List Gate)
      (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (paired : ∀ g ∈ gs, w ∈ g.inputs → v ∈ g.inputs)
      (x y : List Bool) (h : inv w v x y) :
      inv w v (gs.foldl appendGate x) (gs.foldl appendGate y) := by
    induction gs generalizing x y with
    | nil => exact h
    | cons g gs ih =>
      apply ih (fun q hq => ops q (List.mem_cons_of_mem _ hq)) (fun q hq => paired q (List.mem_cons_of_mem _ hq))
      apply extend w v x y h
      rcases ops g (by simp) with hand|hor
      · rw [hand]
        change (g.inputs.map fun i => x.getD i false).all id = true → (g.inputs.map fun i => y.getD i false).all id = true
        simp only [List.all_map,Function.comp_def,List.all_eq_true,id_eq]
        intro hx i hi
        by_cases eq : i=w
        · have hv := hx v (paired g (by simp) (eq ▸ hi))
          rw [h.2.2.1] at hv
          contradiction
        · exact h.2.2.2.2 i eq (hx i hi)
      · rw [hor]
        change (g.inputs.map fun i => x.getD i false).any id = true → (g.inputs.map fun i => y.getD i false).any id = true
        simp only [List.any_map,Function.comp_def,List.any_eq_true,id_eq]
        rintro ⟨i,hi,hx⟩
        by_cases eq : i=w
        · exact ⟨v,paired g (by simp) (eq ▸ hi),h.2.2.2.1⟩
        · exact ⟨i,hi,h.2.2.2.2 i eq hx⟩

  have exclusive (C : Circuit) (good : G C) (exactC : E C) (w v : Fin 26) (ne : w ≠ v) :
      ∃ q ∈ C.gates, w.val ∈ q.inputs ∧ v.val ∉ q.inputs := by
    obtain ⟨t,tv,tw,hit,miss⟩ := separates w v ne
    let x := two w t
    let y := two v t
    have pick (f : Fin 26 → Bool) (i : Fin 26) : (List.ofFn f).getD i.val false = f i := by
      rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
    have pair0 : inv w.val v.val (List.ofFn x) (List.ofFn y) := by
      refine ⟨by simp,by simp,?_,?_,?_⟩
      · rw [pick]; simp [x,two,ne.symm,tv.symm]
      · rw [pick]; simp [y,two]
      · intro i n
        by_cases small : i < 26
        · let k : Fin 26 := ⟨i,small⟩
          change R ((List.ofFn x).getD k.val false) ((List.ofFn y).getD k.val false)
          rw [pick,pick]
          have nk : k ≠ w := fun h => n (congrArg Fin.val h)
          simpa only [R,x,y,two,decide_eq_true_eq,nk,false_or] using (Or.inr : k=t → k=v ∨ k=t)
        · simp only [R,List.getD_eq_getElem?_getD,List.getElem?_eq_none (show (List.ofFn x).length ≤ i by simp; omega),
              List.getElem?_eq_none (show (List.ofFn y).length ≤ i by simp; omega),Option.getD_none]
          exact id
    have out : C.output ≠ w.val := by
      intro ho
      apply singleton_negative w
      apply (exactC (fun i => decide (i=w))).mp
      change (C.gates.foldl appendGate _).getD C.output false = true
      rw [ho,raw_read _ _ _ (by simp),pick]; simp
    by_contra no
    have ops (g : Gate) (hg : g ∈ C.gates) : g.op = .and ∨ g.op = .or := by
      obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hg
      exact (good i g (by rw [List.getElem?_eq_getElem hi,eq])).1
    have allp (q : Gate) (hq : q ∈ C.gates) (qw : w.val ∈ q.inputs) : v.val ∈ q.inputs := by
      by_contra nv
      exact no ⟨q,hq,qw,nv⟩
    have h := propagate w.val v.val C.gates ops allp _ _ pair0
    have pos := (exactC x).mpr ((two_exact w t).mpr hit)
    have wrong : F y := (exactC y).mp (h.2.2.2.2 C.output out pos)
    have contra := (two_exact v t).mp wrong
    exact Bool.noConfusion (miss.symm.trans contra)

  have lowerFour (C : Circuit) (hg : G C) (he : E C)
      (heads : ∀ g, C.gates.head? = some g → H g) : 63 ≤ C.size :=
    lower C hg he heads (exclusive C hg he)
  -- Wire relabeling follows the argument in R_meta_1482_2.
  have getD_rel : ∀ (ρ : ℕ → ℕ) (hl : ∀ a, a < 26 → ρ a < 26) (hb : ∀ a, 26 ≤ a → ρ a = a)
      (e : Fin 26 → Bool) (T : List Bool) (a : ℕ),
      (List.ofFn e ++ T).getD (ρ a) false =
        (List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩) ++ T).getD a false := by
    intro ρ hl hb e T a
    by_cases ha : a < 26
    · have h1 := hl a ha
      rw [List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact h1),
        List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact ha)]
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact h1),
        List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact ha), List.getElem_ofFn,
        List.getElem_ofFn]
    · rw [hb a (by omega)]
      rw [List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]; omega),
        List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]; omega)]
      rw [List.length_ofFn, List.length_ofFn]
  have fold_rel : ∀ (ρ : ℕ → ℕ) (hl : ∀ a, a < 26 → ρ a < 26) (hb : ∀ a, 26 ≤ a → ρ a = a)
      (stp : List Bool → Gate → List Bool)
      (hstp : ∀ w g, stp w g = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (e : Fin 26 → Bool) (gs : List Gate) (T : List Bool), ∃ T' : List Bool,
      (gs.map (fun g => Gate.mk g.op (g.inputs.map ρ))).foldl stp (List.ofFn e ++ T) =
        List.ofFn e ++ T' ∧
      gs.foldl stp (List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩) ++ T) =
        List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩) ++ T' := by
    intro ρ hl hb stp hstp e gs
    induction gs with
    | nil => intro T; exact ⟨T, by simp, by simp⟩
    | cons g gs ih =>
      intro T
      have hval : (Gate.mk g.op (g.inputs.map ρ)).op.eval ((Gate.mk g.op (g.inputs.map ρ)).inputs.map
          fun i => (List.ofFn e ++ T).getD i false) =
          g.op.eval (g.inputs.map fun i =>
            (List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩) ++ T).getD i false) := by
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        exact getD_rel ρ hl hb e T a
      obtain ⟨T', h1, h2⟩ := ih (T ++ [g.op.eval (g.inputs.map fun i =>
        (List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩) ++ T).getD i false)])
      refine ⟨T', ?_, ?_⟩
      · rw [List.map_cons, List.foldl_cons, hstp, hval, List.append_assoc]
        exact h1
      · rw [List.foldl_cons, hstp, List.append_assoc]
        exact h2
  have wires_rel : ∀ (ρ : ℕ → ℕ) (hl : ∀ a, a < 26 → ρ a < 26) (hb : ∀ a, 26 ≤ a → ρ a = a)
      (C : Circuit) (e : Fin 26 → Bool) (a : ℕ),
      ((Circuit.mk (C.gates.map (fun g => Gate.mk g.op (g.inputs.map ρ))) (ρ C.output)).wires
        (List.ofFn e)).getD (ρ a) false =
        (C.wires (List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩))).getD a false := by
    intro ρ hl hb C e a
    obtain ⟨T', h1, h2⟩ := fold_rel ρ hl hb _ (fun _ _ => rfl) e C.gates []
    simp only [List.append_nil] at h1 h2
    have hw : ∀ (D : Circuit) (x : List Bool), D.wires x = D.gates.foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x := fun _ _ => rfl
    rw [hw, hw]
    rw [h1, h2]
    exact getD_rel ρ hl hb e T' a
  intro C good correct
  cases hgates : C.gates with
  | nil =>
    apply lowerFour C good correct
    simp [hgates]
  | cons g tail =>
    obtain ⟨hop,i,j,inputs,hne,hi,hj⟩ := good 0 g (by simp [hgates])
    simp only [Nat.add_zero] at hi hj
    let u : Fin 26 := ⟨i,hi⟩
    let v : Fin 26 := ⟨j,hj⟩
    obtain ⟨σ,hu,hv,hsym⟩ := symmetry u v (fun h => hne (congrArg Fin.val h))
    let ρ (w : ℕ) := if hw : w < 26 then (σ ⟨w,hw⟩).val else w
    have hl (w : ℕ) (hw : w < 26) : ρ w < 26 := by
      simpa only [ρ,dite_eq_left hw] using (σ ⟨w,hw⟩).isLt
    have hb (w : ℕ) (hw : 26 ≤ w) : ρ w = w := by
      simp [ρ, Nat.not_lt.mpr hw]
    have inj : Function.Injective ρ := by
      intro a b hab
      by_cases ha : a < 26 <;> by_cases hb' : b < 26
      · simp only [ρ,dite_eq_left ha,dite_eq_left hb'] at hab
        exact congrArg Fin.val (σ.injective (Fin.ext hab))
      · have := hl a ha
        rw [hb b (by omega)] at hab
        omega
      · have := hl b hb'
        rw [hb a (by omega)] at hab
        omega
      · simpa only [hb a (by omega),hb b (by omega)] using hab
    let D := Circuit.mk (C.gates.map (fun g => Gate.mk g.op (g.inputs.map ρ))) (ρ C.output)
    have sizeD : D.size = C.size := List.length_map _
    have goodD : G D := by
      intro n g' h
      change (C.gates.map (fun q => Gate.mk q.op (q.inputs.map ρ)))[n]? = some g' at h
      rw [List.getElem?_map] at h
      cases hq : C.gates[n]? with
      | none => simp [hq] at h
      | some q =>
        simp only [hq,Option.map_some,Option.some.injEq] at h
        subst g'
        obtain ⟨ops,a,b,ab,ne,ha,hb'⟩ := good n q hq
        have bound (w : ℕ) (hw : w < 26 + n) : ρ w < 26 + n := by
          by_cases hlt : w < 26
          · have := hl w hlt; omega
          · rw [hb w (by omega)]; exact hw
        exact ⟨ops,ρ a,ρ b,by simp [ab],fun h => ne (inj h),bound a ha,bound b hb'⟩
    have exactD : E D := by
      intro x
      change (D.wires (List.ofFn x)).getD (ρ C.output) false = true ↔ F x
      rw [wires_rel ρ hl hb C x C.output]
      have harg : (fun k : Fin 26 => x ⟨ρ k.val,hl k.val k.isLt⟩) = (fun k => x (σ k)) := by
        funext k
        congr 1
        apply Fin.ext
        simp [ρ,k.isLt]
      rw [harg]
      exact (correct (fun k => x (σ k))).trans (hsym x).symm
    let d := (σ v).val
    have hi0 : ρ i = 0 := by simpa [ρ,hi,u] using congrArg Fin.val hu
    have hjd : ρ j = d := by simp [ρ,hj,d,v]
    have headD : D.gates.head? = some ⟨g.op,[0,d]⟩ := by simp [D,hgates,inputs,hi0,hjd]
    have hd : d = 1 ∨ d = 13 ∨ d = 14 := by

      rcases hv with h|h|h
      · exact Or.inl (congrArg Fin.val h)
      · exact Or.inr (Or.inl (congrArg Fin.val h))
      · exact Or.inr (Or.inr (congrArg Fin.val h))
    rw [← sizeD]
    rcases hop with hand|hor
    · rw [hand] at headD
      by_cases he : d = 13
      · rw [he] at headD
        apply lowerFour D goodD exactD
        intro q hq
        exact Or.inl (Option.some.inj (hq.symm.trans headD))
      · have bad : d ∈ ([1,14] : List ℕ) := by simp; omega
        obtain ⟨N,hs,hn,hen,hh⟩ := repair D goodD exactD ⟨d,bad,headD⟩
        rw [← hs]
        apply lowerFour N hn hen
        intro q hq
        exact Or.inl (Option.some.inj (hq.symm.trans hh))
    · rw [hor] at headD
      apply lowerFour D goodD exactD
      intro q hq
      exact Or.inr ⟨d,by simpa using hd,Option.some.inj (hq.symm.trans headD)⟩
