import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8784
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

private def legal (m : ℕ) (g : Gate) :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < m
private def good (n : ℕ) (gs : List Gate) :=
  ∀ j (hj : j < gs.length), legal (n+j) gs[j]
private theorem good_iff (n : ℕ) (C : Circuit) : good n C.gates ↔ IsAO2 n C := by
  have atGate (j) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    simp [gateAt,List.getD_eq_getElem?_getD,hj]
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro g hg; obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg; exact (h j hj).1
    · intro j hj i hi; rw [atGate j hj] at hi; exact (h j hj).2.2 i hi
    · intro g hg; obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg; exact (h j hj).2.1
  · rintro ⟨op,back,arity⟩ j hj
    refine ⟨op _ (List.getElem_mem _),arity _ (List.getElem_mem _),?_⟩
    rw [← atGate j hj]; exact back j hj
private theorem good_cons {n : ℕ} {g : Gate} {gs : List Gate} :
    good n (g::gs) ↔ legal n g ∧ good (n+1) gs := by
  constructor
  · intro h
    refine ⟨h 0 (by simp),?_⟩
    intro j hj
    have h' := h (j+1) (by simpa using hj)
    change legal (n+(j+1)) gs[j] at h'
    rwa [show n+1+j = n+(j+1) by omega]
  · rintro ⟨h,hs⟩ (_|j) hj
    · exact h
    · have hj' : j<gs.length := by simpa using hj
      have h' := hs j hj'
      change legal (n+(j+1)) gs[j]
      rwa [show n+(j+1) = n+1+j by omega]
private theorem good_append {n : ℕ} {a b : List Gate} (x : good n a)
    (y : good (n+a.length) b) : good n (a++b) := by
  induction a generalizing n with
  | nil => simpa using y
  | cons g a ih =>
    obtain ⟨hg,ha⟩ := good_cons.mp x
    exact good_cons.mpr ⟨hg, ih ha (by rw [show n+1+a.length=n+(g::a).length by simp; omega]; exact y)⟩

private def val (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
private def run (gs : List Gate) (w : List Bool) := gs.foldl (fun ws g => ws ++ [val g ws]) w
private theorem run_len (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih => change (run gs (w++[val g w])).length = _; rw [ih]; simp; omega
private theorem run_app (a b : List Gate) (w : List Bool) : run (a++b) w = run b (run a w) := List.foldl_append
private theorem left {w z : List Bool} {i : ℕ} (h : i < w.length) : (w++z).getD i false = w.getD i false :=
  List.getD_append _ _ _ _ h
private theorem right {w z : List Bool} {i : ℕ} (h : w.length ≤ i) : (w++z).getD i false = z.getD (i-w.length) false :=
  List.getD_append_right _ _ _ _ h
private theorem endBit (w : List Bool) (b : Bool) : (w++[b]).getD w.length false = b := by rw [right (by omega),Nat.sub_self]; rfl
private theorem run_keep (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i<w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => change (run gs (w++[val g w])).getD i false = _; rw [ih _ (by simp; omega),left hi]
private theorem ofFnBit {n : ℕ} (f : Fin n → Bool) (i : Fin n) : (List.ofFn f).getD i.val false = f i := by
  simp [List.getD_eq_getElem?_getD,i.isLt]

private def rename (n k i : ℕ) := if i < n then i else if i < n+n then i+k else i+2*k
private def mapGate (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map r⟩
private theorem ren_le (n k i : ℕ) : rename n k i ≤ i+2*k := by unfold rename; split <;> (try split) <;> omega
private theorem ren_large (n k i : ℕ) (h : n+n ≤ i) : rename n k i = i+2*k := by
  simp [rename,show ¬i<n by omega,show ¬i<n+n by omega]
private theorem good_map {n k m : ℕ} {gs : List Gate} (h : good m gs) : good (m+2*k) (gs.map (mapGate (rename n k))) := by
  intro j hj
  have hj' : j<gs.length := by simpa using hj
  obtain ⟨op,len,back⟩ := h j hj'
  simp only [List.getElem_map]
  refine ⟨op, by simpa [mapGate] using len, ?_⟩
  intro i hi; obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hi
  have := back p hp; have := ren_le n k p; omega

private theorem run_map (n k : ℕ) (gs : List Gate) (w z : List Bool)
    (start : n+n ≤ w.length) (ok : good w.length gs) (len : z.length=w.length+2*k)
    (eq : ∀ i<w.length, z.getD (rename n k i) false = w.getD i false) :
    ∀ i<(run gs w).length, (run (gs.map (mapGate (rename n k))) z).getD (rename n k i) false = (run gs w).getD i false := by
  induction gs generalizing w z with
  | nil => exact eq
  | cons g gs ih =>
    obtain ⟨hg,ht⟩ := good_cons.mp ok
    have same : val (mapGate (rename n k) g) z = val g w := by
      unfold val mapGate; simp only [List.map_map]; congr 1
      exact List.map_congr_left (fun i hi => eq i (hg.2.2 i hi))
    apply ih (w++[val g w]) (z++[val (mapGate (rename n k) g) z]) (by simp; omega) (by simpa using ht) (by simp; omega)
    intro i hi
    by_cases h : i<w.length
    · rw [left (by have := ren_le n k i; omega),left h,eq i h]
    · have e : i=w.length := by simp at hi; omega
      subst i; rw [ren_large _ _ _ start,←len,endBit,endBit,same]

private def bin (op : GateOp) (i j : ℕ) : Gate := ⟨op,[i,j]⟩
private theorem bin_legal (op : GateOp) (h : op=.and ∨ op=.or) {i j m : ℕ} (hi : i<m) (hj : j<m) :
    legal m (bin op i j) := by simp [legal,bin,h,hi,hj]
private def borrowed {n k : ℕ} (a b : Fin k → Fin n) (j : Fin k) : Gate :=
  bin .or (n+k+(a j).val) (n+k+(b j).val)
private def full {n k : ℕ} (x y : Fin (n+k) → Bool) := List.ofFn x ++ List.ofFn y
private def borVal {n k : ℕ} (a b : Fin k → Fin n) (y : Fin (n+k) → Bool) (j : Fin k) :=
  y (Fin.castAdd k (a j)) || y (Fin.castAdd k (b j))
private def old {n k : ℕ} (a b : Fin k → Fin n) (x y : Fin (n+k) → Bool) :=
  (List.ofFn (fun i : Fin n => x (Fin.castAdd k i)) ++ List.ofFn (fun i : Fin n => y (Fin.castAdd k i))) ++ List.ofFn (borVal a b y)
private theorem full_x {n k : ℕ} (x y : Fin (n+k) → Bool) (i : Fin (n+k)) :
    (full x y).getD i.val false = x i := by rw [full,left (by simp),ofFnBit]
private theorem full_y {n k : ℕ} (x y : Fin (n+k) → Bool) (i : Fin (n+k)) :
    (full x y).getD (n+k+i.val) false = y i := by
  rw [full,right (by simp),List.length_ofFn,Nat.add_sub_cancel_left,ofFnBit]
private theorem prefix_run {n k : ℕ} (a b : Fin k → Fin n) (x y : Fin (n+k) → Bool) (js : List (Fin k)) (extra : List Bool) :
    run (js.map (borrowed a b)) (full x y ++ extra) = (full x y ++ extra) ++ js.map (borVal a b y) := by
  induction js generalizing extra with
  | nil => simp [run]
  | cons j js ih =>
    have hval : val (borrowed a b j) (full x y ++ extra) = borVal a b y j := by
      have ha : n+k+(a j).val < (full x y).length := by simp [full]; omega
      have hb : n+k+(b j).val < (full x y).length := by simp [full]; omega
      change ((full x y++extra).getD _ false || ((full x y++extra).getD _ false || false)) = _
      rw [left ha,left hb,Bool.or_false]
      exact congrArg₂ Bool.or (full_y x y (Fin.castAdd k (a j))) (full_y x y (Fin.castAdd k (b j)))
    change run (js.map _) ((full x y++extra)++[val _ _]) = _
    rw [hval,List.append_assoc,ih]; simp
private def pre {n k : ℕ} (a b : Fin k → Fin n) := (List.finRange k).map (borrowed a b)
private theorem pre_run {n k : ℕ} (a b : Fin k → Fin n) (x y : Fin (n+k) → Bool) :
    run (pre a b) (full x y) = full x y ++ List.ofFn (borVal a b y) := by
  simpa [pre,List.ofFn_eq_map] using prefix_run a b x y (List.finRange k) []
private theorem pre_good {n k : ℕ} (a b : Fin k → Fin n) : good (n+k+(n+k)) (pre a b) := by
  intro j hj
  have hm := List.getElem_mem hj
  obtain ⟨r,_,hr⟩ := List.mem_map.mp hm
  rw [← hr]; exact bin_legal _ (Or.inr rfl) (by have := (a r).isLt; omega) (by have := (b r).isLt; omega)
private theorem input_sim {n k : ℕ} (a b : Fin k → Fin n) (x y : Fin (n+k) → Bool)
    (i : ℕ) (hi : i<(old a b x y).length) :
    (full x y ++ List.ofFn (borVal a b y)).getD (rename n k i) false = (old a b x y).getD i false := by
  have size : i<n+n+k := by simpa [old,Nat.add_assoc] using hi
  by_cases h : i<n
  · let j : Fin n := ⟨i,h⟩
    rw [rename,ite_eq_left h,left (by simp [full]; omega),old,left (by simp; omega),left (by simp; omega)]
    exact (full_x x y (Fin.castAdd k j)).trans (ofFnBit (fun l : Fin n => x (Fin.castAdd k l)) j).symm
  · by_cases hh : i<n+n
    · let j : Fin n := ⟨i-n,by omega⟩
      rw [rename,ite_eq_right h,ite_eq_left hh,left (by simp [full]; omega),old,left (by simp; omega),right (by simp; omega), List.length_ofFn]
      rw [show i+k=n+k+(Fin.castAdd k j).val by change i+k=n+k+(i-n); omega,full_y]
      exact (ofFnBit (fun l : Fin n => y (Fin.castAdd k l)) j).symm
    · rw [ren_large _ _ _ (by omega),right (by simp [full]; omega),old,right (by simp; omega)]
      congr 1; simp [full]; omega

private def core {n k : ℕ} (a b : Fin k → Fin n) (C : Circuit) : Circuit :=
  ⟨pre a b ++ C.gates.map (mapGate (rename n k)),rename n k C.output⟩
private theorem core_size {n k : ℕ} (a b : Fin k → Fin n) (C : Circuit) : (core a b C).size = k+C.size := by
  simp [Circuit.size,core,pre]
private theorem core_good {n k : ℕ} (a b : Fin k → Fin n) {C : Circuit} (ok : IsAO2 (n+n+k) C) :
    good (n+k+(n+k)) (core a b C).gates := by
  apply good_append (pre_good a b)
  have h := good_map (n:=n) (k:=k) ((good_iff _ _).mpr ok)
  simpa only [pre,List.length_map,List.length_finRange,show n+k+(n+k)+k = (n+n+k)+2*k by omega] using h
private theorem core_output {n k : ℕ} (a b : Fin k → Fin n) (C : Circuit) (ho : C.output<n+n+k+C.size) :
    (core a b C).output < n+k+(n+k)+(core a b C).size := by
  rw [core_size]; change rename n k C.output < _; have := ren_le n k C.output; omega
private theorem core_eval {n k : ℕ} (a b : Fin k → Fin n) {C : Circuit} (ok : IsAO2 (n+n+k) C)
    (ho : C.output<n+n+k+C.size) (x y : Fin (n+k) → Bool) :
    (core a b C).eval (full x y) = C.eval (old a b x y) := by
  change (run (pre a b ++ _) (full x y)).getD _ false = (run C.gates (old a b x y)).getD _ false
  rw [run_app,pre_run]
  apply run_map n k C.gates (old a b x y) _ (by simp [old]) (by simpa [old,Nat.add_assoc] using (good_iff _ _).mpr ok)
    (by simp [old,full]; omega) (input_sim a b x y) C.output
  simpa [run_len,old,Circuit.size,Nat.add_assoc] using ho
private theorem core_borrow {n k : ℕ} (a b : Fin k → Fin n) (C : Circuit) (x y : Fin (n+k) → Bool) (j : Fin k) :
    (run (core a b C).gates (full x y)).getD (n+k+(n+k)+j.val) false = borVal a b y j := by
  rw [core,run_app,pre_run,run_keep _ _ (by simp [full]; omega),right (by simp [full])]
  simp only [full,List.length_append,List.length_ofFn,Nat.add_sub_cancel_left]; exact ofFnBit _ j

private def append3 (N : ℕ) (D : Circuit) (borrow xp yp : ℕ) : Circuit :=
  let z := N+D.size
  ⟨D.gates ++ [bin .or borrow yp, bin .and xp z, bin .or D.output (z+1)],z+2⟩
private theorem append3_size (N : ℕ) (D : Circuit) (b x y : ℕ) : (append3 N D b x y).size = D.size+3 := by
  simp [append3,Circuit.size]
private theorem append3_good {N : ℕ} {D : Circuit} {b x y : ℕ} (h : good N D.gates)
    (ob : D.output<N+D.size) (hb : b<N+D.size) (hx : x<N+D.size) (hy : y<N+D.size) :
    good N (append3 N D b x y).gates := by
  apply good_append h
  change good (N+D.size) [_,_,_]
  refine good_cons.mpr ⟨bin_legal _ (Or.inr rfl) hb hy,good_cons.mpr ⟨bin_legal _ (Or.inl rfl) (by omega) (by omega),
    good_cons.mpr ⟨bin_legal _ (Or.inr rfl) (by omega) (by omega),?_⟩⟩⟩
  intro j hj; simp at hj
private theorem append3_output (N : ℕ) (D : Circuit) (b x y : ℕ) :
    (append3 N D b x y).output < N+(append3 N D b x y).size := by
  rw [append3_size]; change N+D.size+2 < _; omega
private theorem append3_keep {N : ℕ} (D : Circuit) (b x y : ℕ) (w : List Bool) (i : ℕ) (hi : i<(run D.gates w).length) :
    (run (append3 N D b x y).gates w).getD i false = (run D.gates w).getD i false := by
  exact (congrArg (fun ws : List Bool => ws.getD i false) (run_app _ _ _)).trans (run_keep _ _ hi)
private theorem append3_eval {N : ℕ} (D : Circuit) (b x y : ℕ) (w : List Bool) (hw : w.length=N)
    (ho : D.output<N+D.size) (hx : x<N+D.size) :
    (append3 N D b x y).eval w = (D.eval w || ((run D.gates w).getD x false &&
      ((run D.gates w).getD b false || (run D.gates w).getD y false))) := by
  let W := run D.gates w
  have len : W.length=N+D.size := by simp [W,run_len,hw,Circuit.size]
  let B := W.getD b false || W.getD y false
  let X := W.getD x false && B
  change (run (D.gates ++ _) w).getD (N+D.size+2) false = _
  rw [run_app]
  have g1 : val (bin .or b y) W = B := by simp [B,val,bin,GateOp.eval]
  have g2 : val (bin .and x (N+D.size)) (W++[B]) = X := by
    change ((W++[B]).getD x false && ((W++[B]).getD _ false && true)) = _
    rw [left (by omega),← len,endBit,Bool.and_true]
  have g3 : val (bin .or D.output (N+D.size+1)) (W++[B]++[X]) = (D.eval w || X) := by
    change ((W++[B]++[X]).getD D.output false || ((W++[B]++[X]).getD _ false || false)) = _
    rw [left (by simp; omega),left (by omega),show N+D.size+1=(W++[B]).length by simp [len],endBit,Bool.or_false]
    rfl
  change (run [bin .or b y,bin .and x (N+D.size),bin .or D.output (N+D.size+1)] W).getD _ false = _
  simp only [run,List.foldl_cons,List.foldl_nil,g1,g2,g3]
  rw [show N+D.size+2=(W++[B]++[X]).length by simp [len],endBit]
  rfl

private def next {n k : ℕ} (D : Circuit) (j : Fin k) : Circuit :=
  append3 (n+k+(n+k)) D (n+k+(n+k)+j.val) (n+j.val) (n+k+(n+j.val))
private def term {n k : ℕ} (a b : Fin k → Fin n) (x y : Fin (n+k) → Bool) (j : Fin k) :=
  x (Fin.natAdd n j) && (borVal a b y j || y (Fin.natAdd n j))
private def Ready {n k : ℕ} (a b : Fin k → Fin n) (D : Circuit) : Prop :=
  good (n+k+(n+k)) D.gates ∧ D.output < n+k+(n+k)+D.size ∧ k≤D.size ∧
  ∀ x y j, (run D.gates (full x y)).getD (n+k+(n+k)+(j : Fin k).val) false = borVal a b y j
private theorem ready_next {n k : ℕ} {a b : Fin k → Fin n} {D : Circuit} (h : Ready a b D) (j : Fin k) :
    Ready a b (next (n:=n) D j) := by
  have sz := h.2.2.1
  refine ⟨append3_good h.1 h.2.1 (by omega) (by omega) (by omega),append3_output _ _ _ _ _,?_,?_⟩
  · rw [next,append3_size]; omega
  · intro x y i; rw [next,append3_keep _ _ _ _ _ _ (by simp [run_len,full]; exact i.isLt.trans_le sz)]
    exact h.2.2.2 x y i
private theorem next_eval {n k : ℕ} {a b : Fin k → Fin n} {D : Circuit} (h : Ready a b D) (j : Fin k)
    (x y : Fin (n+k) → Bool) : (next (n:=n) D j).eval (full x y) = (D.eval (full x y) || term a b x y j) := by
  have sz := h.2.2.1
  rw [next,append3_eval _ _ _ _ _ (by simp [full]) h.2.1 (by omega),h.2.2.2 x y j]
  rw [run_keep _ _ (by simp [full]; omega),run_keep _ _ (by simp [full])]
  exact congrArg (fun z => D.eval (full x y) || z)
    (congrArg₂ Bool.and (full_x x y (Fin.natAdd n j)) (congrArg (fun z => borVal a b y j || z) (full_y x y (Fin.natAdd n j))))
private theorem fold_spec {n k : ℕ} {a b : Fin k → Fin n} (js : List (Fin k)) (D : Circuit) (h : Ready a b D) :
    let E := js.foldl (next (n:=n)) D
    Ready a b E ∧ E.size = D.size+3*js.length ∧ ∀ x y,
      E.eval (full x y) = (D.eval (full x y) || js.any (term a b x y)) := by
  induction js generalizing D with
  | nil => exact ⟨h,by simp,fun x y => by simp⟩
  | cons j js ih =>
    obtain ⟨he,sz,ev⟩ := ih (next (n:=n) D j) (ready_next h j)
    refine ⟨he,?_,?_⟩
    · change (js.foldl (next (n:=n)) (next (n:=n) D j)).size = _
      rw [sz,next,append3_size,List.length_cons]; omega
    · intro x y
      change (js.foldl (next (n:=n)) (next (n:=n) D j)).eval (full x y) = _
      rw [ev,next_eval h j x y,List.any_cons,Bool.or_assoc]

/-- Materialize all borrowed disjunctions, run the old circuit on the renamed
wires, and append three gates for each attached point. -/
theorem compile (n k : ℕ) (a b : Fin k → Fin n) (C : Circuit) (ok : IsAO2 (n+n+k) C)
    (ho : C.output < n+n+k+C.size) :
    ∃ D : Circuit, IsAO2 ((n+k)+(n+k)) D ∧ D.size ≤ C.size+4*k ∧ ∀ x y : Fin (n+k) → Bool,
      D.eval (List.ofFn x ++ List.ofFn y) =
      (C.eval ((List.ofFn (fun i : Fin n => x (Fin.castAdd k i)) ++
        List.ofFn (fun i : Fin n => y (Fin.castAdd k i))) ++
        List.ofFn (fun j : Fin k => y (Fin.castAdd k (a j)) || y (Fin.castAdd k (b j)))) ||
        (List.finRange k).any (fun j => x (Fin.natAdd n j) &&
        ((y (Fin.castAdd k (a j)) || y (Fin.castAdd k (b j))) || y (Fin.natAdd n j)))) := by
  let B := core a b C
  have ready : Ready a b B := ⟨core_good a b ok,core_output a b C ho,by simp [B,core_size],core_borrow a b C⟩
  let D := (List.finRange k).foldl (next (n:=n)) B
  obtain ⟨rd,sz,ev⟩ := fold_spec (List.finRange k) B ready
  refine ⟨D,(good_iff _ _).mp rd.1,?_,?_⟩
  · change ((List.finRange k).foldl _ B).size ≤ _
    rw [sz,show B.size=k+C.size from core_size a b C,List.length_finRange]; omega
  · intro x y
    change D.eval (full x y) = (C.eval (old a b x y) || (List.finRange k).any (term a b x y))
    exact (ev x y).trans (congrArg (fun z => z || (List.finRange k).any (term a b x y)) (core_eval a b ok ho x y))
end PEqualNP.Outside.L_meta_8784

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem PEqualNP.Outside.L_meta_8784 :
    ∀ (n k : ℕ) (a b : Fin k → Fin n) (C : Circuit),
      IsAO2 (n+n+k) C → C.output < n+n+k+C.size →
      ∃ D : Circuit, IsAO2 ((n+k)+(n+k)) D ∧ D.size ≤ C.size+4*k ∧
      ∀ x y : Fin (n+k) → Bool,
        D.eval (List.ofFn x ++ List.ofFn y) =
          (C.eval ((List.ofFn (fun i : Fin n => x (Fin.castAdd k i)) ++
                    List.ofFn (fun i : Fin n => y (Fin.castAdd k i))) ++
                    List.ofFn (fun j => y (Fin.castAdd k (a j)) || y (Fin.castAdd k (b j)))) ||
           (List.finRange k).any (fun j => x (Fin.natAdd n j) &&
             ((y (Fin.castAdd k (a j)) || y (Fin.castAdd k (b j))) || y (Fin.natAdd n j)))) := by
  exact PEqualNP.Outside.L_meta_8784.compile
