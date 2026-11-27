import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14622

abbrev Fn := (Fin 8 → Bool) → Bool

def z : Fn := fun _ => false

def u : Fn := fun _ => true

def inv (f : Fn) : Fn := fun x => !f x

def meet (f g : Fn) : Fn := fun x => f x && g x

def var (i : Fin 8) : Fn := fun x => x i

def avail (S : Set Fn) (f : Fn) : Prop := f = z ∨ f = u ∨ f ∈ S ∨ inv f ∈ S

-- A proof of reachability with exactly k conjunctions. Constants and wire inversions are free.
inductive Run (f : Fn) : ℕ → Set Fn → Prop
  | done {S} : avail S f → Run f 0 S
  | step {k S a b} : avail S a → avail S b → Run f k (insert (meet a b) S) → Run f (k+1) S

def seed (I : Set (Fin 8)) : Set Fn := var '' I

def fix (i : Fin 8) (b : Bool) (f : Fn) : Fn := fun x => f (Function.update x i b)

def nonconst (f : Fn) : Prop := f ≠ z ∧ f ≠ u

@[local simp] lemma inv_inv (f : Fn) : inv (inv f) = f := by funext x; simp [inv]
@[local simp] lemma inv_z : inv z = u := rfl
@[local simp] lemma inv_u : inv u = z := rfl
@[local simp] lemma meet_z_left (a : Fn) : meet z a = z := rfl
@[local simp] lemma meet_z_right (a : Fn) : meet a z = z := by funext x; simp [meet, z]
@[local simp] lemma meet_u_left (a : Fn) : meet u a = a := rfl
@[local simp] lemma meet_u_right (a : Fn) : meet a u = a := by funext x; simp [meet, u]

lemma avail_mono {S T : Set Fn} {a : Fn} (h : S ⊆ T) : avail S a → avail T a := by
  rintro (rfl | rfl | ha | ha)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl (h ha)))
  · exact Or.inr (Or.inr (Or.inr (h ha)))

lemma avail_z (S : Set Fn) : avail S z := Or.inl rfl
lemma avail_u (S : Set Fn) : avail S u := Or.inr (Or.inl rfl)
lemma avail_of_mem {S : Set Fn} {f : Fn} (h : f ∈ S) : avail S f := Or.inr (Or.inr (Or.inl h))

lemma avail_inv {S : Set Fn} {a : Fn} (h : avail S a) : avail S (inv a) := by
  rcases h with rfl | rfl | hm | hm
  · exact avail_u S
  · exact avail_z S
  · exact Or.inr (Or.inr (Or.inr (by simpa using hm)))
  · exact avail_of_mem hm

lemma Run.changeStock {f : Fn} {k : ℕ} {S T : Set Fn} (h : Run f k S)
    (sub : ∀ a ∈ S, avail T a) : Run f k T := by
  have lift {A B : Set Fn} (hm : ∀ a ∈ A, avail B a) {a} (ha : avail A a) : avail B a := by
    rcases ha with rfl | rfl | h | h
    · exact avail_z B
    · exact avail_u B
    · exact hm _ h
    · simpa using avail_inv (hm _ h)
  induction h generalizing T with
  | done ha => exact .done (lift sub ha)
  | @step j S a b ha hb hh ih =>
    refine .step (lift sub ha) (lift sub hb) (ih ?_)
    intro c hc
    rcases Set.mem_insert_iff.mp hc with rfl | hc
    · exact avail_of_mem (Set.mem_insert _ _)
    · exact avail_mono (Set.subset_insert _ _) (sub _ hc)

open PEqualNP.CircuitLowerBounds

def counted (g : Gate) : Bool :=
  match g.op with
  | .not => false
  | _ => true

private lemma bridge_getD_avail {S : Set Fn} {ws : List Fn}
    (hw : ∀ f ∈ ws, avail S f) {d : Fn} (hd : avail S d) (i : Nat) :
    avail S (ws.getD i d) := by
  induction ws generalizing i with
  | nil => cases i <;> exact hd
  | cons f ws ih =>
    cases i with
    | zero => exact hw f (by simp)
    | succ i => exact ih (fun a ha => hw a (List.mem_cons_of_mem f ha)) i

private lemma bridge_app_getD (ws : List Fn) (x : Fin 8 → Bool) (i : Nat) :
    (ws.map fun f => f x).getD i false = (ws.getD i z) x := by
  induction ws generalizing i with
  | nil => cases i <;> rfl
  | cons f ws ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

private def bridgeGate (ws : List Fn) (g : Gate) : Fn :=
  fun x => g.op.eval (g.inputs.map fun i => (ws.getD i z) x)

private def bridgeRead (ws : List Fn) (is : List Nat) (d : Fn) (i : Nat) : Fn :=
  (is.map fun j => ws.getD j z).getD i d

private lemma bridge_read_avail {S : Set Fn} {ws : List Fn}
    (hw : ∀ f ∈ ws, avail S f) (is : List Nat) {d : Fn} (hd : avail S d) (i : Nat) :
    avail S (bridgeRead ws is d i) := by
  apply bridge_getD_avail _ hd i
  intro f hf
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hf
  exact bridge_getD_avail hw (avail_z S) j

private lemma bridge_gate_and (ws : List Fn) (is : List Nat) (h : is.length ≤ 2) :
    bridgeGate ws ⟨.and, is⟩ = meet (bridgeRead ws is u 0) (bridgeRead ws is u 1) := by
  rcases is with _ | ⟨i, _ | ⟨j, _ | ⟨k, is⟩⟩⟩
  · rfl
  · funext x
    cases (ws.getD i z) x <;> rfl
  · funext x
    change ((ws.getD i z) x && ((ws.getD j z) x && true)) =
      ((ws.getD i z) x && (ws.getD j z) x)
    cases (ws.getD j z) x <;> rfl
  · simp at h

private lemma bridge_gate_or (ws : List Fn) (is : List Nat) (h : is.length ≤ 2) :
    bridgeGate ws ⟨.or, is⟩ =
      inv (meet (inv (bridgeRead ws is z 0)) (inv (bridgeRead ws is z 1))) := by
  rcases is with _ | ⟨i, _ | ⟨j, _ | ⟨k, is⟩⟩⟩
  · rfl
  · funext x
    change ((ws.getD i z) x || false) = !(!(ws.getD i z) x && !false)
    cases (ws.getD i z) x <;> rfl
  · funext x
    change ((ws.getD i z) x || ((ws.getD j z) x || false)) =
      !(!(ws.getD i z) x && !(ws.getD j z) x)
    cases (ws.getD i z) x <;> cases (ws.getD j z) x <;> rfl
  · simp at h

private lemma bridge_gate_not (ws : List Fn) (is : List Nat) :
    bridgeGate ws ⟨.not, is⟩ = inv (bridgeRead ws is z 0) := by
  cases is <;> rfl

private lemma bridge_add {S : Set Fn} {ws : List Fn} (hw : ∀ f ∈ ws, avail S f)
    (g : Gate) (legal : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    {r : Fn} {k : Nat}
    (next : ∀ T, S ⊆ T → avail T (bridgeGate ws g) → Run r k T) :
    Run r (k + if counted g then 1 else 0) S := by
  rcases g with ⟨op, is⟩
  change (op = .and ∨ op = .or ∨ op = .not) ∧ is.length ≤ 2 at legal
  rcases legal with ⟨h | h | h, hlen⟩
  · subst op
    change Run r (k + 1) S
    refine .step (bridge_read_avail hw is (avail_u S) 0)
      (bridge_read_avail hw is (avail_u S) 1) (next _ (Set.subset_insert _ _) ?_)
    rw [bridge_gate_and ws is hlen]
    exact avail_of_mem (Set.mem_insert _ _)
  · subst op
    change Run r (k + 1) S
    refine .step (avail_inv (bridge_read_avail hw is (avail_z S) 0))
      (avail_inv (bridge_read_avail hw is (avail_z S) 1)) (next _ (Set.subset_insert _ _) ?_)
    rw [bridge_gate_or ws is hlen]
    exact avail_inv (avail_of_mem (Set.mem_insert _ _))
  · subst op
    change Run r k S
    apply next S (fun _ h => h)
    rw [bridge_gate_not]
    exact avail_inv (bridge_read_avail hw is (avail_z S) 0)

private def bridgeWires (gs : List Gate) (ws : List Fn) : List Fn :=
  gs.foldl (fun w g => w ++ [bridgeGate w g]) ws

private lemma bridge_wires_map (gs : List Gate) (ws : List Fn) (x : Fin 8 → Bool) (o : Nat) :
    (bridgeWires gs ws).map (fun f => f x) = Circuit.wires ⟨gs, o⟩ (ws.map fun f => f x) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    change (bridgeWires gs (ws ++ [bridgeGate ws g])).map (fun f => f x) =
      Circuit.wires ⟨gs, o⟩ ((ws.map fun f => f x) ++
        [g.op.eval (g.inputs.map fun i => (ws.map fun f => f x).getD i false)])
    rw [ih, List.map_append]
    simp only [List.map_cons, List.map_nil, bridgeGate, bridge_app_getD]

private lemma bridge_compile_from (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (ws : List Fn) (S : Set Fn) (hw : ∀ f ∈ ws, avail S f) :
    Run ((bridgeWires gs ws).getD o z) (gs.countP counted) S := by
  induction gs generalizing ws S with
  | nil => exact .done (bridge_getD_avail hw (avail_z S) o)
  | cons g gs ih =>
    have hg := legal g List.mem_cons_self
    have hgs : ∀ h ∈ gs, _ := fun h hh => legal h (List.mem_cons_of_mem g hh)
    change Run ((bridgeWires gs (ws ++ [bridgeGate ws g])).getD o z) ((g :: gs).countP counted) S
    have h := bridge_add hw g hg (r := (bridgeWires gs (ws ++ [bridgeGate ws g])).getD o z)
      (k := gs.countP counted) (fun T hST hGate => ih hgs _ T (by
        intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · exact avail_mono hST (hw f hf)
        · rcases List.mem_singleton.mp hf with rfl
          exact hGate))
    cases hc : counted g <;> simpa [List.countP_cons, hc] using h

lemma compile (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    Run (fun x => Circuit.eval ⟨gs, o⟩ (List.ofFn x)) (gs.countP counted) (seed Set.univ) := by
  let ws : List Fn := List.ofFn var
  have hw : ∀ f ∈ ws, avail (seed Set.univ) f := by
    intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    exact avail_of_mem ⟨i, Set.mem_univ _, rfl⟩
  have heq : (bridgeWires gs ws).getD o z = fun x => Circuit.eval ⟨gs, o⟩ (List.ofFn x) := by
    funext x
    change ((bridgeWires gs ws).getD o z) x = (Circuit.wires ⟨gs, o⟩ (List.ofFn x)).getD o false
    have hm : ws.map (fun f => f x) = List.ofFn x := by
      simp [ws, var]
    rw [← bridge_app_getD, bridge_wires_map, hm]
  exact heq ▸ bridge_compile_from gs o legal ws (seed Set.univ) hw

lemma counted_lt (gs : List Gate) (h : ∃ g ∈ gs, g.op = .not) : gs.countP counted < gs.length := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨a, ha, haop⟩ := h
    rcases List.mem_cons.mp ha with ha | ha
    · subst a
      have hc : counted g = false := by simp [counted, haop]
      have hb : gs.countP counted ≤ gs.length := List.countP_le_length
      rw [List.countP_cons, hc, List.length_cons]
      change gs.countP counted < gs.length + 1
      omega
    · have hlt := ih ⟨a, ha, haop⟩
      cases hc : counted g
      · rw [List.countP_cons, hc, List.length_cons]
        change gs.countP counted < gs.length + 1
        omega
      · rw [List.countP_cons, hc, List.length_cons]
        change gs.countP counted + 1 < gs.length + 1
        exact Nat.succ_lt_succ hlt



lemma avail_insert {S : Set Fn} {t a : Fn} :
    avail (insert t S) a ↔ avail S a ∨ a = t ∨ a = inv t := by
  have E : inv a = t ↔ a = inv t := ⟨fun h => by rw [← h, inv_inv], fun h => by rw [h, inv_inv]⟩
  simp only [avail, Set.mem_insert_iff, E]
  tauto

@[local simp] lemma fix_z (i : Fin 8) (c : Bool) : fix i c z = z := rfl
@[local simp] lemma fix_u (i : Fin 8) (c : Bool) : fix i c u = u := rfl
@[local simp] lemma fix_inv (i : Fin 8) (c : Bool) (a : Fn) : fix i c (inv a) = inv (fix i c a) := rfl
@[local simp] lemma fix_meet (i : Fin 8) (c : Bool) (a b : Fn) :
    fix i c (meet a b) = meet (fix i c a) (fix i c b) := rfl

lemma fix_var (i : Fin 8) (c : Bool) : fix i c (var i) = if c then u else z := by
  funext x
  cases c <;> simp [fix, var, z, u]

lemma image_insert_fn (r : Fn → Fn) (h : Fn) (S : Set Fn) :
    r '' insert h S = insert (r h) (r '' S) := by
  ext a
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases Set.mem_insert_iff.mp hw with rfl | hw
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨_, hw, rfl⟩
  · intro ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact ⟨_, Set.mem_insert _ _, rfl⟩
    · obtain ⟨w, hw, rfl⟩ := ha
      exact ⟨_, Set.mem_insert_of_mem _ hw, rfl⟩

lemma avail_fix (i : Fin 8) (c : Bool) {S : Set Fn} {a : Fn} (h : avail S a) :
    avail (fix i c '' S) (fix i c a) := by
  rcases h with rfl | rfl | ha | ha
  · exact avail_z _
  · exact avail_u _
  · exact avail_of_mem ⟨_, ha, rfl⟩
  · exact Or.inr (Or.inr (Or.inr ⟨_, ha, rfl⟩))

lemma run_fix (i : Fin 8) (c : Bool) {f : Fn} {k S} (h : Run f k S) :
    Run (fix i c f) k (fix i c '' S) := by
  induction h with
  | done hf => exact .done (avail_fix i c hf)
  | @step k S a b ha hb _ ih =>
    apply Run.step (avail_fix i c ha) (avail_fix i c hb)
    simpa only [image_insert_fn, fix_meet] using ih

lemma isConst_avail {S : Set Fn} {a : Fn} (h : a = z ∨ a = u) : avail S a := by
  rcases h with rfl | rfl
  · exact avail_z _
  · exact avail_u _

lemma isConst_inv {a : Fn} (h : a = z ∨ a = u) : inv a = z ∨ inv a = u := by
  rcases h with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

lemma isConst_var (i : Fin 8) (c : Bool) : fix i c (var i) = z ∨ fix i c (var i) = u := by
  cases c <;> simp [fix_var]

lemma meet_avail_of_const {S : Set Fn} {a b : Fn} (ha : avail S a) (hb : avail S b)
    (hc : (a = z ∨ a = u) ∨ (b = z ∨ b = u)) : avail S (meet a b) := by
  rcases hc with (rfl | rfl) | (rfl | rfl)
  · simpa using avail_z S
  · simpa using hb
  · simpa using avail_z S
  · simpa using ha

lemma avail_fix_insert {i : Fin 8} {c : Bool} {S : Set Fn} {t a : Fn}
    (ht : fix i c t = z ∨ fix i c t = u) (ha : avail (insert t S) a) :
    avail (fix i c '' S) (fix i c a) := by
  rcases avail_insert.mp ha with h | rfl | rfl
  · exact avail_fix _ _ h
  · exact isConst_avail ht
  · exact avail_inv (isConst_avail ht)

lemma not_avail_const {i : Fin 8} {c : Bool} {S : Set Fn} {t a : Fn}
    (ht : fix i c t = z ∨ fix i c t = u) (ha : avail (insert t S) a) (hn : ¬ avail S a) :
    fix i c a = z ∨ fix i c a = u := by
  rcases (avail_insert.mp ha).resolve_left hn with rfl | rfl
  · exact ht
  · exact isConst_inv ht

lemma skip_two_insertions {i : Fin 8} {c : Bool} {f t d : Fn} {k S}
    (ht : avail (fix i c '' S) (fix i c t)) (hd : avail (fix i c '' S) (fix i c d))
    (h : Run f k (insert d (insert t S))) : Run (fix i c f) k (fix i c '' S) := by
  apply (run_fix i c h).changeStock
  rintro _ ⟨w, hw, rfl⟩
  rcases Set.mem_insert_iff.mp hw with rfl | hw
  · exact hd
  · rcases Set.mem_insert_iff.mp hw with rfl | hw
    · exact ht
    · exact avail_of_mem ⟨_, hw, rfl⟩

-- If a new wire becomes constant, either the original run did not need it or
-- the first step that needed it can be bypassed in the restricted run.
lemma dropConst {f : Fn} {i : Fin 8} {c : Bool} {k : Nat} {S : Set Fn} {t : Fn}
    (hn : nonconst (fix i c f)) (ht : fix i c t = z ∨ fix i c t = u)
    (h : Run f k (insert t S)) :
    Run f k S ∨ ∃ j, j+1 ≤ k ∧ Run (fix i c f) j (fix i c '' S) := by
  induction k generalizing S with
  | zero =>
    cases h with
    | done ha =>
      apply Or.inl
      apply Run.done
      by_contra no
      exact (not_avail_const ht ha no).elim hn.1 hn.2
  | succ k ih =>
    cases h with
    | @step _ _ a b ha hb next =>
      by_cases hab : avail S a ∧ avail S b
      · rw [Set.insert_comm] at next
        rcases ih next with short | ⟨j, hj, run⟩
        · exact Or.inl (.step hab.1 hab.2 short)
        · apply Or.inr
          refine ⟨j+1, by omega, .step (avail_fix _ _ hab.1) (avail_fix _ _ hab.2) ?_⟩
          simpa only [image_insert_fn, fix_meet] using run
      · have hc : (fix i c a = z ∨ fix i c a = u) ∨ (fix i c b = z ∨ fix i c b = u) := by
          by_cases haa : avail S a
          · exact Or.inr (not_avail_const ht hb (fun h => hab ⟨haa, h⟩))
          · exact Or.inl (not_avail_const ht ha haa)
        have hg := meet_avail_of_const (avail_fix_insert ht ha) (avail_fix_insert ht hb) hc
        exact Or.inr ⟨k, le_rfl, skip_two_insertions (d := meet a b) (isConst_avail ht) hg next⟩

def independent (i : Fin 8) (S : Set Fn) : Prop := ∀ a ∈ S, ∀ c, fix i c a = a

lemma avail_independent {i : Fin 8} {S : Set Fn} {a : Fn}
    (hi : independent i S) (h : avail S a) (c : Bool) : fix i c a = a := by
  rcases h with rfl | rfl | h | h
  · rfl
  · rfl
  · exact hi _ h _
  · have hh := congrArg inv (hi _ h c)
    simpa using hh

lemma independent_insert {i : Fin 8} {S : Set Fn} {a b : Fn}
    (hi : independent i S) (ha : avail S a) (hb : avail S b) : independent i (insert (meet a b) S) := by
  intro r hr c
  rcases Set.mem_insert_iff.mp hr with rfl | hr
  · simp [avail_independent hi ha c, avail_independent hi hb c]
  · exact hi _ hr _

lemma image_independent {i : Fin 8} {S : Set Fn} (hi : independent i S) (c : Bool) : fix i c '' S = S := by
  ext a
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [hi _ hw _]
  · intro h
    exact ⟨a, h, hi _ h _⟩

lemma forbid_done {i : Fin 8} {c : Bool} {S : Set Fn} {f : Fn}
    (hi : independent i S) (dep : fix i false f ≠ fix i true f) (hn : nonconst (fix i c f))
    (hf : avail (insert (var i) S) f) : False := by
  by_cases h : avail S f
  · exact dep ((avail_independent hi h false).trans (avail_independent hi h true).symm)
  · exact (not_avail_const (isConst_var i c) hf h).elim hn.1 hn.2

lemma choose_ctrl {i : Fin 8} {S : Set Fn} {a b : Fn}
    (ha : avail (insert (var i) S) a) (hb : avail (insert (var i) S) b)
    (hab : ¬ (avail S a ∧ avail S b)) : ∃ c, fix i c (meet a b) = z := by
  by_cases haa : avail S a
  · rcases (avail_insert.mp hb).resolve_left (fun h => hab ⟨haa, h⟩) with rfl | rfl
    · exact ⟨false, by simp [fix_var]⟩
    · exact ⟨true, by simp [fix_var]⟩
  · rcases (avail_insert.mp ha).resolve_left haa with rfl | rfl
    · exact ⟨false, by simp [fix_var]⟩
    · exact ⟨true, by simp [fix_var]⟩

lemma elim1_stock {f : Fn} {k S} (i : Fin 8) (c : Bool)
    (hi : independent i S) (dep : fix i false f ≠ fix i true f) (hn : nonconst (fix i c f))
    (h : Run f k (insert (var i) S)) : ∃ j, j+1 ≤ k ∧ Run (fix i c f) j S := by
  induction k generalizing S with
  | zero =>
    cases h with
    | done hf => exact (forbid_done hi dep hn hf).elim
  | succ k ih =>
    cases h with
    | @step _ _ a b ha hb next =>
      by_cases hab : avail S a ∧ avail S b
      · rw [Set.insert_comm] at next
        obtain ⟨j, hj, run⟩ := ih (independent_insert hi hab.1 hab.2) next
        exact ⟨j+1, by omega, .step hab.1 hab.2 run⟩
      · have ht := isConst_var i c
        have hc : (fix i c a = z ∨ fix i c a = u) ∨ (fix i c b = z ∨ fix i c b = u) := by
          by_cases haa : avail S a
          · exact Or.inr (not_avail_const ht hb (fun h => hab ⟨haa, h⟩))
          · exact Or.inl (not_avail_const ht ha haa)
        have hg := meet_avail_of_const (avail_fix_insert ht ha) (avail_fix_insert ht hb) hc
        have out := skip_two_insertions (d := meet a b) (isConst_avail ht) hg next
        rw [image_independent hi c] at out
        exact ⟨k, le_rfl, out⟩

-- Choose the input value that forces the first reader to zero (false for a
-- positive literal, true for its inverse). The nonconstant output cannot be
-- this forced wire. If it is not used at all, repeat on the shorter run.
lemma elim2_stock {f : Fn} {k S} (i : Fin 8)
    (hi : independent i S) (dep : fix i false f ≠ fix i true f) (hn : ∀ c, nonconst (fix i c f))
    (h : Run f k (insert (var i) S)) : ∃ c j, j+2 ≤ k ∧ Run (fix i c f) j S := by
  induction k generalizing S with
  | zero =>
    cases h with
    | done hf => exact (forbid_done hi dep (hn false) hf).elim
  | succ k ih =>
    cases h with
    | @step _ _ a b ha hb next =>
      by_cases hab : avail S a ∧ avail S b
      · rw [Set.insert_comm] at next
        obtain ⟨c, j, hj, run⟩ := ih (independent_insert hi hab.1 hab.2) next
        exact ⟨c, j+1, by omega, .step hab.1 hab.2 run⟩
      · obtain ⟨c, hc⟩ := choose_ctrl ha hb hab
        rcases dropConst (hn c) (Or.inl hc) next with unused | ⟨j, hj, run⟩
        · obtain ⟨b, j, hj, run⟩ := ih hi unused
          exact ⟨b, j, by omega, run⟩
        · rw [image_insert_fn, image_independent hi c] at run
          have reduced := run.changeStock (T := S) (by
            intro a m
            rcases Set.mem_insert_iff.mp m with rfl | m
            · exact isConst_avail (isConst_var i c)
            · exact avail_of_mem m)
          exact ⟨c, j, by omega, reduced⟩

lemma seed_independent {i : Fin 8} {I : Set (Fin 8)} (hi : i ∉ I) : independent i (seed I) := by
  rintro _ ⟨j, hj, rfl⟩ c
  have h : j ≠ i := fun e => hi (e ▸ hj)
  funext x
  simp [fix, var, h]

lemma seed_insert (i : Fin 8) (I : Set (Fin 8)) : seed (insert i I) = insert (var i) (seed I) := by
  ext a
  constructor
  · rintro ⟨j, hj, rfl⟩
    rcases Set.mem_insert_iff.mp hj with rfl | hj
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨_, hj, rfl⟩
  · intro ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact ⟨_, Set.mem_insert _ _, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := ha
      exact ⟨_, Set.mem_insert_of_mem _ hj, rfl⟩

lemma elim1 {f : Fn} {k} (i : Fin 8) (b : Bool) (I : Set (Fin 8)) (hi : i ∉ I)
    (dep : fix i false f ≠ fix i true f) (hn : nonconst (fix i b f))
    (h : Run f k (seed (insert i I))) : ∃ j, j+1≤k ∧ Run (fix i b f) j (seed I) := by
  rw [seed_insert] at h
  exact elim1_stock i b (seed_independent hi) dep hn h

lemma elim2 {f : Fn} {k} (i : Fin 8) (I : Set (Fin 8)) (hi : i ∉ I)
    (dep : fix i false f ≠ fix i true f) (hn : ∀ b, nonconst (fix i b f))
    (h : Run f k (seed (insert i I))) : ∃ b j, j+2≤k ∧ Run (fix i b f) j (seed I) := by
  rw [seed_insert] at h
  exact elim2_stock i (seed_independent hi) dep hn h

def F : Fn := fun x => decide (∃ i <
    ([0, 4, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7] : List ℕ).length / 2,
    (List.ofFn x).getD
      (([0, 4, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0)
      false = true ∧
    (List.ofFn x).getD
      (([0, 4, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0)
      false = true)

def gmono : List Gate :=
  [⟨.or, [0, 4]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [9, 6]⟩, ⟨.or, [8, 1]⟩,
   ⟨.or, [11, 3]⟩, ⟨.and, [12, 7]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [1, 5]⟩,
   ⟨.or, [10, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [16, 17]⟩]

lemma gmono_length : gmono.length = 11 := rfl

lemma gmono_legal : ∀ g ∈ gmono, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [gmono]

set_option maxHeartbeats 800000 in
lemma gmono_correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gmono, 18⟩ (List.ofFn x) = F x := by
  decide +kernel

def graphM : Fn := fun x => (x 0 && x 4) || (x 0 && x 6) || (x 4 && x 6)
def graphD : Fn := fun x => graphM x || (x 0 && x 7) || (x 4 && x 7)
def graphQ : Fn := fun x => graphD x || (x 3 && x 7)
def graphR : Fn := fun x => graphQ x || (x 2 && x 6)
def graphS (b : Bool) : Fn := fun x => graphR x || (x 1 && (x 7 || b))
def graphT (b : Bool) : Fn := if b then (fun x => graphM x || x 7) else graphD
def graphU (b : Bool) : Fn := if b then (fun x => x 0 || x 4) else (fun x => x 0 && x 4)

set_option maxHeartbeats 800000 in
lemma graphF_shape : F = (fun x => graphR x || (x 1 && (x 7 || x 5))) := by
  apply funext
  decide +kernel

lemma graph_fixF (b : Bool) : fix 5 b F = graphS b := by
  rw [graphF_shape]
  funext x
  simp [fix, graphS, graphR, graphQ, graphD, graphM]

lemma graph_fixS (b : Bool) : fix 1 false (graphS b) = graphR := by
  funext x
  simp [fix, graphS, graphR, graphQ, graphD, graphM]

lemma graph_fixR : fix 2 false graphR = graphQ := by
  funext x
  simp [fix, graphR, graphQ, graphD, graphM]

lemma graph_fixQ (b : Bool) : fix 3 b graphQ = graphT b := by
  funext x
  cases b <;> cases h : x 7 <;> simp [fix, graphQ, graphT, graphD, graphM, h]

lemma graph_fixT (b : Bool) : fix 7 false (graphT b) = graphM := by
  funext x
  cases b <;> simp [fix, graphT, graphD, graphM]

lemma graph_fixM (b : Bool) : fix 6 b graphM = graphU b := by
  funext x
  cases b <;> cases h : x 0 <;> simp [fix, graphM, graphU, h]

def graphRow (s : List (Fin 8)) : Fin 8 → Bool := fun i => s.contains i

lemma graph_neq {f g : Fn} (s : List (Fin 8)) (h : f (graphRow s) ≠ g (graphRow s)) :
    f ≠ g := fun he => h (congrFun he _)

lemma graph_dep {i : Fin 8} {f : Fn} (s : List (Fin 8))
    (h0 : fix i false f (graphRow s) = false) (h1 : fix i true f (graphRow s) = true) :
    fix i false f ≠ fix i true f := by
  apply graph_neq s
  rw [h0, h1]
  decide

lemma graph_nc {f : Fn} (h0 : f (graphRow []) = false) (h1 : f (graphRow [0, 4]) = true) :
    nonconst f := by
  constructor
  · apply graph_neq [0, 4]
    rw [h1]
    decide
  · apply graph_neq []
    rw [h0]
    decide

def graphI2 : Set (Fin 8) := insert 0 (insert 4 ∅)
def graphI3 : Set (Fin 8) := insert 6 graphI2
def graphI4 : Set (Fin 8) := insert 7 graphI3
def graphI5 : Set (Fin 8) := insert 3 graphI4
def graphI6 : Set (Fin 8) := insert 2 graphI5
def graphI7 : Set (Fin 8) := insert 1 graphI6

lemma graph_all : (Set.univ : Set (Fin 8)) = insert 5 graphI7 := by
  ext i
  fin_cases i <;> simp [graphI7, graphI6, graphI5, graphI4, graphI3, graphI2]

lemma graphU_min {b : Bool} {k : ℕ} (h : Run (graphU b) k (seed graphI2)) : 1 ≤ k := by
  cases k with
  | succ k => omega
  | zero =>
    cases h with
    | done ha =>
      exfalso
      have nc : nonconst (graphU b) := by
        cases b <;> exact graph_nc (by decide) (by decide)
      have notVar {i : Fin 8} (hi : i ∈ graphI2) : graphU b ≠ var i := by
        simp [graphI2] at hi
        rcases hi with rfl | rfl
        · cases b
          · exact graph_neq [0] (by decide)
          · exact graph_neq [4] (by decide)
        · cases b
          · exact graph_neq [4] (by decide)
          · exact graph_neq [0] (by decide)
      have notInvVar (i : Fin 8) : inv (graphU b) ≠ var i := by
        apply graph_neq []
        cases b <;> simp [graphRow, graphU, var, inv]
      rcases ha with hz | hu | ⟨i, hi, he⟩ | ⟨i, _, he⟩
      · exact nc.1 hz
      · exact nc.2 hu
      · exact notVar hi he.symm
      · exact notInvVar i he.symm

-- Savings along the restriction chain are 2, 1, 1, 2, 1 and 2; either
-- controlling value at each two-step cut leads to the same lower bound.
lemma lb {k : ℕ} (h : Run F k (seed Set.univ)) : 10 ≤ k := by
  rw [graph_all] at h
  obtain ⟨b5, k7, n5, h7⟩ := elim2 5 graphI7
    (by simp [graphI7, graphI6, graphI5, graphI4, graphI3, graphI2])
    (graph_dep [1] (by decide) (by decide))
    (by intro b; rw [graph_fixF]; cases b <;> exact graph_nc (by decide) (by decide)) h
  rw [graph_fixF] at h7
  obtain ⟨k6, n1, h6⟩ := elim1 1 false graphI6
    (by simp [graphI6, graphI5, graphI4, graphI3, graphI2])
    (by cases b5 <;> exact graph_dep [7] (by decide) (by decide))
    (by rw [graph_fixS]; exact graph_nc (by decide) (by decide)) h7
  rw [graph_fixS] at h6
  obtain ⟨k5, n2, h5⟩ := elim1 2 false graphI5
    (by simp [graphI5, graphI4, graphI3, graphI2])
    (graph_dep [6] (by decide) (by decide))
    (by rw [graph_fixR]; exact graph_nc (by decide) (by decide)) h6
  rw [graph_fixR] at h5
  obtain ⟨b3, k4, n3, h4⟩ := elim2 3 graphI4
    (by simp [graphI4, graphI3, graphI2])
    (graph_dep [7] (by decide) (by decide))
    (by intro b; rw [graph_fixQ]; cases b <;> exact graph_nc (by decide) (by decide)) h5
  rw [graph_fixQ] at h4
  obtain ⟨k3, n7, h3⟩ := elim1 7 false graphI3
    (by simp [graphI3, graphI2])
    (by cases b3 <;> exact graph_dep [0] (by decide) (by decide))
    (by rw [graph_fixT]; exact graph_nc (by decide) (by decide)) h4
  rw [graph_fixT] at h3
  obtain ⟨b6, k2, n6, h2⟩ := elim2 6 graphI2
    (by simp [graphI2])
    (graph_dep [0] (by decide) (by decide))
    (by intro b; rw [graph_fixM]; cases b <;> exact graph_nc (by decide) (by decide)) h3
  rw [graph_fixM] at h2
  have lowest := graphU_min h2
  omega

end PEqualNP.Outside.L_meta_14622

open PEqualNP.Outside.L_meta_14622 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_14622 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal _ eval
  change ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = F x at eval
  by_cases hn : ∃ g ∈ gs, g.op = .not
  · have run := compile gs o legal
    rw [funext eval] at run
    have lower := lb run
    have strict := counted_lt gs hn
    exact ⟨gmono, 18, gmono_legal, by rw [gmono_length]; omega, gmono_correct⟩
  · refine ⟨gs, o, ?_, le_rfl, eval⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := legal g hg
    exact ⟨hop.imp_right (fun h => h.resolve_right (fun e => hn ⟨g, hg, e⟩)), hlen⟩
