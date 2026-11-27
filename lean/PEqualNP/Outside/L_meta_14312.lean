import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_14312
open PEqualNP.CircuitLowerBounds
abbrev Row := Fin 256
abbrev Wire := Row → Bool
def bin (d a b : Nat) : Nat :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def flipOp (d : Nat) : Nat :=
  match d with
  | 2 => 3
  | 3 => 2
  | _ => d
lemma bin_comm_flip (d : Nat) (hd : d < 4) (a b : Nat) : bin d a b = bin (flipOp d) b a := by
  interval_cases d <;> simp [bin, flipOp, Nat.and_comm, Nat.or_comm]
lemma flipOp_lt {d : Nat} (hd : d < 4) : flipOp d < 4 := by
  interval_cases d <;> decide
lemma testBit_bin (d a b r : Nat) :
    (bin d a b).testBit r =
      match d with
      | 0 => a.testBit r && b.testBit r
      | 1 => a.testBit r || b.testBit r
      | 2 => a.testBit r && !b.testBit r
      | _ => !a.testBit r && b.testBit r := by
  rcases d with _ | _ | _ | d <;>
    simp [bin, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit r <;> cases b.testBit r <;> rfl
lemma bin_lt (d a b : Nat) (ha : a < 2^256) (hb : b < 2^256) : bin d a b < 2^256 := by
  have h1 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x &&& y) < 2^256 := fun x y hx _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left hx
  have h2 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x ||| y) < 2^256 := fun x y hx hy =>
    Nat.or_lt_two_pow hx hy
  have h3 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x ^^^ y) < 2^256 := fun x y hx hy =>
    Nat.xor_lt_two_pow hx hy
  rcases d with _ | _ | _ | d
  · exact h1 a b ha hb
  · exact h2 a b ha hb
  · exact h3 a (a &&& b) ha (h1 a b ha hb)
  · exact h3 b (a &&& b) hb (h1 a b ha hb)
lemma bin_bit0 (d a b : Nat) (ha : a.testBit 0 = false) (hb : b.testBit 0 = false) :
    (bin d a b).testBit 0 = false := by
  rw [testBit_bin]
  rcases d with _ | _ | _ | d <;> simp [ha, hb]
def Live (T : Nat) : Nat → Finset Nat → Prop
  | 0, S => S = {T} ∧ T ≠ 0
  | k + 1, S => ∃ (U : Finset Nat) (a b d : Nat),
      d < 4 ∧ S = insert a (insert b U) ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live T k (insert (bin d a b) U)
lemma live_nonzero {T k S} (h : Live T k S) : ∀ a ∈ S, a ≠ 0 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, hT⟩ := h; simpa using hT
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, ha, hb, _, _, tail⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
lemma live_size {T k S} (h : Live T k S) : S.card ≤ k + 1 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; simp
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, hf, tail⟩ := h
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have ht := ih tail
    rw [Finset.card_insert_of_notMem hu] at ht
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    omega
lemma live_sep {T k S} (h : Live T k S) {r s : Nat} (hd : T.testBit r ≠ T.testBit s) :
    ∃ a ∈ S, a.testBit r ≠ a.testBit s := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; exact ⟨T, by simp, hd⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, _, tail⟩ := h
    obtain ⟨v, hv, hvd⟩ := ih tail
    rcases Finset.mem_insert.mp hv with rfl | hv
    · by_cases ha : a.testBit r = a.testBit s
      · refine ⟨b, by simp, fun hb => hvd ?_⟩
        rw [testBit_bin, testBit_bin, ha, hb]
      · exact ⟨a, by simp, ha⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv), hvd⟩
abbrev SWire := Bool × Nat
def swZero : SWire := (false, 0)
def swFlip (a : SWire) : SWire := (!a.1, a.2)
def opIdx (s t : Bool) : Nat := if s then (if t then 1 else 3) else (if t then 2 else 0)
def swMeet (a b : SWire) : SWire := (a.1 && b.1, bin (opIdx a.1 b.1) a.2 b.2)
def swJoin (a b : SWire) : SWire := swFlip (swMeet (swFlip a) (swFlip b))
def swRead (j : Nat) (a : SWire) : Bool := a.1 != a.2.testBit j
lemma swRead_zero (j : Nat) : swRead j swZero = false := by simp [swRead, swZero]
lemma swRead_flip (j : Nat) (a : SWire) : swRead j (swFlip a) = !(swRead j a) := by
  cases a with | mk s v => cases s <;> cases h : v.testBit j <;> simp [swRead, swFlip, h]
lemma swRead_meet (j : Nat) (a b : SWire) : swRead j (swMeet a b) = (swRead j a && swRead j b) := by
  obtain ⟨s, u⟩ := a; obtain ⟨t, v⟩ := b
  cases s <;> cases t <;> cases hu : u.testBit j <;> cases hv : v.testBit j <;>
    simp [swRead, swMeet, opIdx, testBit_bin, hu, hv]
lemma swRead_join (j : Nat) (a b : SWire) : swRead j (swJoin a b) = (swRead j a || swRead j b) := by
  simp only [swJoin, swRead_flip, swRead_meet]
  cases swRead j a <;> cases swRead j b <;> rfl
def swGate (w : List SWire) (g : Gate) : SWire :=
  let arg := fun i => w.getD i swZero
  match g.op, g.inputs with
  | .not, xs => swFlip (arg (xs.headD w.length))
  | .and, [] => swFlip swZero
  | .or, [] => swZero
  | .and, [i] | .or, [i] => arg i
  | .and, i :: j :: _ => swMeet (arg i) (arg j)
  | .or, i :: j :: _ => swJoin (arg i) (arg j)
  | _, _ => swZero
def swExec (gs : List Gate) (w : List SWire) : List SWire :=
  gs.foldl (fun w g => w ++ [swGate w g]) w
def isBin (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List SWire) : List Nat := w.map Prod.snd
def simple (w : List SWire) (z : Nat) : Prop := z = 0 ∨ z ∈ reps w
def priced (w : List SWire) (paid : Bool) (z : Nat) : Prop :=
  simple w z ∨ (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ z = bin d a b)
lemma bin_eq_cases (d a b : Nat) (hd : d < 4) (h : a = 0 ∨ b = 0 ∨ a = b) :
    bin d a b = 0 ∨ bin d a b = a ∨ bin d a b = b := by
  rcases h with rfl | rfl | rfl <;> interval_cases d <;> simp [bin]
lemma opIdx_lt (s t : Bool) : opIdx s t < 4 := by cases s <;> cases t <;> decide
lemma get_simple (w : List SWire) (i : Nat) : simple w (w.getD i swZero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a, List.mem_of_getElem? eq, rfl⟩)
lemma made_priced (w : List SWire) (d : Nat) (a b : SWire) (hd : d < 4)
    (pa : simple w a.2) (pb : simple w b.2) : priced w true (bin d a.2 b.2) := by
  by_cases h : a.2 = 0 ∨ b.2 = 0 ∨ a.2 = b.2
  · rcases bin_eq_cases d a.2 b.2 hd h with e | e | e
    · exact Or.inl (Or.inl e)
    · rw [e]; exact Or.inl pa
    · rw [e]; exact Or.inl pb
  · push Not at h
    exact Or.inr ⟨rfl, d, hd, a.2, pa.resolve_left h.1, b.2, pb.resolve_left h.2.1, h.1, h.2.1, h.2.2, rfl⟩
lemma swGate_priced (w : List SWire) (g : Gate) : priced w (isBin g) (swGate w g).2 := by
  obtain ⟨op, xs⟩ := g
  cases op with
  | and =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made_priced w _ _ _ (opIdx_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made_priced w _ _ _ (opIdx_lt _ _) (get_simple w i) (get_simple w j)
  | not => exact Or.inl (get_simple w _)
  | _ => exact Or.inl (Or.inl rfl)
lemma swGate_lt (w : List SWire) (hw : ∀ u ∈ w, u.2 < 2^256 ∧ u.2.testBit 0 = false) (g : Gate) :
    (swGate w g).2 < 2^256 ∧ (swGate w g).2.testBit 0 = false := by
  have hz : (0 : Nat) < 2^256 ∧ (0 : Nat).testBit 0 = false := ⟨by decide, by decide⟩
  have hg (i : Nat) : (w.getD i swZero).2 < 2^256 ∧ (w.getD i swZero).2.testBit 0 = false := by
    simp only [List.getD_eq_getElem?_getD]
    cases eq : w[i]? with
    | none => exact hz
    | some a => exact hw a (List.mem_of_getElem? eq)
  obtain ⟨op, xs⟩ := g
  cases op with
  | and =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact hz
    · exact hg i
    · exact ⟨bin_lt _ _ _ (hg i).1 (hg j).1, bin_bit0 _ _ _ (hg i).2 (hg j).2⟩
  | or =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact hz
    · exact hg i
    · exact ⟨bin_lt _ _ _ (hg i).1 (hg j).1, bin_bit0 _ _ _ (hg i).2 (hg j).2⟩
  | not => exact hg (xs.headD w.length)
  | _ => exact hz
lemma swExec_lt (gs : List Gate) (w : List SWire)
    (hw : ∀ u ∈ w, u.2 < 2^256 ∧ u.2.testBit 0 = false) :
    ∀ u ∈ swExec gs w, u.2 < 2^256 ∧ u.2.testBit 0 = false := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hw u hu
    · rw [List.mem_singleton.mp hu]; exact swGate_lt w hw g
lemma swRead_get (j : Nat) (w : List SWire) (i : Nat) :
    (w.map (swRead j)).getD i false = swRead j (w.getD i swZero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp [swRead_zero]
lemma swGate_read (w : List SWire) (g : Gate)
    (legal : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) (j : Nat) :
    swRead j (swGate w g) = g.op.eval (g.inputs.map fun i => (w.map (swRead j)).getD i false) := by
  simp_rw [swRead_get]
  obtain ⟨op, xs⟩ := g
  obtain ⟨hop, hlen⟩ := legal
  rcases hop with rfl | rfl | rfl <;>
    rcases xs with _ | ⟨i, _ | ⟨k, _ | ⟨h, rest⟩⟩⟩ <;>
    simp_all [swGate, GateOp.eval, swRead_flip, swRead_meet, swRead_join, swRead_zero]
lemma swExec_read (j : Nat) (gs : List Gate) (w : List SWire)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    (swExec gs w).map (swRead j) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (swRead j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (swExec gs (w ++ [swGate w g])).map (swRead j) = _
    rw [ih _ (fun v hv => legal v (List.mem_cons_of_mem _ hv))]
    simp [swGate_read w g (legal g List.mem_cons_self) j]
lemma pull_live {T k S w z p} (h : Live T k S) (op : priced w p z)
    (sub : ∀ a ∈ S, a ∈ reps w ++ [z]) :
    ∃ l V, l ≤ k + p.toNat ∧ Live T l V ∧ ∀ a ∈ V, a ∈ reps w := by
  by_cases needed : z ∈ S
  · by_cases avail : z ∈ reps w
    · refine ⟨k, S, by omega, h, fun a ha => ?_⟩
      rcases (by simpa using sub a ha : a ∈ reps w ∨ a = z) with old | rfl
      · exact old
      · exact avail
    · rcases op with easy | ⟨rfl, d, hd, a, ha, b, hb, na, nb, ab, rfl⟩
      · rcases easy with rfl | hm
        · exact (live_nonzero h 0 needed rfl).elim
        · exact (avail hm).elim
      · let U := S.erase (bin d a b)
        have tail : Live T k (insert (bin d a b) U) := by
          simpa [U, Finset.insert_erase needed] using h
        have old (x : Nat) (hx : x ∈ U) : x ∈ reps w := by
          obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hx
          exact (by simpa using sub x mem : x ∈ reps w ∨ x = bin d a b).resolve_right ne
        have fresh : bin d a b ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e | h'
          · exact avail (e.symm ▸ ha)
          rcases Finset.mem_insert.mp h' with e | u
          · exact avail (e.symm ▸ hb)
          · exact avail (old _ u)
        exact ⟨k + 1, insert a (insert b U), by simp,
          ⟨U, a, b, d, hd, rfl, na, nb, ab, fresh, tail⟩, by simpa using And.intro ha (And.intro hb old)⟩
  · exact ⟨k, S, by omega, h, fun a ha => (by simpa [show a ≠ z from fun e => needed (e ▸ ha)] using sub a ha)⟩
lemma extract_live {T} (hT : T ≠ 0) (gs : List Gate) (w : List SWire)
    (found : T ∈ reps (swExec gs w)) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ reps w := by
  induction gs generalizing w with
  | nil => exact ⟨0, {T}, by simp, ⟨rfl, hT⟩, by simpa [swExec] using found⟩
  | cons g gs ih =>
    obtain ⟨k, S, lim, h, sub⟩ := ih (w ++ [swGate w g]) found
    have sub' : ∀ a ∈ S, a ∈ reps w ++ [(swGate w g).2] := by simpa [reps] using sub
    obtain ⟨l, V, cost, hl, raw⟩ := pull_live h (swGate_priced w g) sub'
    refine ⟨l, V, ?_, hl, raw⟩
    rw [List.countP_cons]
    cases e : isBin g <;> simp [e] at cost ⊢ <;> omega
def invW (a : Wire) : Wire := fun r => !(a r)
def comb2 (isOr : Bool) (a b : Wire) : Wire :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb4 (d : Nat) (a b : Wire) : Wire :=
  match d with
  | 0 => comb2 false a b
  | 1 => comb2 true a b
  | 2 => comb2 false a (invW b)
  | _ => comb2 false (invW a) b
def Constant (a : Wire) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def wcost (a : Wire) : Nat := by classical exact if Constant a then 1 else 0
noncomputable def wmass (xs : List Wire) : Nat := (xs.map wcost).sum
def Avail (pool : List Wire) (v : Wire) : Prop := v ∈ pool ∨ Constant v ∨ invW v ∈ pool
def Supply (pool xs : List Wire) : Prop := ∀ a ∈ xs, Avail pool a
def Reach (roots : List Wire) : Nat → List Wire → Prop
  | 0, b => b = roots
  | p + 1, c => ∃ (op : Bool) (bank : List Wire) (a b : Wire),
      Reach roots p bank ∧ Avail bank a ∧ Avail bank b ∧ c = comb2 op a b :: bank
def kept {α : Type} (save : Bool) (x : α) (xs : List α) : List α := if save then x :: xs else xs
def Run (goal : Wire) : Nat → List Wire → Prop
  | 0, zs => List.Perm [goal] zs
  | s + 1, zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire) (rest : List Wire),
      op < 4 ∧ (a :: b :: rest).Perm zs ∧ Run goal s (comb4 op a b :: kept ka a (kept kb b rest))
lemma invW_inv (a : Wire) : invW (invW a) = a := by funext r; simp [invW]
lemma invW_const {a : Wire} (h : Constant a) : Constant (invW a) := by
  obtain ⟨v, rfl⟩ := h; exact ⟨!v, rfl⟩
lemma wcost_inv (a : Wire) : wcost (invW a) = wcost a := by
  have h : Constant (invW a) ↔ Constant a := ⟨fun hc => invW_inv a ▸ invW_const hc, invW_const⟩
  by_cases hc : Constant a
  · simp [wcost, hc, h.mpr hc]
  · simp [wcost, hc, mt h.mp hc]
lemma avail_inv {bank : List Wire} {a : Wire} (h : Avail bank a) : Avail bank (invW a) := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr (by rwa [invW_inv]))
  · exact Or.inr (Or.inl (invW_const h))
  · exact Or.inl h
lemma avail_cons {bank : List Wire} {v : Wire} (w : Wire) (h : Avail bank v) : Avail (w :: bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (List.mem_cons_of_mem _))
lemma from_const (op : Bool) {a b : Wire} {bank : List Wire} (h : Constant a ∨ Constant b)
    (ha : Avail bank a) (hb : Avail bank b) : Avail bank (comb2 op a b) := by
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> cases op <;> cases v
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using hb
  · simpa [comb2] using hb
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using ha
  · simpa [comb2] using ha
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
lemma both_const (op : Bool) {a b : Wire} (ha : Constant a) (hb : Constant b) :
    Constant (comb2 op a b) := by
  obtain ⟨v, rfl⟩ := ha; obtain ⟨w, rfl⟩ := hb; cases op <;> exact ⟨_, rfl⟩
lemma extend_comb (roots : List Wire) {p bank a b} (d : Nat) (hd : d < 4)
    (hp : Reach roots p bank) (ha : Avail bank a) (hb : Avail bank b) :
    ∃ q next, Reach roots q next ∧ Avail next (comb4 d a b) ∧
      (∀ v, Avail bank v → Avail next v) ∧ q + wcost a + wcost b ≤ p + 1 + wcost (comb4 d a b) := by
  have hprep : ∃ op x y, comb4 d a b = comb2 op x y ∧ Avail bank x ∧ Avail bank y ∧
      wcost x = wcost a ∧ wcost y = wcost b := by
    interval_cases d
    · exact ⟨false, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨true, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨false, a, invW b, rfl, ha, avail_inv hb, rfl, wcost_inv b⟩
    · exact ⟨false, invW a, b, rfl, avail_inv ha, hb, wcost_inv a, rfl⟩
  obtain ⟨op, x, y, eq, hx, hy, cx, cy⟩ := hprep
  rw [eq, ← cx, ← cy]
  classical
  by_cases c : Constant x ∨ Constant y
  · refine ⟨p, bank, hp, from_const op c hx hy, fun _ h => h, ?_⟩
    by_cases hcx : Constant x <;> by_cases hcy : Constant y
    · simp [wcost, hcx, hcy, both_const op hcx hcy]
    · simp [wcost, hcx, hcy]
    · simp [wcost, hcx, hcy]
    · exact (c.elim hcx hcy).elim
  · have hcx : ¬Constant x := fun h => c (Or.inl h)
    have hcy : ¬Constant y := fun h => c (Or.inr h)
    exact ⟨p + 1, _, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, Or.inl (by simp),
      fun _ h => avail_cons _ h, by simp [wcost, hcx, hcy]⟩
lemma wmass_kept (a : Wire) (xs : List Wire) (k : Bool) : wmass xs ≤ wmass (kept k a xs) := by
  cases k <;> simp [kept, wmass]
lemma contraction {goal : Wire} (nc : ¬Constant goal) {s ws} (h : Run goal s ws)
    (roots : List Wire) {p bank} (hp : Reach roots p bank) (hs : Supply bank ws) :
    ∃ q next, Reach roots q next ∧ Avail next goal ∧ q + wmass ws ≤ p + s := by
  classical
  induction s generalizing ws p bank with
  | zero =>
    have hmem : goal ∈ ws := h.mem_iff.mp (by simp)
    have hlen : wmass ws = wcost goal := by
      have := (h.map wcost).sum_eq
      simpa [wmass] using this.symm
    exact ⟨p, bank, hp, hs goal hmem, by simp [hlen, wcost, nc]⟩
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have hsa : Avail bank a := hs a (perm.mem_iff.mp (by simp))
    have hsb : Avail bank b := hs b (perm.mem_iff.mp (by simp))
    obtain ⟨r, T, hT, hz, inc, le⟩ := extend_comb roots op hd hp hsa hsb
    have ht : Supply T (comb4 op a b :: kept ka a (kept kb b rest)) := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hz
      · apply inc; apply hs; apply perm.mem_iff.mp
        cases ka <;> cases kb <;> simp [kept] at hv ⊢ <;> tauto
    obtain ⟨q, W, hW, hv, hl⟩ := ih tail hT ht
    have hm1 := wmass_kept a (kept kb b rest) ka
    have hm2 := wmass_kept b rest kb
    have hp_eq : wmass ws = wcost a + wcost b + wmass rest := by
      have := (perm.map wcost).sum_eq
      simpa [wmass, Nat.add_assoc] using this.symm
    have hcons : wmass (comb4 op a b :: kept ka a (kept kb b rest)) =
        wcost (comb4 op a b) + wmass (kept ka a (kept kb b rest)) := rfl
    rw [hcons] at hl
    exact ⟨q, W, hW, hv, by omega⟩
def restrictW (f : Row → Row) (a : Wire) : Wire := fun r => a (f r)
lemma restrict_run (f : Row → Row) {goal s ws} (h : Run goal s ws) :
    Run (restrictW f goal) s (ws.map (restrictW f)) := by
  induction s generalizing ws with
  | zero => exact h.map _
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have htail := ih tail
    have hk : ∀ (k : Bool) (x : Wire) (l : List Wire),
        (kept k x l).map (restrictW f) = kept k (restrictW f x) (l.map (restrictW f)) := by
      intro k x l; cases k <;> rfl
    have hc : restrictW f (comb4 op a b) = comb4 op (restrictW f a) (restrictW f b) := by
      funext r; rcases op with _ | _ | _ | op <;> rfl
    simp only [List.map_cons, hk, hc] at htail
    exact ⟨op, ka, kb, restrictW f a, restrictW f b, rest.map (restrictW f), hd,
      by simpa using perm.map (restrictW f), htail⟩
def obs (a : Nat) : Wire := fun r => a.testBit r.val
lemma obs_bin (d a b : Nat) : obs (bin d a b) = comb4 d (obs a) (obs b) := by
  funext r
  simp only [obs, testBit_bin, comb4, comb2, invW]
  rcases d with _ | _ | _ | d <;> rfl
lemma kept_nodup {α : Type} (c : Bool) (x : α) (l : List α) (hl : l.Nodup) (hx : x ∉ l) :
    (kept c x l).Nodup := by
  cases c <;> simp [kept, hl, hx]
lemma live_to_run {T k S} (h : Live T k S) (v : List Nat) (nd : v.Nodup) (eqv : v.toFinset = S) :
    Run (obs T) k (v.map obs) := by
  classical
  induction k generalizing S v with
  | zero =>
    obtain ⟨rfl, _⟩ := h
    have hp : [T].Perm v := List.perm_of_nodup_nodup_toFinset_eq (by simp) nd (by simp [eqv])
    exact hp.map obs
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, _, _, hab, fresh, tail⟩ := h
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tl := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm : mid.Nodup := kept_nodup kb b rest hr br
    have am : a ∉ mid := by cases hkb : kb <;> simp [mid, kept, hkb, hab, ar]
    have ntl : tl.Nodup := kept_nodup ka a mid bm am
    have htl : tl.toFinset = U := by
      have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
        cases c <;> simp [kept]
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kf, kf, er]
      ext j
      by_cases ha' : a ∈ U <;> by_cases hb' : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;>
        simp_all [ka, kb]
    have hf : bin d a b ∉ tl := fun hm =>
      fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (htl ▸ List.mem_toFinset.mpr hm)))
    have prog := ih tail (bin d a b :: tl) (List.nodup_cons.mpr ⟨hf, ntl⟩) (by simp [htl])
    have hk : ∀ (c : Bool) (x : Nat) (l : List Nat), (kept c x l).map obs = kept c (obs x) (l.map obs) := by
      intro c x l; cases c <;> rfl
    change Run (obs T) k ((bin d a b :: kept ka a (kept kb b rest)).map obs) at prog
    rw [List.map_cons, hk, hk, obs_bin] at prog
    have perm : (a :: b :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) nd
      ext j
      by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all
    exact ⟨d, ka, kb, obs a, obs b, rest.map obs, hd, by simpa using perm.map obs, prog⟩
def normPack (f : Wire) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).toNat
lemma normPack_lt (f : Wire) : normPack f < 2^256 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).isLt
lemma testBit_normPack (f : Wire) (r : Nat) :
    (normPack f).testBit r = if h : r < 256 then (f ⟨r, h⟩ != f 0) else false := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).getLsbD r = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : r < 256 <;> simp [h]
lemma normPack_eq_of_obs {a : Nat} (ha : a < 2^256) (h0 : a.testBit 0 = false) :
    normPack (obs a) = a := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 256
  · simp [hr, obs, h0]
  · simp only [hr, dite_false]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma normPack_inv (f : Wire) : normPack (invW f) = normPack f := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_normPack]
  by_cases hr : r < 256
  · simp only [hr, dite_true, invW]
    cases f ⟨r, hr⟩ <;> cases f 0 <;> rfl
  · simp [hr]
lemma normPack_const {f : Wire} (h : Constant f) : normPack f = 0 := by
  obtain ⟨b, rfl⟩ := h
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 256 <;> simp [hr]
lemma normPack_comb2 (op : Bool) (a b : Wire) :
    ∃ d < 4, normPack (comb2 op a b) = bin d (normPack a) (normPack b) := by
  refine ⟨opIdx (if op then !(a 0) else a 0) (if op then !(b 0) else b 0), opIdx_lt _ _, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_bin, testBit_normPack, testBit_normPack]
  by_cases hr : r < 256
  · simp only [hr, dite_true]
    cases op <;> cases ha0 : a 0 <;> cases hb0 : b 0 <;>
      cases har : a ⟨r, hr⟩ <;> cases hbr : b ⟨r, hr⟩ <;>
      simp [comb2, opIdx, ha0, hb0, har, hbr]
  · simp only [hr, dite_false]
    rcases opIdx _ _ with _ | _ | _ | d <;> rfl
lemma avail_normPack {bank : List Wire} {v : Wire} (h : Avail bank v) :
    normPack v = 0 ∨ normPack v ∈ bank.map normPack := by
  rcases h with hm | hc | hi
  · exact Or.inr (List.mem_map_of_mem hm)
  · exact Or.inl (normPack_const hc)
  · exact Or.inr (by rw [← normPack_inv v]; exact List.mem_map_of_mem hi)
lemma reach_to_live_sub {roots : List Wire} {p bank} (h : Reach roots p bank)
    {T k S} (run : Live T k S) (sub : ∀ a ∈ S, a ∈ bank.map normPack) :
    ∃ l V, l ≤ p + k ∧ Live T l V ∧ ∀ a ∈ V, a ∈ roots.map normPack := by
  induction p generalizing bank k S with
  | zero =>
    rcases h with rfl
    exact ⟨k, S, by omega, run, sub⟩
  | succ p ih =>
    obtain ⟨op, prev, a, b, hr, ha, hb, rfl⟩ := h
    obtain ⟨d, hd, eq⟩ := normPack_comb2 op a b
    let w := prev.map (fun f => (false, normPack f))
    have hreps : reps w = prev.map normPack := by simp [w, reps, List.map_map, Function.comp_def]
    have hp : priced w true (normPack (comb2 op a b)) := by
      rw [eq]
      have ha' : simple w (normPack a) := by simpa [simple, hreps] using avail_normPack ha
      have hb' : simple w (normPack b) := by simpa [simple, hreps] using avail_normPack hb
      generalize normPack a = na at ha' ⊢
      generalize normPack b = nb at hb' ⊢
      exact made_priced w d (false, na) (false, nb) hd ha' hb'
    have hsub' : ∀ x ∈ S, x ∈ reps w ++ [normPack (comb2 op a b)] := by
      intro x hx
      rcases List.mem_cons.mp (sub x hx) with rfl | hm
      · simp
      · simp [hreps, hm]
    obtain ⟨k', S', hk', run', sub'⟩ := pull_live run hp hsub'
    obtain ⟨l, V, hl, run'', sub''⟩ := ih hr run' (by simpa [hreps] using sub')
    simp only [Bool.toNat_true] at hk'
    exact ⟨l, V, by omega, run'', sub''⟩
def Lower (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map obs) p bank → Avail bank (obs T) → L ≤ p
def Impossible (T : Nat) (cap : Nat) (S : Finset Nat) : Prop :=
  ∀ k ≤ cap, ¬Live T k S
def Essential (T : Nat) (roots : List Nat) (a : Nat) : Prop :=
  ∃ r s : Row, T.testBit r.val ≠ T.testBit s.val ∧ ∀ v ∈ roots, v ≠ a → v.testBit r.val = v.testBit s.val
lemma raw_required {T k S} (h : Live T k S) (roots : List Nat) (a : Nat)
    (sub : ∀ v ∈ S, v ∈ roots) (he : Essential T roots a) : a ∈ S := by
  obtain ⟨r, s, hd, hiso⟩ := he
  obtain ⟨v, hv, hvd⟩ := live_sep h hd
  by_cases veq : v = a
  · exact veq ▸ hv
  · exact (hvd (hiso v (sub v hv) veq)).elim
lemma lower_of_impossible {roots : List Nat} {T L : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
    (ess : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L + 1) := by
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hnz : normPack (obs T) ≠ 0 := by rwa [hnormT]
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left hnz
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id roots]
    apply List.map_congr_left
    intro a ha'
    exact normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have heq : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    exact ⟨fun ha' => raw_required run roots a sub (ess a ha'), sub a⟩
  by_contra! small
  exact noRun k (by omega) (heq.symm ▸ run)
lemma obs_not_const {T : Nat} (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false) :
    ¬Constant (obs T) := by
  intro hc
  have h := normPack_const hc
  rw [normPack_eq_of_obs hTlt hTb0] at h
  exact hT0 h
def Slice (raw : List Nat) (T d : Nat) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Nat),
    (∀ r : Row, d.testBit (f r).val = true) ∧
    (∀ a ∈ raw, Avail (roots.map obs) (restrictW f (obs a))) ∧
    ¬Constant (restrictW f (obs T)) ∧
    ∀ p bank, Reach (roots.map obs) p bank → Avail bank (restrictW f (obs T)) → L ≤ p
def isConstM (d a : Nat) : Bool := (a &&& d == 0) || (a &&& d == d)
def availM (d : Nat) (pm : List Nat) (a : Nat) : Bool :=
  let m := a &&& d
  m == 0 || m == d || pm.contains m || pm.contains (d ^^^ m)
lemma masked_eq_obs {f : Row → Row} {d a b : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = (b &&& d)) : restrictW f (obs a) = restrictW f (obs b) := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_zero_obs {f : Row → Row} {d a : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = 0) : restrictW f (obs a) = fun _ => false := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_one_obs {f : Row → Row} {d a : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = d) : restrictW f (obs a) = fun _ => true := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_comp_obs {f : Row → Row} {d a b : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = (d ^^^ (b &&& d))) : restrictW f (obs a) = invW (restrictW f (obs b)) := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simp only [Nat.testBit_and, Nat.testBit_xor, dom r, Bool.and_true] at h
  simp only [restrictW, obs, invW, h]
  cases b.testBit (f r).val <;> rfl
def poolSupply (f : Row → Row) (bank : List Wire) (pool : List Nat) : Prop :=
  ∀ a ∈ pool, Avail bank (restrictW f (obs a))
lemma availM_sound {f : Row → Row} {d a : Nat} {bank : List Wire} {pool : List Nat}
    (dom : ∀ r : Row, d.testBit (f r).val = true)
    (hs : poolSupply f bank pool)
    (ok : availM d (pool.map (· &&& d)) a = true) :
    Avail bank (restrictW f (obs a)) := by
  simp only [availM, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq, List.mem_map] at ok
  rcases ok with ((h0 | h1) | ⟨v, hv, he⟩) | ⟨v, hv, he⟩
  · exact Or.inr (Or.inl ⟨false, masked_zero_obs dom h0⟩)
  · exact Or.inr (Or.inl ⟨true, masked_one_obs dom h1⟩)
  · exact (masked_eq_obs dom he.symm) ▸ hs v hv
  · have hinv := avail_inv (hs v hv)
    have hcomp : restrictW f (obs a) = invW (restrictW f (obs v)) := by
      have hx : (a &&& d) = d ^^^ (v &&& d) := by
        have := congrArg (d ^^^ ·) he
        simpa [Nat.xor_assoc, Nat.xor_comm, Nat.xor_self] using this.symm
      exact masked_comp_obs dom hx
    exact hcomp ▸ hinv
abbrev Choice := Nat × Nat × Nat
def choiceVal (c : Choice) : Nat := bin c.1 c.2.1 c.2.2
def choiceOK (d : Nat) (pm : List Nat) (c : Choice) : Bool :=
  decide (c.1 < 4) && availM d pm c.2.1 && availM d pm c.2.2
def makePool (d : Nat) (pool : List Nat) : List Choice → Option (List Nat)
  | [] => some pool
  | c :: cs => if choiceOK d (pool.map (· &&& d)) c then makePool d (choiceVal c :: pool) cs else none
lemma pay_choice {f : Row → Row} {d : Nat} {roots bank q} {pool : List Nat}
    (dom : ∀ r : Row, d.testBit (f r).val = true)
    (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d (pool.map (· &&& d)) c = true) :
    ∃ next, Reach roots (q + 1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  simp only [choiceOK, Bool.and_eq_true, decide_eq_true_eq] at valid
  have ha := availM_sound dom hs valid.1.2
  have hb := availM_sound dom hs valid.2
  have hprep : ∃ op x y, comb4 c.1 (restrictW f (obs c.2.1)) (restrictW f (obs c.2.2)) = comb2 op x y ∧
      Avail bank x ∧ Avail bank y := by
    have hd := valid.1.1
    interval_cases c.1
    · exact ⟨false, _, _, rfl, ha, hb⟩
    · exact ⟨true, _, _, rfl, ha, hb⟩
    · exact ⟨false, _, _, rfl, ha, avail_inv hb⟩
    · exact ⟨false, _, _, rfl, avail_inv ha, hb⟩
  obtain ⟨op, x, y, eq, hx, hy⟩ := hprep
  refine ⟨comb2 op x y :: bank, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, fun v hv => ?_⟩
  rcases List.mem_cons.mp hv with rfl | hv
  · have hcv : restrictW f (obs (choiceVal c)) = comb2 op x y := by
      rw [← eq]; funext r; simp only [choiceVal, restrictW, obs, testBit_bin, comb4, comb2, invW]
      rcases c.1 with _ | _ | _ | d' <;> rfl
    exact hcv ▸ Or.inl (by simp)
  · exact avail_cons _ (hs v hv)
lemma makePool_sound {d : Nat} {f : Row → Row} (dom : ∀ r : Row, d.testBit (f r).val = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {res} (ok : makePool d pool cs = some res) :
    ∃ next, Reach roots (q + cs.length) next ∧ poolSupply f next res := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨bank, hp, hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next, hr, sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out, hr', sh'⟩ := ih hr sh ok
      exact ⟨out, by simpa [Nat.add_assoc, Nat.add_comm 1] using hr', sh'⟩
    next => contradiction
lemma count_constM {d : Nat} {f : Row → Row} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (ws : List Nat) : ws.countP (isConstM d) ≤ wmass ((ws.map obs).map (restrictW f)) := by
  classical
  induction ws with
  | nil => simp [wmass]
  | cons a ws ih =>
    simp only [List.countP_cons, List.map_cons, wmass, List.sum_cons] at ih ⊢
    cases h : isConstM d a
    · simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
      exact ih.trans (Nat.le_add_left _ _)
    · have hc : Constant (restrictW f (obs a)) := by
        simp only [isConstM, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with h0 | h1
        · exact ⟨false, masked_zero_obs dom h0⟩
        · exact ⟨true, masked_one_obs dom h1⟩
      simp only [ite_true, wcost, hc]
      omega
structure BoundPool where
  dom : Nat
  lb : Nat
  paid : Nat
  wires : List Nat
  pm : List Nat
def ValidPool (_raw : List Nat) (T : Nat) (c : BoundPool) : Prop :=
  c.pm = c.wires.map (· &&& c.dom) ∧
  ∃ (f : Row → Row) (roots : List Nat) (bank : List Wire),
    (∀ r : Row, c.dom.testBit (f r).val = true) ∧ ¬Constant (restrictW f (obs T)) ∧
    (∀ q ws, Reach (roots.map obs) q ws → Avail ws (restrictW f (obs T)) → c.lb ≤ q) ∧
    Reach (roots.map obs) c.paid bank ∧ poolSupply f bank c.wires
def materialize (raw : List Nat) (cs : List Choice) (d lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map fun pool => ⟨d, lb, cs.length, pool, pool.map (· &&& d)⟩
lemma materialize_sound {raw T d L cs c} (sl : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst c
    obtain ⟨f, roots, dom, base, nc, lo⟩ := sl
    obtain ⟨bank, hr, hs⟩ := makePool_sound dom (show Reach (roots.map obs) 0 (roots.map obs) from rfl) base cs he
    exact ⟨rfl, f, roots, bank, dom, nc, lo, by simpa using hr, hs⟩
def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let z := choiceVal op
  let extra := !(availM c.dom c.pm z)
  decide (k + c.paid + extra.toNat < c.lb + (z :: rest).countP (isConstM c.dom)) &&
    rest.all (availM c.dom c.pm) && (!extra || choiceOK c.dom c.pm op)
lemma scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op :: rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  obtain ⟨hpm, f, roots, bank, dom, nc, lo, hp, hs⟩ := valid
  simp only [scalarPoolCut, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at cut
  intro t ht run
  have finish (n : Nat) (out : List Wire) (hr : Reach (roots.map obs) n out)
      (hsup : poolSupply f out (choiceVal op :: rest))
      (hle : n = c.paid + (!(availM c.dom c.pm (choiceVal op))).toNat) : False := by
    have hcov : Supply out (((choiceVal op :: rest).map obs).map (restrictW f)) := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
      exact hsup a ha
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction nc (restrict_run f (live_to_run run (choiceVal op :: rest) nd rfl)) (roots.map obs) hr hcov
    have hlo := lo q next hq hav
    have hcm := count_constM dom (choiceVal op :: rest)
    have hineq := cut.1.1
    omega
  cases hav : availM c.dom c.pm (choiceVal op) with
  | true =>
    apply finish c.paid bank hp _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact availM_sound dom hs (hpm ▸ hav)
    · exact availM_sound dom hs (hpm ▸ cut.1.2 a ha)
  | false =>
    have hok : choiceOK c.dom (c.wires.map (· &&& c.dom)) op = true := by
      have h2 := cut.2
      simp only [hav, Bool.not_false, Bool.not_true, Bool.false_eq_true, false_or] at h2
      exact hpm ▸ h2
    obtain ⟨out, hr, hc⟩ := pay_choice dom hp hs op hok
    apply finish (c.paid + 1) out hr _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hc (choiceVal op) (by simp)
    · have hpt : poolSupply f out c.wires := fun v hv => hc v (List.mem_cons_of_mem _ hv)
      exact availM_sound dom hpt (hpm ▸ cut.1.2 a ha)
def fixRow (z o : Nat) (r : Row) : Row :=
  ⟨((r.val &&& (255 ^^^ z)) ||| o) % 256, Nat.mod_lt _ (by decide)⟩
def renameW (f : Row → Row) (a : Nat) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).toNat
lemma testBit_renameW (f : Row → Row) (a : Nat) (r : Row) :
    (renameW f a).testBit r.val = a.testBit (f r).val := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).getLsbD r.val = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, r.isLt, dite_true, Option.getD_some]
lemma renameW_lt (f : Row → Row) (a : Nat) : renameW f a < 2^256 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).isLt
lemma obs_renameW (f : Row → Row) (a : Nat) : obs (renameW f a) = restrictW f (obs a) := by
  funext r; exact testBit_renameW f a r
lemma renameW_bin (f : Row → Row) (d a b : Nat) :
    renameW f (bin d a b) = bin d (renameW f a) (renameW f b) := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 256
  · rw [testBit_renameW f _ ⟨r, hr⟩, testBit_bin, testBit_bin, testBit_renameW f _ ⟨r, hr⟩, testBit_renameW f _ ⟨r, hr⟩]
  · have hlt (x : Nat) : (renameW f x).testBit r = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f x) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hlt, testBit_bin, hlt, hlt]
    rcases d with _ | _ | _ | d <;> rfl
lemma renameW_zero (f : Row → Row) : renameW f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
  · simpa using testBit_renameW f 0 ⟨r, hr⟩
  · rw [Nat.zero_testBit]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f 0) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 256 ≤ r)))
lemma renameW_inj (f : Row → Row) (onto : Function.Surjective f) {a b : Nat}
    (ha : a < 2^256) (hb : b < 2^256) (eq : renameW f a = renameW f b) : a = b := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
  · obtain ⟨q, hq⟩ := onto ⟨r, hr⟩
    have h := congrArg (fun x => x.testBit q.val) eq
    rw [testBit_renameW, testBit_renameW, hq] at h
    exact h
  · have hge : 256 ≤ r := by omega
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide : 0 < 2) hge)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 0 < 2) hge))]
lemma live_renameW {T k S} (h : Live T k S) (hS : ∀ a ∈ S, a < 2^256) (f : Row → Row)
    (onto : Function.Surjective f) : Live (renameW f T) k (S.image (renameW f)) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hT⟩ := h
    have hTlt : T < 2^256 := hS T (by simp)
    refine ⟨by simp, fun hz => hT (renameW_inj f onto hTlt (by decide) (hz.trans (renameW_zero f).symm))⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := h
    have halt : a < 2^256 := hS a (by simp)
    have hblt : b < 2^256 := hS b (by simp)
    have hUlt : ∀ x ∈ U, x < 2^256 := fun x hx => hS x (by simp [hx])
    have hzlt : bin d a b < 2^256 := bin_lt d a b halt hblt
    have htail_lt : ∀ x ∈ insert (bin d a b) U, x < 2^256 := by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx; exact hzlt; exact hUlt x hx
    have nr := ih tail htail_lt
    simp only [Finset.image_insert, renameW_bin] at nr ⊢
    refine ⟨U.image (renameW f), renameW f a, renameW f b, d, hd, rfl,
      fun hz => ha (renameW_inj f onto halt (by decide) (hz.trans (renameW_zero f).symm)),
      fun hz => hb (renameW_inj f onto hblt (by decide) (hz.trans (renameW_zero f).symm)),
      fun heq => hab (renameW_inj f onto halt hblt heq), ?_, nr⟩
    intro hm
    rw [← renameW_bin] at hm
    rcases Finset.mem_insert.mp hm with heq | hm
    · exact fresh (by rw [renameW_inj f onto hzlt halt heq]; simp)
    rcases Finset.mem_insert.mp hm with heq | hm
    · exact fresh (by rw [renameW_inj f onto hzlt hblt heq]; simp)
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hm
    exact fresh (by rw [renameW_inj f onto hzlt (hUlt x hx) heq.symm]; simp [hx])
lemma wmass_append (a b : List Wire) : wmass (a ++ b) = wmass a + wmass b := by simp [wmass]
lemma wmass_consts (xs : List Wire) (hc : ∀ x ∈ xs, Constant x) : wmass xs = xs.length := by
  classical
  induction xs with
  | nil => simp [wmass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [wmass, List.map_cons, List.sum_cons, List.length_cons, wcost, ha, ite_true]
    have := ih (fun x hx => hc x (by simp [hx]))
    simp only [wmass] at this
    omega
lemma lower_slice {roots other : List Nat} {T G : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^256) (hGb0 : G.testBit 0 = false)
    (f : Row → Row) (eq : renameW f T = G)
    (covered : ∀ a ∈ roots, Avail (other.map obs) (restrictW f (obs a)))
    (singles : Finset Nat) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (restrictW f (obs a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left (by rwa [hnormT])
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]; conv_rhs => rw [← List.map_id roots]
    exact List.map_congr_left fun a ha' => normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have subS : singles ⊆ S := fun a hs => raw_required run roots a sub (necessary a hs)
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb he => ?_⟩
    subst b; exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset = S := by ext a; simp [front, Finset.union_sdiff_of_subset subS]
  have gc : restrictW f (obs T) = obs G := (obs_renameW f T).symm.trans (congrArg obs eq)
  have hsup : Supply (other.map obs) ((front.map obs).map (restrictW f)) := by
    intro v hv
    obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
    exact covered a (sub a (fe ▸ List.mem_toFinset.mpr ha'))
  obtain ⟨q, next, hq, hav, hbound⟩ :=
    contraction (gc ▸ obs_not_const hG0 hGlt hGb0) (restrict_run f (live_to_run run front nd fe))
      (other.map obs) (show Reach (other.map obs) 0 (other.map obs) from rfl) hsup
  have hlo := prior q next hq (gc ▸ hav)
  have hmass : singles.card ≤ wmass ((front.map obs).map (restrictW f)) := by
    simp only [front, List.map_append, wmass_append]
    let xs := (singles.toList.map obs).map (restrictW f)
    have hc : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
      exact constant a (Finset.mem_toList.mp ha')
    have hlen := wmass_consts xs hc
    simp only [xs, List.length_map, Finset.length_toList] at hlen
    change singles.card ≤ wmass xs + _
    rw [← hlen]
    exact Nat.le_add_right _ _
  have := hbound
  omega
lemma lower_count {roots : List Nat} {T : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
    (singles : Finset Nat) (ess : ∀ a ∈ singles, Essential T roots a) :
    Lower roots T (singles.card - 1) := by
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left (by rwa [hnormT])
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]; conv_rhs => rw [← List.map_id roots]
    exact List.map_congr_left fun a ha' => normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have hsub : singles ⊆ S := fun a ha' => raw_required run roots a sub (ess a ha')
  have hle := (Finset.card_le_card hsub).trans (live_size run)
  omega
def VAR (i : Nat) : Nat :=
  match i with
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
  | 7 => 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
  | _ => 0
def ALL256 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def swapRow (i j : Nat) (r : Row) : Row :=
  let bi := r.val.testBit i
  let bj := r.val.testBit j
  if bi == bj then r
  else ⟨(r.val ^^^ (1 <<< i) ^^^ (1 <<< j)) % 256, Nat.mod_lt _ (by decide)⟩
def swapWord (i j : Nat) (w : Nat) : Nat :=
  let a := VAR i
  let b := VAR j
  let m10 := a ^^^ (a &&& b)
  let m01 := b ^^^ (a &&& b)
  let msame := ALL256 ^^^ (m10 ||| m01)
  let d := (1 <<< j) - (1 <<< i)
  (w &&& msame) ||| ((w &&& m10) <<< d) ||| ((w &&& m01) >>> d)
def permRow (swaps : List (Nat × Nat)) (r : Row) : Row :=
  swaps.foldl (fun x p => swapRow p.1 p.2 x) r
def permWord (swaps : List (Nat × Nat)) (w : Nat) : Nat :=
  swaps.foldr (fun p x => swapWord p.1 p.2 x) w
lemma swapRow_invol (i j : Nat) (hi : i < 8) (hj : j < 8) (r : Row) :
    swapRow i j (swapRow i j r) = r := by
  revert r
  interval_cases i <;> interval_cases j <;> decide +kernel
lemma swapWord_testBit (i j : Nat) (hij : i < j) (hj : j < 8) (w : Nat) (hw : w < 2^256) (r : Row) :
    (swapWord i j w).testBit r.val = w.testBit (swapRow i j r).val := by
  have hi : i < 8 := by omega
  have hspec : ∀ r : Row,
      let a := VAR i; let b := VAR j
      let m10 := a ^^^ (a &&& b); let m01 := b ^^^ (a &&& b); let msame := ALL256 ^^^ (m10 ||| m01)
      let d := (1 <<< j) - (1 <<< i)
      (msame.testBit r.val = true → (swapRow i j r).val = r.val ∧ (d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = false) ∧
      (msame.testBit r.val = false →
        (d ≤ r.val ∧ m10.testBit (r.val - d) = true ∧ (swapRow i j r).val = r.val - d ∧ m01.testBit (r.val + d) = false) ∨
        ((d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = true ∧ (swapRow i j r).val = r.val + d)) := by
    revert r; interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have hr := hspec r
  simp only [swapWord, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.add_comm]
  cases hms : (ALL256 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))).testBit r.val with
  | true =>
    obtain ⟨heq, h10, h01⟩ := hr.1 hms
    rw [heq]
    by_cases hd : (1 <<< j) - (1 <<< i) ≤ r.val
    · simp [hd, h10 hd, h01]
    · simp [hd, h01]
  | false =>
    rcases hr.2 hms with ⟨hd, h10, heq, h01⟩ | ⟨h10, h01, heq⟩
    · simp [hd, h10, heq, h01]
    · by_cases hd : (1 <<< j) - (1 <<< i) ≤ r.val
      · simp [hd, h10 hd, h01, heq]
      · simp [hd, h01, heq]
lemma swapWord_lt (i j : Nat) (hij : i < j) (hj : j < 8) (w : Nat) : swapWord i j w < 2^256 := by
  have hi : i < 8 := by omega
  have h1 : (ALL256 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))) < 2^256 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h2 : ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) < 2^256 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h3 : ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) < 2^256 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  unfold swapWord
  have e1 : (w &&& (ALL256 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j))))) < 2^256 :=
    Nat.lt_of_le_of_lt Nat.and_le_right h1
  have e2 : ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i))) < 2^256 := by
    have hle : (w &&& (VAR i ^^^ (VAR i &&& VAR j))) ≤ (VAR i ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR i ^^^ (VAR i &&& VAR j))) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftLeft_eq _ _
      _ ≤ (VAR i ^^^ (VAR i &&& VAR j)) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.mul_le_mul_right _ hle
      _ = ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) := (Nat.shiftLeft_eq _ _).symm
      _ < 2^256 := h2
  have e3 : ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i))) < 2^256 := by
    have hle : (w &&& (VAR j ^^^ (VAR i &&& VAR j))) ≤ (VAR j ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR j ^^^ (VAR i &&& VAR j))) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftRight_eq_div_pow _ _
      _ ≤ (VAR j ^^^ (VAR i &&& VAR j)) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.div_le_div_right hle
      _ = ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) := (Nat.shiftRight_eq_div_pow _ _).symm
      _ < 2^256 := h3
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow e1 e2) e3
lemma swapWord_eq_renameW (i j : Nat) (hij : i < j) (hj : j < 8) (w : Nat) (hw : w < 2^256) :
    swapWord i j w = renameW (swapRow i j) w := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
  · rw [swapWord_testBit i j hij hj w hw ⟨r, hr⟩, ← testBit_renameW (swapRow i j) w ⟨r, hr⟩]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (swapWord_lt i j hij hj w) (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
def swapsValid (swaps : List (Nat × Nat)) : Bool :=
  swaps.all fun p => decide (p.1 < p.2) && decide (p.2 < 8)
lemma permWord_eq_renameW (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (w : Nat) (hw : w < 2^256) : permWord swaps w = renameW (permRow swaps) w := by
  induction swaps generalizing w with
  | nil =>
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 256
    · exact (testBit_renameW (permRow []) w ⟨r, hr⟩).symm
    · rw [show permWord [] w = w from rfl,
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have ihw := ih hv.2 w hw
    have hlt : permWord ps w < 2^256 := ihw ▸ renameW_lt _ w
    change swapWord p.1 p.2 (permWord ps w) = renameW (permRow (p :: ps)) w
    rw [swapWord_eq_renameW p.1 p.2 hv.1.1 hv.1.2 _ hlt, ihw]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 256
    · rw [testBit_renameW _ _ ⟨r, hr⟩, testBit_renameW _ _ (swapRow p.1 p.2 ⟨r, hr⟩), testBit_renameW _ _ ⟨r, hr⟩]
      rfl
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega)))]
lemma permRow_surj (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true) :
    Function.Surjective (permRow swaps) := by
  induction swaps with
  | nil => intro r; exact ⟨r, rfl⟩
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    intro r
    obtain ⟨q, hq⟩ := ih hv.2 r
    refine ⟨swapRow p.1 p.2 q, ?_⟩
    change permRow ps (swapRow p.1 p.2 (swapRow p.1 p.2 q)) = r
    rw [swapRow_invol p.1 p.2 (by omega) hv.1.2, hq]
lemma permRow_rev_cancel (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true) (r : Row) :
    permRow swaps.reverse (permRow swaps r) = r := by
  induction swaps generalizing r with
  | nil => rfl
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
        swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
      simp [permRow, List.reverse_cons, List.foldl_append]
    rw [h1, ih hv.2, swapRow_invol p.1 p.2 (by omega) hv.1.2]
lemma rotate_impossible {T n : Nat} {ws : List Nat} (hi : Impossible T n ws.toFinset)
    (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (hT : T < 2^256) (hfix : permWord swaps T = T)
    (hw : ∀ a ∈ ws, a < 2^256) :
    Impossible T n (ws.map (permWord swaps)).toFinset := by
  intro k hk run
  have hr : ∀ a ∈ (ws.map (permWord swaps)).toFinset, a < 2^256 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    rw [permWord_eq_renameW swaps hv x (hw x hx)]
    exact renameW_lt _ x
  have hvr : swapsValid swaps.reverse = true := by
    simp only [swapsValid, List.all_reverse]; exact hv
  have hinv_row2 : ∀ r : Row, permRow swaps (permRow swaps.reverse r) = r := by
    intro r; simpa using permRow_rev_cancel swaps.reverse hvr r
  have hinv_word : ∀ x : Nat, x < 2^256 → renameW (permRow swaps.reverse) (permWord swaps x) = x := by
    intro x hx
    rw [permWord_eq_renameW swaps hv x hx]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hrr : r < 256
    · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
  have run' := live_renameW run hr (permRow swaps.reverse) (permRow_surj swaps.reverse hvr)
  have hT' : renameW (permRow swaps.reverse) T = T := by
    conv_lhs => rw [← hfix]
    exact hinv_word T hT
  have hS' : (ws.map (permWord swaps)).toFinset.image (renameW (permRow swaps.reverse)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rwa [hinv_word x (hw x hx)]
    · intro ha
      exact ⟨permWord swaps a, ⟨a, ha, rfl⟩, hinv_word a (hw a ha)⟩
  rw [hT', hS'] at run'
  exact hi k hk run'
abbrev Decor := Nat × Nat × Nat
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1, bin d x.2.1 y.2.1, bin d x.2.2 y.2.2)
def dsep (x : Decor) : Nat := x.2.1 ^^^ x.2.2
def projBits (rows : List Nat) (w : Nat) : Nat :=
  rows.foldr (fun r acc => (acc <<< 1) ||| (if w.testBit r then 1 else 0)) 0
lemma testBit_projBits (rows : List Nat) (w i : Nat) :
    (projBits rows w).testBit i = match rows[i]? with | none => false | some r => w.testBit r := by
  induction rows generalizing i with
  | nil => simp [projBits]
  | cons r rs ih =>
    simp only [projBits, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Nat.not_le.mpr (by decide : 0 < 1)]
      cases w.testBit r <;> rfl
    | succ i =>
      simp only [List.getElem?_cons_succ, Nat.le_add_left, decide_true, Bool.true_and, Nat.add_sub_cancel]
      have h0 : (if w.testBit r then (1 : Nat) else 0).testBit (i + 1) = false := by
        cases w.testBit r
        · simp
        · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ i + 1)))
      rw [h0, Bool.or_false]
      exact ih i
lemma projBits_bin (rows : List Nat) (d a b : Nat) :
    projBits rows (bin d a b) = bin d (projBits rows a) (projBits rows b) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_projBits, testBit_bin, testBit_projBits, testBit_projBits]
  cases rows[i]? with
  | none => rcases d with _ | _ | _ | d <;> rfl
  | some r => exact testBit_bin d a b r
def faithful (pos neg : List Nat) (x : Decor) : Prop :=
  x.2.1 = projBits pos x.1 ∧ x.2.2 = projBits neg x.1
lemma faithful_bin {pos neg x y} (d : Nat) (hx : faithful pos neg x) (hy : faithful pos neg y) :
    faithful pos neg (dbin d x y) :=
  ⟨by rw [dbin, hx.1, hy.1, projBits_bin], by rw [dbin, hx.2, hy.2, projBits_bin]⟩
def goodPairs (T : Nat) (pos neg : List Nat) : Prop :=
  pos.length = neg.length ∧ ∀ i < pos.length,
    T.testBit (pos.getD i 0) = true ∧ T.testBit (neg.getD i 0) = false
def fullMask (n : Nat) : Nat := (1 <<< n) - 1
abbrev Cov := Nat × Nat × Nat
def addCov (z : Nat) (c : Cov) : Cov :=
  (z ||| c.1, (z ^^^ (z &&& c.1)) ||| (c.2.1 ^^^ (c.2.1 &&& z)),
   (z &&& c.2.1) ||| (c.2.2 ^^^ (c.2.2 &&& z)))
def coverage (v : List Decor) : Cov := v.foldr (fun a c => addCov (dsep a) c) (0, 0, 0)
def takeOne (c : Cov) (a : Nat) : Nat := c.1 ^^^ (c.1 &&& (c.2.1 &&& a))
def takeTwo (c : Cov) (a b : Nat) : Nat :=
  c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
lemma cov_one (c : Cov) (a : Nat) : takeOne (addCov a c) a = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeOne, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> rfl
lemma cov_two (c : Cov) (a b : Nat) : takeTwo (addCov a (addCov b c)) a b = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeTwo, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma addCov_swap (c : Cov) (a b : Nat) : addCov a (addCov b c) = addCov b (addCov a c) := by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [addCov, Nat.testBit_or]; cases a.testBit i <;> cases b.testBit i <;> rfl
  · apply Prod.ext <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
      simp only [addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor] <;>
      cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma cov_perm {l r : List Decor} (h : l.Perm r) : coverage l = coverage r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (dsep a)) ih
  | swap _ _ _ => exact addCov_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
def delOne (ws : List Decor) (a : Decor) (k : Bool) : List Decor := if k then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) : List Decor := delOne (delOne ws a ka) b kb
def restCov (c : Cov) (a b : Nat) (ka kb : Bool) : Nat :=
  if ka then (if kb then c.1 else takeOne c b) else if kb then takeOne c a else takeTwo c a b
lemma cov_delOne {ws : List Decor} (a : Decor) (ha : a ∈ ws) (k : Bool) :
    (coverage (delOne ws a k)).1 = if k then (coverage ws).1 else takeOne (coverage ws) (dsep a) := by
  cases k
  · change (coverage (ws.erase a)).1 = _
    rw [cov_perm (List.perm_cons_erase ha)]
    exact (cov_one _ _).symm
  · rfl
lemma cov_delTwo {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (ka kb : Bool) :
    (coverage (delTwo ws a b ka kb)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb := by
  cases ka <;> cases kb
  · have hbm : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
    have hp : ws.Perm (a :: b :: (ws.erase a).erase b) :=
      (List.perm_cons_erase ha).trans (List.Perm.cons _ (List.perm_cons_erase hbm))
    change (coverage ((ws.erase a).erase b)).1 = takeTwo (coverage ws) _ _
    rw [cov_perm hp]
    exact (cov_two _ _ _).symm
  · exact cov_delOne a ha false
  · exact cov_delOne b hb false
  · rfl
lemma cov_testBit (ws : List Decor) (i : Nat) :
    (coverage ws).1.testBit i = true ↔ ∃ x ∈ ws, (dsep x).testBit i = true := by
  induction ws with
  | nil => simp [coverage]
  | cons a ws ih =>
    change (dsep a ||| (coverage ws).1).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    simp
lemma cov_required {T k pos neg} {ws : List Decor}
    (gp : goodPairs T pos neg) (hf : ∀ x ∈ ws, faithful pos neg x)
    (h : Live T k (ws.map Prod.fst).toFinset) :
    ((coverage ws).1 &&& fullMask pos.length) = fullMask pos.length := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and]
  have hfm : (fullMask pos.length).testBit i = decide (i < pos.length) := by
    simp [fullMask, Nat.shiftLeft_eq, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < pos.length
  · have ⟨hp, hn⟩ := gp.2 i hi
    have hsep : T.testBit (pos.getD i 0) ≠ T.testBit (neg.getD i 0) := by rw [hp, hn]; decide
    obtain ⟨v, hv, hvd⟩ := live_sep h hsep
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    have hfx := hf x hx
    have hpi : pos[i]? = some (pos.getD i 0) := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    have hni : neg[i]? = some (neg.getD i 0) := by
      have hi' : i < neg.length := gp.1 ▸ hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    have hbit : (dsep x).testBit i = true := by
      simp only [dsep, Nat.testBit_xor, hfx.1, hfx.2, testBit_projBits, hpi, hni]
      have h12 : x.1.testBit (pos.getD i 0) ≠ x.1.testBit (neg.getD i 0) := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        exact hvd
      cases h1 : x.1.testBit (pos.getD i 0) <;> cases h2 : x.1.testBit (neg.getD i 0)
      · exact absurd (h1.trans h2.symm) h12
      · rfl
      · rfl
      · exact absurd (h1.trans h2.symm) h12
    have hc := (cov_testBit ws i).mpr ⟨x, hx, hbit⟩
    simp [hfm, hi, hc]
  · simp [hfm, hi]
def insertNat (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: insertNat a bs
def sortNats : List Nat → List Nat
  | [] => []
  | a :: bs => insertNat a (sortNats bs)
lemma insertNat_perm (a : Nat) (l : List Nat) : (insertNat a l).Perm (a :: l) := by
  induction l with
  | nil => exact .refl _
  | cons b bs ih =>
    by_cases h : a ≤ b
    · simp [insertNat, h]
    · exact by simpa [insertNat, h] using (List.Perm.cons b ih).trans (.swap a b bs)
lemma sortNats_perm (l : List Nat) : (sortNats l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons a bs ih => exact (insertNat_perm a (sortNats bs)).trans (.cons a ih)
lemma sortNats_toFinset (l : List Nat) : (sortNats l).toFinset = l.toFinset := by
  ext x; simpa only [List.mem_toFinset] using (sortNats_perm l).mem_iff
def childTwo (ws : List Nat) (a b d : Nat) (ka kb : Bool) : List Nat :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
lemma erase_toFinset {l : List Nat} (nd : l.Nodup) (a : Nat) :
    (l.erase a).toFinset = l.toFinset.erase a := by
  ext x; simp [nd.mem_erase_iff]
lemma enum_step {T cap : Nat} {ws : List Nat} (nd : ws.Nodup) (out : T ∉ ws)
    (stepOK : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d < 4, ∀ ka kb : Bool,
      a ≠ b → bin d a b ≠ 0 → bin d a b ∉ ws → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap - 1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k hk h
  cases k with
  | zero =>
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  | succ k =>
    obtain ⟨U, a, b, d, hd, he, _, _, hab, hf, tail⟩ := h
    have am : a ∈ ws := List.mem_toFinset.mp (he ▸ Finset.mem_insert_self a _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
    have fresh : bin d a b ∉ ws := fun hm => hf (he ▸ List.mem_toFinset.mpr hm)
    have hnz : bin d a b ≠ 0 := live_nonzero tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest = (ws.erase a).erase b from rfl, erase_toFinset (nd.erase _) b, erase_toFinset nd a]
    have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
      cases c <;> simp [kept]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kf, kf, er, he]; ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all [ka, kb]
    have rn : rest.Nodup := (nd.erase _).erase _
    have ar : a ∉ rest := fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest := (nd.erase a).not_mem_erase
    have nk := kept_nodup kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept, ar, hab]
    have ndc : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr hm))),
        kept_nodup ka a _ nk ax⟩
    have eqc : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b :: kept ka a (kept kb b rest)).toFinset = _; simp [ke]
    have sc := live_size tail
    have hlen : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [← List.toFinset_card_of_nodup ndc, eqc]; omega
    exact stepOK a am b bm d hd ka kb hab hnz fresh hlen k (by omega) (eqc.symm ▸ tail)
lemma delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k; exact List.erase_sublist; exact List.Sublist.refl _
lemma delTwo_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) : (delTwo ws a b ka kb).Sublist ws :=
  (delOne_sub _ _ _).trans (delOne_sub _ _ _)
lemma delTwo_len (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) :
    (delTwo ws a b ka kb).length = ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
  cases ka <;> cases kb <;> simp [delTwo, delOne, List.length_erase_of_mem ha, List.length_erase_of_mem hb, List.length_erase_of_mem hm]
lemma unique_fst {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (eq : a.1 = b.1) : a = b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact (hn (eq ▸ List.mem_map_of_mem hb')).elim
    · exact (hn (eq.symm ▸ List.mem_map_of_mem ha')).elim
    · exact ih ht ha' hb'
lemma delTwo_map_toFinset {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a.1 ≠ b.1) (d : Nat) (ka kb : Bool) :
    ((dbin d a b).1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  have wn : ws.Nodup := nd.of_map
  have dn : (delOne ws a ka).Nodup := wn.sublist (delOne_sub ws a ka)
  have m1 (l : List Decor) (hl : l.Nodup) (x y : Decor) (c : Bool) :
      y ∈ delOne l x c ↔ y ∈ l ∧ (y ≠ x ∨ c = true) := by
    cases c <;> simp [delOne, hl.mem_erase_iff, and_comm]
  have km (v : Nat) : v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
      v ∈ ws.map Prod.fst ∧ (v ≠ a.1 ∨ ka = true) ∧ (v ≠ b.1 ∨ kb = true) := by
    simp only [delTwo, List.mem_map, m1 _ wn, m1 _ dn]
    constructor
    · rintro ⟨w, ⟨⟨hw, h1⟩, h2⟩, rfl⟩
      exact ⟨⟨w, hw, rfl⟩, h1.imp (fun h e => h (unique_fst nd hw ha e)) id,
        h2.imp (fun h e => h (unique_fst nd hw hb e)) id⟩
    · rintro ⟨⟨w, hw, rfl⟩, h1, h2⟩
      exact ⟨w, ⟨⟨hw, h1.imp (fun h e => h (congrArg Prod.fst e)) id⟩,
        h2.imp (fun h e => h (congrArg Prod.fst e)) id⟩, rfl⟩
  have av := List.mem_map_of_mem (f := Prod.fst) ha
  have bv := List.mem_map_of_mem (f := Prod.fst) hb
  have hkeep (c : Bool) (x : Nat) (l : List Nat) (v : Nat) : v ∈ kept c x l ↔ (v = x ∧ c = true) ∨ v ∈ l := by
    cases c <;> simp [kept]
  ext v
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, km, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, dbin]
  by_cases va : v = a.1 <;> by_cases vb : v = b.1 <;> cases ka <;> cases kb <;> simp_all
lemma childTwo_swap (v : List Nat) (nd : v.Nodup) (a b : Nat) (d : Nat) (hd : d < 4) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  have hkeep (c : Bool) (x : Nat) (l : List Nat) (y : Nat) : y ∈ kept c x l ↔ (y = x ∧ c = true) ∨ y ∈ l := by
    cases c <;> simp [kept]
  ext x
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, bin_comm_flip d hd a b]
  tauto
def varsOf (m : Nat) : List Nat :=
  (List.range 8).filterMap fun i => if m.testBit i then some (VAR i) else none
def subcube (z o : Nat) : Nat :=
  (List.range 256).foldr (fun r acc =>
    if (r &&& z == 0) && (r &&& o == o) then acc ||| (1 <<< r) else acc) 0
def fixWord (z o w : Nat) : Nat :=
  (List.range 256).foldr (fun r acc =>
    let fr := ((r &&& (255 ^^^ z)) ||| o) % 256
    if w.testBit fr then acc ||| (1 <<< r) else acc) 0
lemma testBit_foldr_bits (p : Nat → Bool) (l : List Nat) (r : Nat) :
    (l.foldr (fun i acc => if p i then acc ||| (1 <<< i) else acc) 0).testBit r =
      (decide (r ∈ l) && p r) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    by_cases hpa : p a = true
    · simp only [hpa, ite_true, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
      by_cases hra : r = a
      · subst hra; simp [hpa]
      · have h1 : (decide (a ≤ r) && (1 : Nat).testBit (r - a)) = false := by
          by_cases hle : a ≤ r
          · have hpos : r - a ≠ 0 := by omega
            simp only [hle, decide_true, Bool.true_and]
            exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ r - a)))
          · simp [hle]
        simp [h1, hra]
    · have hpf : p a = false := Bool.eq_false_iff.mpr hpa
      simp only [hpf, Bool.false_eq_true, ite_false, ih]
      by_cases hra : r = a
      · subst hra; simp [hpf]
      · simp [hra]
lemma fixWord_eq_renameW (z o w : Nat) : fixWord z o w = renameW (fixRow z o) w := by
  apply Nat.eq_of_testBit_eq; intro r
  unfold fixWord
  rw [testBit_foldr_bits]
  by_cases hr : r < 256
  · rw [testBit_renameW (fixRow z o) w ⟨r, hr⟩]
    simp [hr, fixRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma subcube_fixRow (z o : Nat) (hz : z < 256) (ho : o < 256) (hzo : (z &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow z o r).val = true := by
  unfold subcube
  rw [testBit_foldr_bits]
  have hmem : (fixRow z o r).val ∈ List.range 256 := List.mem_range.mpr (fixRow z o r).isLt
  simp only [hmem, decide_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have h127 : ((r.val &&& (255 ^^^ z)) ||| o) < 256 := by
    have hr := r.isLt
    have hlt1 : (r.val &&& (255 ^^^ z)) < 256 := Nat.lt_of_le_of_lt Nat.and_le_left hr
    exact Nat.or_lt_two_pow (n := 8) hlt1 ho
  have hval : (fixRow z o r).val = ((r.val &&& (255 ^^^ z)) ||| o) := Nat.mod_eq_of_lt h127
  rw [hval]
  constructor
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit]
    have hzi : (z.testBit i && o.testBit i) = false := by
      have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
    by_cases hi : i < 8
    · have h7 : (255 : Nat).testBit i = true := by interval_cases i <;> decide
      cases hzb : z.testBit i <;> cases hob : o.testBit i <;> simp_all [h7]
    · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 ≤ i)))
      simp [hzf]
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases o.testBit i <;> simp
def checkEss1 (T : Nat) (roots : List Nat) (a r s : Nat) : Bool :=
  decide (r < 256) && decide (s < 256) && (T.testBit r != T.testBit s) &&
    roots.all fun v => v == a || (v.testBit r == v.testBit s)
lemma checkEss1_sound {T roots a r s} (h : checkEss1 T roots a r s = true) : Essential T roots a := by
  simp only [checkEss1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨⟨r, h.1.1.1⟩, ⟨s, h.1.1.2⟩, h.1.2, fun v hv hne => (h.2 v hv).resolve_left hne⟩
def freeIn (other : List Nat) (w : Nat) : Bool := w == 0 || w == ALL256 || other.contains w
lemma freeIn_sound {other : List Nat} {f : Row → Row} {a : Nat} (ok : freeIn other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)) := by
  rw [← obs_renameW]
  simp only [freeIn, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (h0 | h1) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL256]; have := r.isLt; exact Nat.testBit_two_pow_sub_one 256 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkProper (w : Nat) : Bool := w != 0 && decide (w < 2^256) && !w.testBit 0
lemma checkProper_sound {w : Nat} (h : checkProper w = true) : w ≠ 0 ∧ w < 2^256 ∧ w.testBit 0 = false := by
  simp only [checkProper, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
def checkRoots (rs : List Nat) : Bool := rs.all fun a => decide (a < 2^256) && !a.testBit 0
lemma checkRoots_sound {rs : List Nat} (h : checkRoots rs = true) :
    ∀ a ∈ rs, a < 2^256 ∧ a.testBit 0 = false := by
  simp only [checkRoots, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact h
def carryOK (swaps : List (Nat × Nat)) (roots1 : List Nat) (T1 : Nat) (roots2 : List Nat) (T2 : Nat) : Bool :=
  swapsValid swaps && checkProper T1 && checkRoots roots1 && checkProper T2 &&
    (permWord swaps T1 == T2) && roots1.all (fun a => freeIn roots2 (permWord swaps a))
lemma carry_of {swaps roots1 T1 roots2 T2 L} (ok : carryOK swaps roots1 T1 roots2 T2 = true)
    (hL : Lower roots2 T2 L) : Lower roots1 T1 L := by
  simp only [carryOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨hsv, hT1⟩, hR1⟩, hT2⟩, heq⟩, hcov⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT1
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hT2
  have hR1' := checkRoots_sound hR1
  have heq' : renameW (permRow swaps) T1 = T2 := (permWord_eq_renameW swaps hsv T1 p1b).symm.trans heq
  have hcov' : ∀ a ∈ roots1, Avail (roots2.map obs) (restrictW (permRow swaps) (obs a)) := fun a ha =>
    freeIn_sound (permWord_eq_renameW swaps hsv a (hR1' a ha).1 ▸ hcov a ha)
  simpa using lower_slice p1a p1b p1c hR1' p2a p2b p2c (permRow swaps) heq' hcov' ∅ (by simp) (by simp) L hL
def countCheck (roots : List Nat) (T L : Nat) (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots &&
    decide (essPairs.map Prod.fst).Nodup &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2) &&
    decide (L ≤ essPairs.length - 1)
lemma count_of {roots T L essPairs} (ok : countCheck roots T L essPairs = true) :
    Lower roots T L := by
  simp only [countCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨hT, hR⟩, hnd⟩, hess⟩, hle⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hl := lower_count p1 p2 p3 hR' (essPairs.map Prod.fst).toFinset (fun a ha => by
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm))
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [hcard] at hl
  exact fun p bank hr hav => hle.trans (hl p bank hr hav)
def liftCheck (z o : Nat) (roots : List Nat) (T : Nat) (other : List Nat) (G : Nat)
    (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots && checkProper G &&
    decide (essPairs.map Prod.fst).Nodup &&
    (fixWord z o T == G) &&
    roots.all (fun a => freeIn other (fixWord z o a)) &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2 &&
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL256))
lemma lift_of {z o roots T other G essPairs L} (ok : liftCheck z o roots T other G essPairs = true)
    (hL : Lower other G L) : Lower roots T (L + essPairs.length) := by
  simp only [liftCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hT, hR⟩, hG⟩, hnd⟩, heq⟩, hcov⟩, hess⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hG
  have hR' := checkRoots_sound hR
  have heq' : renameW (fixRow z o) T = G := (fixWord_eq_renameW z o T).symm.trans heq
  have hcov' : ∀ a ∈ roots, Avail (other.map obs) (restrictW (fixRow z o) (obs a)) := fun a ha =>
    freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha)
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [← hcard]
  apply lower_slice p1a p1b p1c hR' p2a p2b p2c (fixRow z o) heq' hcov' (essPairs.map Prod.fst).toFinset _ _ L hL
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm).1
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    have hc := (hess (v, r, s) hm).2
    simp only [Bool.or_eq_true, beq_iff_eq, fixWord_eq_renameW] at hc
    rw [← obs_renameW]
    rcases hc with h0 | h1
    · exact ⟨false, by rw [h0]; funext r'; simp [obs]⟩
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL256]; have := r'.isLt; exact Nat.testBit_two_pow_sub_one 256 r'.val |> fun e => by simpa [this] using e⟩
def sliceCheck (z o zDrop : Nat) (raw : List Nat) (T : Nat) (freeRoots : List Nat) (qRoots : List Nat) (qGoal : Nat)
    (qL : Nat) (lEss : List (Nat × Nat × Nat)) (sliceL : Nat) : Bool :=
  let G := fixWord z o T
  decide (z < 256) && decide (o < 256) && ((z &&& o) == 0) &&
    checkProper G && checkRoots freeRoots &&
    raw.all (fun a => freeIn freeRoots (fixWord z o a)) &&
    (if qGoal == 0 then
       decide (lEss.map Prod.fst).Nodup &&
       lEss.all (fun e => checkEss1 G freeRoots e.1 e.2.1 e.2.2) &&
       decide (sliceL ≤ lEss.length - 1)
     else
       liftCheck zDrop 0 freeRoots G qRoots qGoal lEss &&
       decide (sliceL ≤ qL + lEss.length))
lemma slice_of {z o zDrop raw T freeRoots qRoots qGoal qL lEss sliceL}
    (ok : sliceCheck z o zDrop raw T freeRoots qRoots qGoal qL lEss sliceL = true)
    (hPrior : qGoal ≠ 0 → Lower qRoots qGoal qL) :
    Slice raw T (subcube z o) sliceL := by
  simp only [sliceCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hz, ho⟩, hzo⟩, hGp⟩, hFR⟩, hcov⟩, htail⟩ := ok
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  have hFR' := checkRoots_sound hFR
  refine ⟨fixRow z o, freeRoots, subcube_fixRow z o hz ho hzo,
    fun a ha => freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha),
    by rw [← obs_renameW, ← fixWord_eq_renameW]; exact obs_not_const g0 glt gb0, ?_⟩
  rw [← obs_renameW, ← fixWord_eq_renameW]
  by_cases hq : qGoal = 0
  · simp only [hq, ite_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at htail
    have hl := lower_count g0 glt gb0 hFR' (lEss.map Prod.fst).toFinset (fun a ha => by
      obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      exact checkEss1_sound (htail.1.2 _ hm))
    have hcard : (lEss.map Prod.fst).toFinset.card = lEss.length := by
      rw [List.toFinset_card_of_nodup htail.1.1, List.length_map]
    rw [hcard] at hl
    exact fun p bank hr hav => htail.2.trans (hl p bank hr hav)
  · simp only [hq, ite_false, Bool.and_eq_true, decide_eq_true_eq] at htail
    have hl := lift_of htail.1 (hPrior hq)
    exact fun p bank hr hav => htail.2.trans (hl p bank hr hav)
def goodPairsCheck (T : Nat) (pos neg : List Nat) : Bool :=
  (pos.length == neg.length) &&
    (List.range pos.length).all fun i => T.testBit (pos.getD i 0) && !(T.testBit (neg.getD i 0))
lemma goodPairs_of {T pos neg} (ok : goodPairsCheck T pos neg = true) : goodPairs T pos neg := by
  simp only [goodPairsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at ok
  exact ok
def autosCheck (T : Nat) (autos : List (List (Nat × Nat))) : Bool :=
  autos.all fun sw => swapsValid sw && (permWord sw T == T)
lemma autos_of {T autos} (ok : autosCheck T autos = true) :
    ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T := by
  simp only [autosCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at ok
  exact ok
def baseCheck (pos neg : List Nat) (base : List Decor) : Bool :=
  base.all fun x => (x.2.1 == projBits pos x.1) && (x.2.2 == projBits neg x.1) && decide (x.1 < 2^256)
lemma base_of {pos neg base} (ok : baseCheck pos neg base = true) :
    ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^256 := by
  simp only [baseCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  intro x hx
  have h := ok x hx
  exact ⟨⟨h.1.1, h.1.2⟩, h.2⟩
def forestRootCheck (roots : List Nat) (T : Nat) (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots &&
    roots.all fun a => essPairs.any fun e => (e.1 == a) && checkEss1 T roots e.1 e.2.1 e.2.2
lemma faithful_zero (pos neg : List Nat) : faithful pos neg (0, 0, 0) := by
  constructor
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases pos[i]? <;> simp
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases neg[i]? <;> simp
lemma forall_cons {α : Type} {P : α → Prop} {a : α} {l : List α} (ha : P a) (hl : ∀ x ∈ l, P x) :
    ∀ x ∈ a :: l, P x := by
  intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exact ha; exact hl x hx
abbrev PoolSpec := Nat × List (Nat × Nat × Nat)
abbrev NodeSpec := List Nat × List Nat × List Nat
def evalInput (r : Row) : Fin 8 → Bool := fun i => r.val.testBit i.val
def packInput (x : Fin 8 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
    16 * (x 4).toNat + 32 * (x 5).toNat + 64 * (x 6).toNat + 128 * (x 7).toNat, by
    have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
    have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
    have h6 := Bool.toNat_le (x 6); have h7 := Bool.toNat_le (x 7); omega⟩
lemma evalInput_packInput (x : Fin 8 → Bool) : evalInput (packInput x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) (j : Fin 8),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat + 64 * b6.toNat + 128 * b7.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5, b6, b7].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) i
  fin_cases i <;> simpa [evalInput, packInput] using hi
lemma var_testBit (i : Fin 8) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by
  revert i r; decide +kernel
lemma sw_extract_full (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 255 := by
  let seeds : List SWire := (varsOf 255).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^256 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 255).all (fun a => decide (a < 2^256) && !a.testBit 0) = true := by decide +kernel
    have h1 := List.all_eq_true.mp hall v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact h1
  let final := swExec gs seeds
  let out := final.getD o swZero
  have hfinal_lt : out.2 < 2^256 ∧ out.2.testBit 0 = false := by
    simp only [out, List.getD_eq_getElem?_getD]
    cases eq : final[o]? with
    | none => exact ⟨by decide, by decide⟩
    | some a => exact swExec_lt gs seeds hseeds_lt a (List.mem_of_getElem? eq)
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi7 : i < 8 := by simpa using hi2
      have hv : (varsOf 255)[i]? = some (VAR i) := by
        interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput, swRead, Bool.false_bne]
      have hget : (varsOf 255)[i]'(by simpa [seeds] using hi1) = VAR i := by
        have := List.getElem?_eq_some_iff.mp hv; exact this.2
      rw [hget]
      exact var_testBit ⟨i, hi7⟩ r
  have hev (r : Row) : swRead r.val out = T.testBit r.val := by
    have h1 := (swRead_get r.val final o).symm
    rw [show final = swExec gs seeds from rfl, swExec_read r.val gs seeds legal, hread_seeds r] at h1
    exact h1.trans (he r)
  have hout0 : out.1 = false := by
    have h0 := hev 0
    simp only [swRead, Fin.val_zero, hfinal_lt.2, hTb0, Bool.bne_false] at h0
    exact h0
  have hout2 : out.2 = T := by
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 256
    · have h := hev ⟨r, hr⟩
      simpa [swRead, hout0] using h
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hfinal_lt.1 (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hTlt (Nat.pow_le_pow_right (by decide) (by omega)))]
  have hfound : T ∈ reps final := by
    rw [← hout2]
    exact (get_simple final o).resolve_left (hout2.symm ▸ hT0)
  obtain ⟨k, S, hk, hlive, hsub⟩ := extract_live hT0 gs seeds hfound
  refine ⟨k, S, hk, hlive, ?_⟩
  simpa [reps, seeds, List.map_map, Function.comp_def] using hsub
lemma replace_of_lower (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 255) T L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : ∀ g ∈ wit, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (edgeFn : (Fin 8 → Bool) → Bool)
    (hEdgeT : ∀ r : Row, edgeFn (evalInput r) = T.testBit r.val)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput r)) = T.testBit r.val)
    (gates : List Gate) (o : Nat)
    (legal : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (spec : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = edgeFn x) :
    ∃ (gates' : List Gate) (o' : Nat),
      (∀ g ∈ gates', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = edgeFn x := by
  have hwEval : ∀ x : Fin 8 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = edgeFn x := by
    intro x
    have hx := evalInput_packInput x
    rw [← hx]
    exact (hwEvalR (packInput x)).trans (hEdgeT (packInput x)).symm
  by_cases hn : ∃ g ∈ gates, g.op = .not
  · have hlt : gates.countP isBin < gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro eq
      obtain ⟨g, hg, hop⟩ := hn
      have bad := List.countP_eq_length.mp eq g hg
      simp [isBin, hop] at bad
    obtain ⟨k, S, hk, hlive, hsub⟩ := sw_extract_full T hT0 hTlt hTb0 gates o legal (fun r => (spec (evalInput r)).trans (hEdgeT r))
    have hnd : S.toList.Nodup := Finset.nodup_toList S
    have hrun := live_to_run hlive S.toList hnd (by simp)
    have hsup : Supply ((varsOf 255).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 255).map obs)
        (show Reach ((varsOf 255).map obs) 0 ((varsOf 255).map obs) from rfl) hsup
    have hlo := hLow q next hq hav
    refine ⟨wit, wo, hwMono, by omega, hwEval⟩
  · refine ⟨gates, o, ?_, le_rfl, spec⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := legal g hg
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g, hg, h⟩).elim
def sliceDirectCheck (z o zDead : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (z < 256) && decide (o < 256) && ((z &&& o) == 0) &&
    decide (zDead < 256) && (((z ||| zDead) &&& o) == 0) &&
    checkProper qGoal && checkRoots qRoots &&
    (fixWord (z ||| zDead) o T == qGoal) &&
    raw.all (fun a => freeIn qRoots (fixWord (z ||| zDead) o a))
lemma subcube_fixRow_sup (z o zDead : Nat) (hz : z < 256) (hd : zDead < 256) (ho : o < 256)
    (hzo : ((z ||| zDead) &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow (z ||| zDead) o r).val = true := by
  have hsub := subcube_fixRow (z ||| zDead) o (Nat.or_lt_two_pow (n := 8) hz hd) ho hzo r
  unfold subcube at hsub ⊢
  rw [testBit_foldr_bits] at hsub ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsub ⊢
  refine ⟨hsub.1, ?_, hsub.2.2⟩
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun x => x.testBit i) hsub.2.1
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h1 ⊢
  cases hfa : (fixRow (z ||| zDead) o r).val.testBit i <;> cases hzb : z.testBit i <;> simp_all
lemma slice_direct {z o zDead raw T qRoots qGoal qL}
    (ok : sliceDirectCheck z o zDead raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcube z o) qL := by
  simp only [sliceDirectCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hz, ho⟩, _hzo0⟩, hd⟩, hzo⟩, hGp⟩, hQR⟩, heq⟩, hcov⟩ := ok
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  refine ⟨fixRow (z ||| zDead) o, qRoots, subcube_fixRow_sup z o zDead hz hd ho hzo,
    fun a ha => freeIn_sound ((fixWord_eq_renameW (z ||| zDead) o a).symm ▸ hcov a ha),
    by rw [← obs_renameW, ← fixWord_eq_renameW, heq]; exact obs_not_const g0 glt gb0, ?_⟩
  rw [← obs_renameW, ← fixWord_eq_renameW, heq]
  exact hPrior
inductive BT (α : Type) where
  | empty : BT α
  | leaf : α → BT α
  | node : BT α → BT α → BT α
def btGet {α : Type} (d : α) : BT α → Nat → α
  | .empty, _ => d
  | .leaf x, _ => x
  | .node l r, i => if i &&& 1 == 0 then btGet d l (i >>> 1) else btGet d r (i >>> 1)
def btSet {α : Type} : Nat → BT α → Nat → α → BT α
  | 0, _, _, v => .leaf v
  | d + 1, .empty, i, v =>
    if i &&& 1 == 0 then .node (btSet d .empty (i >>> 1) v) .empty
    else .node .empty (btSet d .empty (i >>> 1) v)
  | d + 1, .leaf x, i, v =>
    if i &&& 1 == 0 then .node (btSet d (.leaf x) (i >>> 1) v) .empty
    else .node .empty (btSet d (.leaf x) (i >>> 1) v)
  | d + 1, .node l r, i, v =>
    if i &&& 1 == 0 then .node (btSet d l (i >>> 1) v) r
    else .node l (btSet d r (i >>> 1) v)
def btUpdate {α : Type} (d0 : α) : Nat → BT α → Nat → (α → α) → BT α
  | 0, .leaf x, _, f => .leaf (f x)
  | 0, _, _, f => .leaf (f d0)
  | d + 1, .empty, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d .empty (i >>> 1) f) .empty
    else .node .empty (btUpdate d0 d .empty (i >>> 1) f)
  | d + 1, .leaf x, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d (.leaf x) (i >>> 1) f) .empty
    else .node .empty (btUpdate d0 d (.leaf x) (i >>> 1) f)
  | d + 1, .node l r, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d l (i >>> 1) f) r
    else .node l (btUpdate d0 d r (i >>> 1) f)
def btAll {α : Type} (P : α → Prop) : BT α → Prop
  | .empty => True
  | .leaf x => P x
  | .node l r => btAll P l ∧ btAll P r
lemma btAll_get {α : Type} {P : α → Prop} {d : α} {t : BT α} (ht : btAll P t) (hd : P d) (i : Nat) :
    P (btGet d t i) := by
  induction t generalizing i with
  | empty => exact hd
  | leaf x => exact ht
  | node l r ihl ihr =>
    unfold btGet
    split
    · exact ihl ht.1 _
    · exact ihr ht.2 _
lemma btAll_set {α : Type} {P : α → Prop} {depth : Nat} {t : BT α} {i : Nat} {v : α}
    (ht : btAll P t) (hv : P v) : btAll P (btSet depth t i v) := by
  induction depth generalizing t i with
  | zero => exact hv
  | succ d ih =>
    cases t with
    | empty =>
      unfold btSet; split
      · exact ⟨ih trivial, trivial⟩
      · exact ⟨trivial, ih trivial⟩
    | leaf x =>
      unfold btSet; split
      · exact ⟨ih ht, trivial⟩
      · exact ⟨trivial, ih ht⟩
    | node l r =>
      unfold btSet; split
      · exact ⟨ih ht.1, ht.2⟩
      · exact ⟨ht.1, ih ht.2⟩
lemma btAll_update {α : Type} {P : α → Prop} {d0 : α} {depth : Nat} {t : BT α} {i : Nat} {f : α → α}
    (ht : btAll P t) (hd0 : P d0) (hf : ∀ x, P x → P (f x)) : btAll P (btUpdate d0 depth t i f) := by
  induction depth generalizing t i with
  | zero =>
    cases t with
    | leaf x => exact hf x ht
    | empty => exact hf d0 hd0
    | node _ _ => exact hf d0 hd0
  | succ d ih =>
    cases t with
    | empty =>
      unfold btUpdate; split
      · exact ⟨ih trivial, trivial⟩
      · exact ⟨trivial, ih trivial⟩
    | leaf x =>
      unfold btUpdate; split
      · exact ⟨ih ht, trivial⟩
      · exact ⟨trivial, ih ht⟩
    | node l r =>
      unfold btUpdate; split
      · exact ⟨ih ht.1, ht.2⟩
      · exact ⟨ht.1, ih ht.2⟩
def btOfList {α : Type} (depth : Nat) (l : List α) : BT α :=
  (l.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) (0, BT.empty)).2
lemma btAll_ofList {α : Type} {P : α → Prop} {depth : Nat} {l : List α}
    (h : ∀ x ∈ l, P x) : btAll P (btOfList depth l) := by
  unfold btOfList
  have hgo : ∀ (xs : List α) (acc : Nat × BT α),
      (∀ x ∈ xs, P x) → btAll P acc.2 →
      btAll P (xs.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) acc).2 := by
    intro xs
    induction xs with
    | nil => intro acc _ hacc; exact hacc
    | cons x xs ih =>
      intro acc hx hacc
      exact ih (acc.1 + 1, btSet depth acc.2 acc.1 x)
        (fun y hy => hx y (List.mem_cons_of_mem _ hy))
        (btAll_set hacc (hx x (List.mem_cons_self ..)))
  exact hgo l (0, BT.empty) h trivial
def fastBitMask (z o i : Nat) : Nat :=
  if z.testBit i then ALL256 ^^^ VAR i else if o.testBit i then VAR i else ALL256
def subcubeFast (z o : Nat) : Nat :=
  fastBitMask z o 0 &&& fastBitMask z o 1 &&& fastBitMask z o 2 &&& fastBitMask z o 3 &&&
  fastBitMask z o 4 &&& fastBitMask z o 5 &&& fastBitMask z o 6 &&& fastBitMask z o 7
lemma fastBitMask_testBit (z o i : Nat) (hi : i < 8) (r : Row) :
    (fastBitMask z o i).testBit r.val =
      (if z.testBit i then !(r.val.testBit i) else if o.testBit i then r.val.testBit i else true) := by
  have hall : ALL256.testBit r.val = true := by
    simp only [ALL256]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 256 r.val
  have hvar : (VAR i).testBit r.val = r.val.testBit i := var_testBit ⟨i, hi⟩ r
  unfold fastBitMask
  split
  · simp [Nat.testBit_xor, hall, hvar]
  · split
    · exact hvar
    · exact hall
lemma subcubeFast_eq_subcube (z o : Nat) (hz : z < 256) (ho : o < 256) (hzo : (z &&& o) = 0) :
    subcubeFast z o = subcube z o := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
  · have hsub : (subcube z o).testBit r = ((r &&& z == 0) && (r &&& o == o)) := by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and,
      fastBitMask_testBit z o 0 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 1 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 2 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 3 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 4 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 5 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 6 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 7 (by decide) ⟨r, hr⟩]
    have hbit (i : Nat) (hi : i < 8) :
        ((r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i) ↔
          (if z.testBit i then !r.testBit i else if o.testBit i then r.testBit i else true) = true := by
      have hzi : (z.testBit i && o.testBit i) = false := by
        have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
      simp only [Nat.testBit_and]
      cases hz' : z.testBit i <;> cases ho' : o.testBit i <;> cases hr' : r.testBit i <;> simp_all
    have heq_iff : (((r &&& z == 0) && (r &&& o == o)) = true) ↔
        ∀ i < 8, (r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩ i _; rw [h1, h2, Nat.zero_testBit]; exact ⟨rfl, rfl⟩
      · intro h
        constructor
        · apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.zero_testBit]
          by_cases hi : i < 8
          · exact (h i hi).1
          · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 ≤ i)))
            simp [Nat.testBit_and, hzf]
        · apply Nat.eq_of_testBit_eq; intro i
          by_cases hi : i < 8
          · exact (h i hi).2
          · have hof : o.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 ≤ i)))
            simp [Nat.testBit_and, hof]
    apply Bool.eq_iff_iff.mpr
    rw [heq_iff]
    simp only [Bool.and_eq_true]
    constructor
    · intro h i hi
      have := hbit i hi
      interval_cases i <;> tauto
    · intro h
      refine ⟨⟨⟨⟨⟨⟨⟨(hbit 0 (by decide)).mp (h 0 (by decide)), (hbit 1 (by decide)).mp (h 1 (by decide))⟩,
        (hbit 2 (by decide)).mp (h 2 (by decide))⟩, (hbit 3 (by decide)).mp (h 3 (by decide))⟩,
        (hbit 4 (by decide)).mp (h 4 (by decide))⟩, (hbit 5 (by decide)).mp (h 5 (by decide))⟩,
        (hbit 6 (by decide)).mp (h 6 (by decide))⟩, (hbit 7 (by decide)).mp (h 7 (by decide))⟩
  · have hlt_f (i : Nat) : (fastBitMask z o i).testBit r = false := by
      have hle : 256 ≤ r := by omega
      have ha : ALL256 < 2^256 := by decide
      have hv : VAR i < 2^256 := by
        unfold VAR; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · change (0 : Nat) < 2^256; decide
      have hlt_m : fastBitMask z o i < 2^256 := by
        unfold fastBitMask; split
        · exact Nat.xor_lt_two_pow ha hv
        · split; exact hv; exact ha
      exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt_m (Nat.pow_le_pow_right (by decide : 0 < 2) hle))
    have hsub : (subcube z o).testBit r = false := by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and, hlt_f]
    rfl
lemma slice_fast_of {z o zDrop raw T freeRoots qRoots qGoal qL lEss sliceL}
    (ok : sliceCheck z o zDrop raw T freeRoots qRoots qGoal qL lEss sliceL = true)
    (hPrior : qGoal ≠ 0 → Lower qRoots qGoal qL) :
    Slice raw T (subcubeFast z o) sliceL := by
  have ok2 := ok
  simp only [sliceCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ok2
  rw [subcubeFast_eq_subcube z o ok2.1.1.1.1.1.1 ok2.1.1.1.1.1.2 ok2.1.1.1.1.2]
  exact slice_of ok hPrior
lemma slice_fast_direct {z o zDead raw T qRoots qGoal qL}
    (ok : sliceDirectCheck z o zDead raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcubeFast z o) qL := by
  have ok2 := ok
  simp only [sliceDirectCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ok2
  rw [subcubeFast_eq_subcube z o ok2.1.1.1.1.1.1.1.1 ok2.1.1.1.1.1.1.1.2 ok2.1.1.1.1.1.1.2]
  exact slice_direct ok hPrior
def hashWs64 (ws : List Nat) : Nat :=
  (ws.foldl (fun h w => h + (w % 1000003) * 31) 0) &&& 63
def bucketContainsBT (bks : BT (List (List Nat))) (ws : List Nat) : Bool :=
  let s := sortNats ws
  (btGet [] bks (hashWs64 s)).contains s
def closeChildBT (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun c => scalarPoolCut c k rest op) ||
    autos.any (fun sw => bucketContainsBT prevBks (ws.map (permWord sw)))
lemma closeChildBT_sound {raw T pools autos prevBks k rest op}
    (hT : T < 2^256)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun b => ∀ xs ∈ b, Impossible T k xs.toFinset) prevBks)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^256)
    (h : closeChildBT pools autos prevBks k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChildBT, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨c, hc, hcut⟩ | ⟨sw, hsw, hhit⟩
  · exact scalarPoolCut_sound (hPools c hc) nd hcut
  · unfold bucketContainsBT at hhit
    have hmem := List.contains_iff_mem.mp hhit
    have hb : ∀ xs ∈ btGet [] prevBks (hashWs64 (sortNats ((choiceVal op :: rest).map (permWord sw)))),
        Impossible T k xs.toFinset :=
      btAll_get hPrev (fun _ hx => (List.not_mem_nil hx).elim) _
    have himp := hb _ hmem
    rw [sortNats_toFinset] at himp
    have ⟨hsv, hfix⟩ := hAutos sw hsw
    have hvr : swapsValid sw.reverse = true := by simp only [swapsValid, List.all_reverse]; exact hsv
    have hinv_row_gen : ∀ (l : List (Nat × Nat)), swapsValid l = true →
        ∀ r : Row, permRow l.reverse (permRow l r) = r := by
      intro l hl
      induction l with
      | nil => intro r; rfl
      | cons p ps ih =>
        simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
        intro r
        have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
            swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
          simp [permRow, List.reverse_cons, List.foldl_append]
        rw [h1, ih hl.2, swapRow_invol p.1 p.2 (by omega) hl.1.2]
    have hinv_row2 : ∀ r : Row, permRow sw (permRow sw.reverse r) = r := by
      simpa using hinv_row_gen sw.reverse hvr
    have hinv_w : ∀ x : Nat, x < 2^256 → permWord sw.reverse (permWord sw x) = x := by
      intro x hx
      have h1 := permWord_eq_renameW sw hsv x hx
      have h2 := permWord_eq_renameW sw.reverse hvr (permWord sw x) (h1 ▸ renameW_lt _ x)
      rw [h2, h1]
      apply Nat.eq_of_testBit_eq; intro r
      by_cases hrr : r < 256
      · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
    have hfixr : permWord sw.reverse T = T := by
      have := hinv_w T hT; rwa [hfix] at this
    have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^256 := by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      rw [permWord_eq_renameW sw hsv x (hlt x hx)]
      exact renameW_lt _ x
    have hrot := rotate_impossible himp sw.reverse hvr hT hfixr hmap_lt
    have hback : (((choiceVal op :: rest).map (permWord sw)).map (permWord sw.reverse)) = (choiceVal op :: rest) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (choiceVal op :: rest)]
      exact List.map_congr_left fun x hx => hinv_w x (hlt x hx)
    rwa [hback] at hrot
abbrev FastPool := BoundPool × List Nat × List Nat × Nat
def prepPool (vals : List Nat) (c : BoundPool) : Option FastPool :=
  let miss := vals.filter (fun w => !availM c.dom c.pm w)
  if miss.length > 2 then none
  else
    let consts := vals.filter (isConstM c.dom)
    some (c, miss, consts, consts.length)
def fastPoolCut (fp : FastPool) (k a b z : Nat) (ka kb : Bool) : Bool :=
  let c := fp.1
  let miss := fp.2.1
  let consts := fp.2.2.1
  let totC := fp.2.2.2
  if !miss.all (fun m => (!ka && m == a) || (!kb && m == b)) then false
  else
    let dropA := if !ka && consts.contains a then 1 else 0
    let dropB := if !kb && consts.contains b then 1 else 0
    let base := c.lb + (totC - dropA - dropB)
    if k + c.paid >= base + 1 then false
    else
      let m := z &&& c.dom
      if m == 0 || m == c.dom then true
      else if k + c.paid >= base then false
      else
        let okAB := !miss.contains a && !miss.contains b
        if k + c.paid + 1 < base && okAB then true
        else
          let zIn := c.pm.contains m || c.pm.contains (c.dom ^^^ m)
          if zIn then true
          else decide (k + c.paid + 1 < base) && okAB
lemma countP_erase {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) {l : List α} {x : α} (hx : x ∈ l) :
    (l.erase x).countP p + (if p x then 1 else 0) = l.countP p := by
  have hp := List.perm_cons_erase hx
  have h1 := List.Perm.countP_eq p hp
  simp only [List.countP_cons] at h1
  omega
lemma countP_delTwo_fst (p : Nat → Bool) {ws : List Decor} {a b : Decor}
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map Prod.fst).countP p =
      (ws.map Prod.fst).countP p - (if !ka && p a.1 then 1 else 0) - (if !kb && p b.1 then 1 else 0) := by
  have hne : a ≠ b := fun e => hab (congrArg Prod.fst e)
  have hmap_erase : ∀ (l : List Decor) (x : Decor), (l.map Prod.fst).Nodup → x ∈ l →
      (l.erase x).map Prod.fst = (l.map Prod.fst).erase x.1 := by
    intro l x hnd hx
    induction l with
    | nil => simp at hx
    | cons y ys ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      by_cases hyx : y = x
      · subst hyx; simp
      · have hne1 : y.1 ≠ x.1 := by
          intro eq; apply hnd.1; rw [eq]
          exact List.mem_map_of_mem ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx))
        have h1 : (y == x) = false := beq_false_of_ne hyx
        have h2 : (y.1 == x.1) = false := beq_false_of_ne hne1
        simp only [List.erase_cons, h1, h2, List.map_cons]
        exact congrArg (y.1 :: ·) (ih hnd.2 ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx)))
  cases ka <;> cases kb
  · have hbm : b ∈ ws.erase a := (List.mem_erase_of_ne hne.symm).mpr hb
    have hnd1 : ((ws.erase a).map Prod.fst).Nodup := ((List.erase_sublist).map Prod.fst).nodup nd
    change (((ws.erase a).erase b).map Prod.fst).countP p = _
    rw [hmap_erase _ b hnd1 hbm, hmap_erase ws a nd ha]
    have ha1 : a.1 ∈ ws.map Prod.fst := List.mem_map_of_mem ha
    have hb1 : b.1 ∈ (ws.map Prod.fst).erase a.1 := (List.mem_erase_of_ne hab.symm).mpr (List.mem_map_of_mem hb)
    have c1 := countP_erase p ha1
    have c2 := countP_erase p hb1
    cases hpa : p a.1 <;> cases hpb : p b.1 <;> simp [hpa, hpb] at c1 c2 ⊢ <;> omega
  · change ((ws.erase a).map Prod.fst).countP p = _
    rw [hmap_erase ws a nd ha]
    have c1 := countP_erase p (List.mem_map_of_mem (f := Prod.fst) ha)
    cases hpa : p a.1 <;> simp [hpa] at c1 ⊢ <;> omega
  · change ((ws.erase b).map Prod.fst).countP p = _
    rw [hmap_erase ws b nd hb]
    have c1 := countP_erase p (List.mem_map_of_mem (f := Prod.fst) hb)
    cases hpb : p b.1 <;> simp [hpb] at c1 ⊢ <;> omega
  · simp [delTwo, delOne]
lemma fastPoolCut_sound {raw T ws a b d ka kb k c fp}
    (hP : ValidPool raw T c) (hprep : prepPool (ws.map Prod.fst) c = some fp)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1) (hd : d < 4)
    (ndc : (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).Nodup)
    (hcut : fastPoolCut fp k a.1 b.1 (bin d a.1 b.1) ka kb = true) :
    Impossible T k (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset := by
  unfold prepPool at hprep
  dsimp only at hprep
  split at hprep
  · simp at hprep
  · simp only [Option.some.injEq] at hprep
    subst hprep
    unfold fastPoolCut at hcut
    dsimp only at hcut
    split at hcut
    · simp at hcut
    · next hmiss =>
      simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, List.mem_filter, Bool.not_eq_true'] at hmiss
      have hsub := (delTwo_sub ws a b ka kb).map Prod.fst
      have h_all_avail : ((delTwo ws a b ka kb).map Prod.fst).all (availM c.dom c.pm) = true := by
        rw [List.all_eq_true]; intro w hw
        by_contra hna
        have hnf : availM c.dom c.pm w = false := Bool.eq_false_iff.mpr hna
        have hmem_ws : w ∈ ws.map Prod.fst := hsub.subset hw
        have hm := hmiss w ⟨hmem_ws, hnf⟩
        simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hm
        have hmem_del : ∀ u ∈ delTwo ws a b ka kb, u.1 = w → (ka = false → u ≠ a) ∧ (kb = false → u ≠ b) := by
          intro u hu _
          constructor
          · intro hka; subst hka
            have hsub1 : (delTwo ws a b false kb).Sublist (ws.erase a) := by
              cases kb <;> simp [delTwo, delOne, List.erase_sublist]
            have hu1 := hsub1.subset hu
            intro heq; subst heq
            exact List.Nodup.not_mem_erase (List.Nodup.of_map Prod.fst nd) hu1
          · intro hkb; subst hkb
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            have hnd2 : (delOne ws a ka).Nodup := by cases ka; exact hnd_ws.erase a; exact hnd_ws
            have h2 := List.Nodup.not_mem_erase hnd2 (a := b)
            exact fun heq => h2 (heq ▸ hu)
        obtain ⟨u, hu, huw⟩ := List.mem_map.mp hw
        have ⟨hna', hnb'⟩ := hmem_del u hu huw
        rcases hm with ⟨hka, hwa⟩ | ⟨hkb, hwb⟩
        · exact hna' hka (unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) ha (huw.trans hwa))
        · exact hnb' hkb (unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) hb (huw.trans hwb))
      have hcnt := countP_delTwo_fst (isConstM c.dom) nd ha hb hab ka kb
      have hlen_f : ((ws.map Prod.fst).filter (isConstM c.dom)).length = (ws.map Prod.fst).countP (isConstM c.dom) := by
        rw [List.countP_eq_length_filter]
      have hca : ((ws.map Prod.fst).filter (isConstM c.dom)).contains a.1 = isConstM c.dom a.1 := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.contains_iff_mem, List.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨List.mem_map_of_mem ha, h⟩⟩
      have hcb : ((ws.map Prod.fst).filter (isConstM c.dom)).contains b.1 = isConstM c.dom b.1 := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.contains_iff_mem, List.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨List.mem_map_of_mem hb, h⟩⟩
      have hma : (!((ws.map Prod.fst).filter (fun w => !availM c.dom c.pm w)).contains a.1) = availM c.dom c.pm a.1 := by
        cases h : availM c.dom c.pm a.1 <;> simp [List.contains_iff_mem, List.mem_filter, List.mem_map_of_mem ha, h]
      have hmb : (!((ws.map Prod.fst).filter (fun w => !availM c.dom c.pm w)).contains b.1) = availM c.dom c.pm b.1 := by
        cases h : availM c.dom c.pm b.1 <;> simp [List.contains_iff_mem, List.mem_filter, List.mem_map_of_mem hb, h]
      rw [hlen_f, hca, hcb, hma, hmb] at hcut
      apply scalarPoolCut_sound (op := (d, a.1, b.1)) (rest := (delTwo ws a b ka kb).map Prod.fst) hP ndc
      unfold scalarPoolCut choiceOK
      simp only [choiceVal, h_all_avail, Bool.and_true, List.countP_cons, Bool.and_eq_true, decide_eq_true_eq, hd, true_and]
      rw [hcnt]
      set z := bin d a.1 b.1
      set m := z &&& c.dom
      set restC := (ws.map Prod.fst).countP (isConstM c.dom) - (if !ka && isConstM c.dom a.1 then 1 else 0) - (if !kb && isConstM c.dom b.1 then 1 else 0)
      change (k + c.paid + (!availM c.dom c.pm z).toNat < c.lb + (restC + if isConstM c.dom z then 1 else 0)) ∧
        ((!(!availM c.dom c.pm z)) || (availM c.dom c.pm a.1 && availM c.dom c.pm b.1)) = true
      have hbase_le : ¬(k + c.paid ≥ c.lb + restC + 1) := by
        intro hge; simp only [hge, ↓reduceIte, Bool.false_eq_true] at hcut
      simp only [hbase_le, ↓reduceIte] at hcut
      by_cases hzc : (m == 0 || m == c.dom) = true
      · have hisc : isConstM c.dom z = true := hzc
        have havz : availM c.dom c.pm z = true := by
          unfold availM; dsimp only; rw [show (z &&& c.dom == 0 || z &&& c.dom == c.dom) = true from hzc]; simp
        simp only [hisc, havz, Bool.not_true, Bool.not_false, Bool.toNat_false, Bool.true_or, ite_true, and_true]
        omega
      · have hzc_f : (m == 0 || m == c.dom) = false := Bool.eq_false_iff.mpr hzc
        have hisc : isConstM c.dom z = false := hzc_f
        have hav_eq : availM c.dom c.pm z = (c.pm.contains m || c.pm.contains (c.dom ^^^ m)) := by
          unfold availM; dsimp only
          have hm0 : (m == 0) = false := by cases h1 : (m == 0) <;> simp [h1] at hzc_f ⊢
          have hmd : (m == c.dom) = false := by cases h1 : (m == c.dom) <;> simp [h1] at hzc_f ⊢
          change (m == 0 || m == c.dom || c.pm.contains m || c.pm.contains (c.dom ^^^ m)) = _
          simp [hm0, hmd]
        simp only [hzc_f, Bool.false_eq_true, ↓reduceIte] at hcut
        have hlt_b : ¬(k + c.paid ≥ c.lb + restC) := by
          intro hge; simp only [hge, ↓reduceIte, Bool.false_eq_true] at hcut
        simp only [hlt_b, ↓reduceIte] at hcut
        rw [hav_eq, hisc]
        simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
        by_cases hfast : (k + c.paid + 1 < c.lb + restC ∧ (availM c.dom c.pm a.1 && availM c.dom c.pm b.1) = true)
        · cases hpm : (c.pm.contains m || c.pm.contains (c.dom ^^^ m)) <;>
            simp only [Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false, Bool.true_or, Bool.false_or, hfast.2] <;>
            exact ⟨by omega, trivial⟩
        · have hfast_b : (decide (k + c.paid + 1 < c.lb + restC) && (availM c.dom c.pm a.1 && availM c.dom c.pm b.1)) = false := by
            rw [Bool.eq_false_iff]; intro h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            exact hfast ⟨h.1, (Bool.and_eq_true _ _).mpr h.2⟩
          simp only [hfast_b, Bool.false_eq_true, ↓reduceIte] at hcut
          cases hpm : (c.pm.contains m || c.pm.contains (c.dom ^^^ m))
          · simp only [hpm, Bool.false_eq_true, ↓reduceIte] at hcut
          · simp only [Bool.not_true, Bool.not_false, Bool.toNat_false, Bool.true_or]
            exact ⟨by omega, trivial⟩
def evalMoveBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 z.1 ka kb) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChildBT [] autos prevBks (cap - 1) rest (d, a.1, b.1)
def testPairBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  if n > cap + 1 then true else
  let z := dbin d a b
  if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
    let go := evalMoveBT cap n fmask ws cov fpools autos prevBks d a b z
    if n > cap then go false false
    else if n == cap then go false false && go true false && go false true
    else go false false && go true false && go false true && go true true
def testAllBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPairBT cap n fmask ws cov fpools autos prevBks a b)) &&
      testAllBT cap n fmask ws cov fpools autos prevBks bs
lemma evalMoveBT_sound {raw T pos neg ws fpools autos prevBks cap a b d ka kb}
    (hT : T < 2^256) (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^256)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (hcap : 0 < cap) (_hd : d < 4)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (hnz : bin d a.1 b.1 ≠ 0) (hfr : bin d a.1 b.1 ∉ ws.map Prod.fst)
    (test : evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d a b (dbin d a b) ka kb = true) :
    Impossible T (cap - 1) ((dbin d a b :: delTwo ws a b ka kb).map Prod.fst).toFinset := by
  let z := dbin d a b
  let rest := delTwo ws a b ka kb
  let child := (z :: rest).map Prod.fst
  have sub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : child.Nodup := by
    simp only [child, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => hfr ((sub.map Prod.fst).subset hm), (sub.map Prod.fst).nodup nd⟩
  have hltc : ∀ x ∈ child, x < 2^256 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx; exact hlt w (sub.subset hw)
  have hleq : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = child.length := by
    have hdl := delTwo_len ws a b ka kb ha hb ne
    simp only [child, rest, List.length_map, List.length_cons]
    omega
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k + 1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have hlen : child.length ≤ cap := by omega
  have hcov := cov_required gp (ws := z :: rest)
    (fun w hw => by rcases List.mem_cons.mp hw with rfl | hw; exact faithful_bin d (hf a ha) (hf b hb); exact hf w (sub.subset hw)) h
  have hcov_eq : (coverage (z :: rest)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z := by
    change dsep z ||| (coverage rest).1 = _
    rw [cov_delTwo a b ha hb ne ka kb, Nat.or_comm]
  rw [hcov_eq] at hcov
  have hcov_b : (((restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z) &&& fullMask pos.length) != fullMask pos.length) = false := by
    simp [hcov]
  unfold evalMoveBT at test
  dsimp only at test
  have hnotgt : ¬(child.length > cap) := by omega
  dsimp only [z] at hcov_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, Bool.false_eq_true] at test
  dsimp only [dbin] at test
  have hab1 : a.1 ≠ b.1 := fun eq => ne (unique_fst nd ha hb eq)
  by_cases hfp : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 (bin d a.1 b.1) ka kb) = true
  · obtain ⟨fp, hmem, hcut⟩ := List.any_eq_true.mp hfp
    have ⟨hv, hpr⟩ := hPools fp hmem
    exact fastPoolCut_sound hv hpr nd ha hb hab1 _hd ndc hcut k hk h
  · have hfp_f : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 (bin d a.1 b.1) ka kb) = false := Bool.eq_false_iff.mpr hfp
    simp only [hfp_f, Bool.false_eq_true, ↓reduceIte] at test
    exact closeChildBT_sound (raw := raw) (op := (d, a.1, b.1)) (rest := rest.map Prod.fst) hT (fun _ hm => (List.not_mem_nil hm).elim) hAutos hPrev ndc hltc test k hk h
lemma testAllBT_pair {cap n fmask ws cov fpools autos prevBks l}
    (h : testAllBT cap n fmask ws cov fpools autos prevBks l = true)
    {a b : Decor} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) :
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks a b d = true) ∨
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks b a d = true) := by
  induction l with
  | nil => simp at ha
  | cons w l ih =>
    simp only [testAllBT, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · have bm := (List.mem_cons.mp hb).resolve_left ne.symm
      exact Or.inl fun d hd => h.1 b bm d (by interval_cases d <;> decide)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr fun d hd => h.1 a ha' d (by interval_cases d <;> decide)
      · exact ih h.2 ha' hb'
lemma nodeBT_sound {raw T pos neg ws fpools autos prevBks cap}
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^256) (out : T ∉ ws.map Prod.fst)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (checks : cap = 0 ∨ testAllBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  rcases checks with rfl | hcheck
  · intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  by_cases h0 : cap = 0
  · subst h0
    intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  have hcap : 0 < cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne hnz hfr _
  obtain ⟨a, haW, rfl⟩ := List.mem_map.mp ha
  obtain ⟨b, hbW, rfl⟩ := List.mem_map.mp hb
  have ab : a ≠ b := fun e => ne (congrArg Prod.fst e)
  have one (x y : Decor) (d' : Nat) (hd' : d' < 4) (hx : x ∈ ws) (hy : y ∈ ws) (nxy : x.1 ≠ y.1)
      (k1 k2 : Bool) (hnz' : bin d' x.1 y.1 ≠ 0) (hfr' : bin d' x.1 y.1 ∉ ws.map Prod.fst)
      (ht : testPairBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks x y d' = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) x.1 y.1 d' k1 k2).toFinset := by
    rw [← delTwo_map_toFinset nd hx hy nxy d' k1 k2]
    have hem : evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d' x y (dbin d' x y) k1 k2 = true := by
      have hnz_b : (bin d' x.1 y.1 == 0) = false := beq_false_of_ne hnz'
      have hfr_b : (ws.any (fun v => v.1 == bin d' x.1 y.1)) = false := by
        rw [Bool.eq_false_iff]; intro h; obtain ⟨v, hv, heq⟩ := List.any_eq_true.mp h
        exact hfr' ((beq_iff_eq.mp heq) ▸ List.mem_map_of_mem hv)
      by_cases hlen : 1 + (ws.length - (if k1 then 0 else 1) - (if k2 then 0 else 1)) > cap
      · unfold evalMoveBT; simp [hlen]
      · unfold testPairBT at ht
        dsimp only [dbin] at ht
        have hnot1 : ¬(ws.length > cap + 1) := by cases k1 <;> cases k2 <;> simp at hlen <;> omega
        simp only [hnot1, ↓reduceIte, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at ht
        by_cases hgt : ws.length > cap
        · simp only [hgt, ↓reduceIte] at ht
          cases k1 <;> cases k2
          · exact ht
          · simp at hlen; omega
          · simp at hlen; omega
          · simp at hlen; omega
        · simp only [hgt, ↓reduceIte] at ht
          by_cases heq : ws.length = cap
          · simp only [heq, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at ht ⊢
            cases k1 <;> cases k2
            · exact ht.1.1
            · exact ht.2
            · exact ht.1.2
            · simp at hlen; omega
          · have hneq : (ws.length == cap) = false := beq_false_of_ne heq
            simp only [hneq, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at ht
            cases k1 <;> cases k2 <;> first | exact ht.1.1.1 | exact ht.1.2 | exact ht.1.1.2 | exact ht.2
    exact evalMoveBT_sound hT gp hf nd hlt hx hy (fun e => nxy (congrArg Prod.fst e)) hcap hd' hPools hAutos hPrev hnz' hfr' hem
  rcases testAllBT_pair hcheck haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb hnz hfr (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    have hfl := flipOp_lt hd
    exact one b a (flipOp d) hfl hbW haW ne.symm kb ka
      (bin_comm_flip d hd a.1 b.1 ▸ hnz) (bin_comm_flip d hd a.1 b.1 ▸ hfr) (hh _ hfl)
def buildWiresBT (depth : Nat) (base : List Decor) (steps : List (Nat × Nat × Nat)) : BT Decor :=
  let init := (base.length, btOfList depth base)
  (steps.foldl (fun p s =>
    let a := btGet (0, 0, 0) p.2 s.2.1
    let b := btGet (0, 0, 0) p.2 s.2.2
    (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 a b))) init).2
lemma buildWiresBT_faithful {depth pos neg base steps}
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^256) :
    btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) (buildWiresBT depth base steps) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^256 := ⟨faithful_zero pos neg, by decide⟩
  unfold buildWiresBT
  have h0 : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) (btOfList depth base) := btAll_ofList hbase
  have hgo : ∀ (ss : List (Nat × Nat × Nat)) (acc : Nat × BT Decor),
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) acc.2 →
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^256)
        (ss.foldl (fun p s => (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 (btGet (0, 0, 0) p.2 s.2.1) (btGet (0, 0, 0) p.2 s.2.2)))) acc).2 := by
    intro ss
    induction ss with
    | nil => intro acc hacc; exact hacc
    | cons s ss ih =>
      intro acc hacc
      have ha := btAll_get hacc hdef s.2.1
      have hb := btAll_get hacc hdef s.2.2
      exact ih _ (btAll_set hacc ⟨faithful_bin s.1 ha.1 hb.1, bin_lt s.1 _ _ ha.2 hb.2⟩)
  exact hgo steps (base.length, btOfList depth base) h0
def buildPoolsBT (pdepth : Nat) (W : BT Decor) (raw : List Nat) (slices : BT (Option (Nat × Nat)))
    (pspecs : List PoolSpec) : BT (Option BoundPool) :=
  btOfList pdepth (pspecs.map fun (slIdx, chIdxs) =>
    match btGet none slices slIdx with
    | none => none
    | some (dom, lb) =>
      let cs := chIdxs.map fun (op, ia, ib) => (op, (btGet (0, 0, 0) W ia).1, (btGet (0, 0, 0) W ib).1)
      materialize raw cs dom lb)
lemma buildPoolsBT_sound {pdepth} {W : BT Decor} {raw T} {slices : BT (Option (Nat × Nat))} {pspecs : List PoolSpec}
    (hSlices : btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices) :
    btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (buildPoolsBT pdepth W raw slices pspecs) := by
  apply btAll_ofList
  intro o ho c hc
  obtain ⟨⟨slIdx, chIdxs⟩, _, hmat⟩ := List.mem_map.mp ho
  dsimp only at hmat
  have hsl := btAll_get (d := none) hSlices (fun _ h => by simp at h) slIdx
  cases heq : btGet none slices slIdx with
  | none => rw [heq] at hmat; exact absurd (hmat.trans hc) (by simp)
  | some sl =>
    rw [heq] at hmat
    exact materialize_sound (hsl sl heq) (hmat.trans hc)
def nodupNats : List Nat → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && nodupNats xs
lemma nodupNats_sound : ∀ {l : List Nat}, nodupNats l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [nodupNats, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
    exact List.nodup_cons.mpr ⟨h.1, nodupNats_sound h.2⟩
def checkNodeBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (ns : NodeSpec) : Bool :=
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  let vals := ws.map Prod.fst
  let fpools := ns.2.1.filterMap fun pIdx =>
    match btGet none poolTable pIdx with
    | none => none
    | some c => prepPool vals c
  let nodeAutos := ns.2.2.map fun aIdx => btGet [] autosTable aIdx
  nodupNats vals && !(vals.contains T) &&
    (k == 0 || testAllBT k ws.length fmask ws (coverage ws) fpools nodeAutos prevBks ws)
def checkNodesBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (nodes : List NodeSpec) : Bool :=
  nodes.all (checkNodeBT W T fmask poolTable autosTable prevBks k)
lemma checkNodeBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k ns}
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (ok : checkNodeBT W T (fullMask pos.length) poolTable autosTable prevBks k ns = true) :
    Impossible T k ((ns.1.map fun idx => (btGet (0, 0, 0) W idx).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^256 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (btGet (0, 0, 0) W idx) ∧ (btGet (0, 0, 0) W idx).1 < 2^256 :=
    btAll_get hW hdef idx
  unfold checkNodeBT at ok
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (btGet (0, 0, 0) W idx).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply nodeBT_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    (nodupNats_sound ok.1.1)
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).2)
    (of_decide_eq_false ok.1.2)
    (fun fp hfp => by
      obtain ⟨pIdx, _, hmat⟩ := List.mem_filterMap.mp hfp
      cases heq : btGet none poolTable pIdx with
      | none => simp [heq] at hmat
      | some c =>
        simp only [heq] at hmat
        have hvc := btAll_get hPoolTable (fun _ h => by simp at h) pIdx c heq
        have hfp_eq : fp.1 = c := by
          unfold prepPool at hmat
          dsimp only at hmat
          split at hmat
          · simp at hmat
          · simp only [Option.some.injEq] at hmat; rw [← hmat]
        rw [hfp_eq]
        exact ⟨hvc, hmat⟩)
    (fun sw hsw => by
      obtain ⟨aIdx, _, rfl⟩ := List.mem_map.mp hsw
      exact btAll_get hAutos ⟨rfl, rfl⟩ aIdx)
    hPrev ok.2
def nodeValsBT (W : BT Decor) (ns : NodeSpec) : List Nat :=
  sortNats (ns.1.map fun idx => (btGet (0, 0, 0) W idx).1)
def buildBucketsBT (W : BT Decor) (nodes : List NodeSpec) : BT (List (List Nat)) :=
  nodes.foldl (fun acc ns =>
    let xs := nodeValsBT W ns
    btUpdate [] 6 acc (hashWs64 xs) (fun b => if b.contains xs then b else xs :: b)) BT.empty
lemma buildBucketsBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k}
    {nodes : List NodeSpec}
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes : checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (buildBucketsBT W nodes) := by
  have hmem : ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset := fun ns hns => by
    unfold nodeValsBT; rw [sortNats_toFinset]
    exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
  clear hNodes
  unfold buildBucketsBT
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := trivial
  generalize (BT.empty : BT (List (List Nat))) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    apply ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
    apply btAll_update hinit (fun _ h => (List.not_mem_nil h).elim)
    intro b hb ys hys
    split at hys
    · exact hb ys hys
    · rcases List.mem_cons.mp hys with rfl | hys'
      · exact hmem ns (List.mem_cons_self ..)
      · exact hb ys hys'
lemma lower_of_forestBT {roots T cap} {topBks : BT (List (List Nat))} {essPairs : List (Nat × Nat × Nat)}
    (ok : forestRootCheck roots T essPairs = true)
    (hTop : btAll (fun bk => ∀ xs ∈ bk, Impossible T cap xs.toFinset) topBks)
    (hRoot : bucketContainsBT topBks roots = true) :
    Lower roots T (cap + 1) := by
  simp only [forestRootCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at ok
  obtain ⟨⟨hT, hR⟩, hess⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hEss' : ∀ a ∈ roots, Essential T roots a := fun a ha => by
    obtain ⟨⟨v, r, s⟩, _, rfl, he⟩ := hess a ha
    exact checkEss1_sound he
  have hImp : Impossible T cap (sortNats roots).toFinset := by
    unfold bucketContainsBT at hRoot
    exact btAll_get hTop (fun _ h => (List.not_mem_nil h).elim) _ _ (List.contains_iff_mem.mp hRoot)
  rw [sortNats_toFinset] at hImp
  exact lower_of_impossible p1 p2 p3 hR' hEss' hImp
def buildPoolsSubBT (pdepth : Nat) (W : BT Decor) (raw : List Nat) (slices : BT (Option (Nat × Nat)))
    (pspecs : BT (Option PoolSpec)) (used : List Nat) : BT (Option BoundPool) :=
  used.foldl (fun acc pIdx =>
    match btGet none pspecs pIdx with
    | none => acc
    | some (slIdx, chIdxs) =>
      match btGet none slices slIdx with
      | none => acc
      | some (dom, lb) =>
        let cs := chIdxs.map fun (op, ia, ib) => (op, (btGet (0, 0, 0) W ia).1, (btGet (0, 0, 0) W ib).1)
        btSet pdepth acc pIdx (materialize raw cs dom lb)) BT.empty
lemma buildPoolsSubBT_sound {pdepth} {W : BT Decor} {raw T} {slices : BT (Option (Nat × Nat))}
    {pspecs : BT (Option PoolSpec)} {used : List Nat}
    (hSlices : btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices) :
    btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (buildPoolsSubBT pdepth W raw slices pspecs used) := by
  unfold buildPoolsSubBT
  have hinit : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (BT.empty : BT (Option BoundPool)) := trivial
  generalize (BT.empty : BT (Option BoundPool)) = acc at hinit ⊢
  induction used generalizing acc with
  | nil => exact hinit
  | cons pIdx rest ih =>
    apply ih
    dsimp only
    cases hps : btGet none pspecs pIdx with
    | none => simp only [hps]; exact hinit
    | some spec =>
      cases hsl : btGet none slices spec.1 with
      | none => simp only [hps, hsl]; exact hinit
      | some sl =>
        simp only [hps, hsl]
        apply btAll_set hinit
        intro c hc
        exact materialize_sound (btAll_get (d := none) hSlices (fun _ h => by simp at h) spec.1 sl hsl) hc
lemma checkNodesBT_mem {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k nodes}
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes : checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset := by
  intro ns hns
  unfold nodeValsBT; rw [sortNats_toFinset]
  exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
lemma forall_append {α : Type} {P : α → Prop} {l1 l2 : List α}
    (h1 : ∀ x ∈ l1, P x) (h2 : ∀ x ∈ l2, P x) : ∀ x ∈ l1 ++ l2, P x := by
  intro x hx; rcases List.mem_append.mp hx with h | h; exact h1 x h; exact h2 x h
lemma buildBucketsBT_of_mem {W : BT Decor} {T k nodes}
    (hmem : ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (buildBucketsBT W nodes) := by
  unfold buildBucketsBT
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := trivial
  generalize (BT.empty : BT (List (List Nat))) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    apply ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
    apply btAll_update hinit (fun _ h => (List.not_mem_nil h).elim)
    intro b hb ys hys
    split at hys
    · exact hb ys hys
    · rcases List.mem_cons.mp hys with rfl | hys'
      · exact hmem ns (List.mem_cons_self ..)
      · exact hb ys hys'
def checkTiersBT (W : BT Decor) (T fmask : Nat) (P : BT (Option BoundPool))
    (autos : BT (List (Nat × Nat))) : Nat → BT (List (List Nat)) → List (List NodeSpec) → Option (BT (List (List Nat)))
  | _, prev, [] => some prev
  | k, prev, t :: ts =>
    if checkNodesBT W T fmask P autos prev k t then
      checkTiersBT W T fmask P autos (k + 1) (buildBucketsBT W t) ts
    else none
def checkForestBT (W : BT Decor) (T fmask : Nat) (P : BT (Option BoundPool))
    (autos : BT (List (Nat × Nat))) (tiers : List (List NodeSpec)) (roots : List Nat) : Bool :=
  match checkTiersBT W T fmask P autos 0 BT.empty tiers with
  | none => false
  | some topBks => bucketContainsBT topBks roots
lemma checkTiersBT_sound {W : BT Decor} {raw pos neg T P autos}
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
    (hP : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) P)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autos) :
    ∀ (tiers : List (List NodeSpec)) (k : Nat) (prev res : BT (List (List Nat))),
      btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prev →
      checkTiersBT W T (fullMask pos.length) P autos k prev tiers = some res →
      btAll (fun bk => ∀ xs ∈ bk, Impossible T (k + tiers.length - 1) xs.toFinset) res
  | [], k, prev, res, hprev, h => by
    simp only [checkTiersBT, Option.some.injEq] at h
    subst h; simpa using hprev
  | t :: ts, k, prev, res, hprev, h => by
    unfold checkTiersBT at h
    split at h
    · next hchk =>
      have hnext := buildBucketsBT_sound hT gp hW hP hAutos hprev hchk
      have hres := checkTiersBT_sound hT gp hW hP hAutos ts (k + 1) (buildBucketsBT W t) res (by simpa using hnext) h
      have heq : k + 1 + ts.length - 1 = k + (t :: ts).length - 1 := by simp
      rwa [heq] at hres
    · simp at h
lemma lower_of_checkForestBT {W : BT Decor} {raw pos neg T P autos tiers} {essPairs : List (Nat × Nat × Nat)}
    (hne : tiers.length > 0)
    (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
    (hP : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) P)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autos)
    (okRoot : forestRootCheck raw T essPairs = true)
    (okForest : checkForestBT W T (fullMask pos.length) P autos tiers raw = true) :
    Lower raw T tiers.length := by
  have hTlt : T < 2^256 := by
    simp only [forestRootCheck, Bool.and_eq_true] at okRoot
    exact (checkProper_sound okRoot.1.1).2.1
  unfold checkForestBT at okForest
  cases hres : checkTiersBT W T (fullMask pos.length) P autos 0 BT.empty tiers with
  | none => simp [hres] at okForest
  | some topBks =>
    simp only [hres] at okForest
    have htop := checkTiersBT_sound hTlt gp hW hP hAutos tiers 0 BT.empty topBks trivial hres
    have hlow := lower_of_forestBT okRoot (by simpa using htop) okForest
    have heq : tiers.length - 1 + 1 = tiers.length := by omega
    rwa [heq] at hlow
def G_17 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000
def R_17 : List Nat := varsOf 17
lemma low_17_ok : countCheck R_17 G_17 1 [(VAR 0,17,16),(VAR 4,17,1)] = true := by decide +kernel
lemma low_17 : Lower R_17 G_17 1 := count_of low_17_ok
def G_18 : Nat := 0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000
def R_18 : List Nat := varsOf 18
lemma low_18_ok : carryOK [(0,1)] R_18 G_18 R_17 G_17 = true := by decide +kernel
lemma low_18 : Lower R_18 G_18 1 := carry_of low_18_ok low_17
def G_33 : Nat := 0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000
def R_33 : List Nat := varsOf 33
lemma low_33_ok : carryOK [(4,5)] R_33 G_33 R_17 G_17 = true := by decide +kernel
lemma low_33 : Lower R_33 G_33 1 := carry_of low_33_ok low_17
def G_36 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000
def R_36 : List Nat := varsOf 36
lemma low_36_ok : carryOK [(4,5),(0,2),(0,1)] R_36 G_36 R_17 G_17 = true := by decide +kernel
lemma low_36 : Lower R_36 G_36 1 := carry_of low_36_ok low_17
def G_68 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f00000000000000000
def R_68 : List Nat := varsOf 68
lemma low_68_ok : carryOK [(4,6),(4,5),(0,2),(0,1)] R_68 G_68 R_17 G_17 = true := by decide +kernel
lemma low_68 : Lower R_68 G_68 1 := carry_of low_68_ok low_17
def G_130 : Nat := 0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000
def R_130 : List Nat := varsOf 130
lemma low_130_ok : carryOK [(4,7),(4,6),(4,5),(0,1)] R_130 G_130 R_17 G_17 = true := by decide +kernel
lemma low_130 : Lower R_130 G_130 1 := carry_of low_130_ok low_17
def G_192 : Nat := 0xffffffffffffffff000000000000000000000000000000000000000000000000
def R_192 : List Nat := varsOf 192
lemma low_192_ok : carryOK [(0,4),(0,7),(4,6),(0,5),(0,3),(0,2),(0,1)] R_192 G_192 R_17 G_17 = true := by decide +kernel
lemma low_192 : Lower R_192 G_192 1 := carry_of low_192_ok low_17
def G_19 : Nat := 0xeeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee0000
def R_19 : List Nat := varsOf 19
lemma low_19_ok : liftCheck 1 0 R_19 G_19 R_18 G_18 [(VAR 0,17,16)] = true := by decide +kernel
lemma low_19 : Lower R_19 G_19 2 := lift_of low_19_ok low_18
def G_146 : Nat := 0xffffccccffffccccffffccccffffcccccccc0000cccc0000cccc0000cccc0000
def R_146 : List Nat := varsOf 146
def pos_146 : List Nat := [18,18,130,130,144,144,18,130,144,18,130,144]
def neg_146 : List Nat := [2,16,2,128,16,128,128,16,2,0,0,0]
def fmask_146 : Nat := fullMask 12
def base_146 : List Decor := [(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x6cf,0x105),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xb73,0x92),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xdbc,0x68)]
def steps_146 : List (Nat × Nat × Nat) := []
def W_146 : BT Decor := buildWiresBT 2 base_146 steps_146
def autosL_146 : List (List (Nat × Nat)) := []
def autos_146 : BT (List (Nat × Nat)) := btOfList 1 autosL_146
def slicesL_146 : List (Option (Nat × Nat)) := []
def slices_146 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_146
lemma gp_146 : goodPairs G_146 pos_146 neg_146 := goodPairs_of (by decide +kernel)
lemma base_146_ok : ∀ x ∈ base_146, faithful pos_146 neg_146 x ∧ x.1 < 2^256 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_146_ok : btAll (fun x => faithful pos_146 neg_146 x ∧ x.1 < 2^256) W_146 := buildWiresBT_faithful base_146_ok
set_option maxRecDepth 500000 in
lemma autos_146_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_146 = G_146) autos_146 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_146_ok : btAll (fun o => ∀ p, o = some p → Slice R_146 G_146 p.1 p.2) slices_146 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_146 G_146 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
def P_146 := buildPoolsBT 1 W_146 R_146 slices_146 []
def T_146 : List (List NodeSpec) := [[],[],[],[([0,1,2],[],[])]]
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma low_146 : Lower R_146 G_146 4 := lower_of_checkForestBT (by decide) gp_146 W_146_ok (buildPoolsBT_sound slices_146_ok) autos_146_ok (by decide +kernel : forestRootCheck R_146 G_146 [(VAR 1,18,16),(VAR 4,18,2),(VAR 7,130,2)] = true) (by decide +kernel : checkForestBT W_146 G_146 fmask_146 P_146 autos_146 T_146 R_146 = true)
def G_37 : Nat := 0xfafafafa00000000fafafafa00000000fafafafa00000000fafafafa00000000
def R_37 : List Nat := varsOf 37
lemma low_37_ok : carryOK [(4,5),(1,2)] R_37 G_37 R_19 G_19 = true := by decide +kernel
lemma low_37 : Lower R_37 G_37 2 := carry_of low_37_ok low_19
def G_49 : Nat := 0xaaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000
def R_49 : List Nat := varsOf 49
lemma low_49_ok : carryOK [(1,5),(1,3),(1,2),(0,4)] R_49 G_49 R_19 G_19 = true := by decide +kernel
lemma low_49 : Lower R_49 G_49 2 := carry_of low_49_ok low_19
def G_70 : Nat := 0xfcfcfcfcfcfcfcfc0000000000000000fcfcfcfcfcfcfcfc0000000000000000
def R_70 : List Nat := varsOf 70
lemma low_70_ok : carryOK [(4,6),(4,5),(0,1),(0,2)] R_70 G_70 R_19 G_19 = true := by decide +kernel
lemma low_70 : Lower R_70 G_70 2 := carry_of low_70_ok low_19
def G_82 : Nat := 0xcccccccccccccccccccc0000cccc0000cccccccccccccccccccc0000cccc0000
def R_82 : List Nat := varsOf 82
lemma low_82_ok : carryOK [(1,6),(0,1),(0,5),(0,3),(1,4),(0,2)] R_82 G_82 R_19 G_19 = true := by decide +kernel
lemma low_82 : Lower R_82 G_82 2 := carry_of low_82_ok low_19
def G_100 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000
def R_100 : List Nat := varsOf 100
lemma low_100_ok : carryOK [(0,1),(0,6),(1,5),(0,4),(1,3),(0,2)] R_100 G_100 R_19 G_19 = true := by decide +kernel
lemma low_100 : Lower R_100 G_100 2 := carry_of low_100_ok low_19
def G_145 : Nat := 0xffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa0000
def R_145 : List Nat := varsOf 145
lemma low_145_ok : carryOK [(1,7),(1,6),(1,5),(1,3),(1,2)] R_145 G_145 R_19 G_19 = true := by decide +kernel
lemma low_145 : Lower R_145 G_145 2 := carry_of low_145_ok low_19
def G_194 : Nat := 0xffffffffffffffffcccccccccccccccccccccccccccccccc0000000000000000
def R_194 : List Nat := varsOf 194
lemma low_194_ok : carryOK [(4,6),(4,5)] R_194 G_194 R_146 G_146 = true := by decide +kernel
lemma low_194 : Lower R_194 G_194 4 := carry_of low_194_ok low_146
def G_196 : Nat := 0xffffffffffffffff0000000000000000f0f0f0f0f0f0f0f00000000000000000
def R_196 : List Nat := varsOf 196
lemma low_196_ok : carryOK [(1,7),(4,6),(1,5),(1,3),(0,2)] R_196 G_196 R_19 G_19 = true := by decide +kernel
lemma low_196 : Lower R_196 G_196 2 := carry_of low_196_ok low_19
def G_200 : Nat := 0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff000000000000000000
def R_200 : List Nat := varsOf 200
lemma low_200_ok : carryOK [(4,6),(4,5),(1,3),(1,2)] R_200 G_200 R_146 G_146 = true := by decide +kernel
lemma low_200 : Lower R_200 G_200 4 := carry_of low_200_ok low_146
def G_51 : Nat := 0xeeeeaaaaeeee0000eeeeaaaaeeee0000eeeeaaaaeeee0000eeeeaaaaeeee0000
def R_51 : List Nat := varsOf 51
def pos_51 : List Nat := [17,17,18,18,18,33,33,33,17,17,18,33,17,17,18,18,33,33]
def neg_51 : List Nat := [3,48,3,34,48,3,34,48,34,0,0,0,1,16,2,16,1,32]
def fmask_51 : Nat := fullMask 18
def base_51 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x33be3,0x11025),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xc41c,0x416d),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xf71f,0xa092),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x308e0,0x201da)]
def steps_51 : List (Nat × Nat × Nat) := []
def W_51 : BT Decor := buildWiresBT 2 base_51 steps_51
def autosL_51 : List (List (Nat × Nat)) := []
def autos_51 : BT (List (Nat × Nat)) := btOfList 1 autosL_51
def slicesL_51 : List (Option (Nat × Nat)) := []
def slices_51 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_51
lemma gp_51 : goodPairs G_51 pos_51 neg_51 := goodPairs_of (by decide +kernel)
lemma base_51_ok : ∀ x ∈ base_51, faithful pos_51 neg_51 x ∧ x.1 < 2^256 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_51_ok : btAll (fun x => faithful pos_51 neg_51 x ∧ x.1 < 2^256) W_51 := buildWiresBT_faithful base_51_ok
set_option maxRecDepth 500000 in
lemma autos_51_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_51 = G_51) autos_51 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_51_ok : btAll (fun o => ∀ p, o = some p → Slice R_51 G_51 p.1 p.2) slices_51 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_51 G_51 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
def P_51 := buildPoolsBT 1 W_51 R_51 slices_51 []
def T_51 : List (List NodeSpec) := [[],[],[],[([0,1,2,3],[],[])]]
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma low_51 : Lower R_51 G_51 4 := lower_of_checkForestBT (by decide) gp_51 W_51_ok (buildPoolsBT_sound slices_51_ok) autos_51_ok (by decide +kernel : forestRootCheck R_51 G_51 [(VAR 0,17,16),(VAR 1,18,16),(VAR 4,17,1),(VAR 5,33,1)] = true) (by decide +kernel : checkForestBT W_51 G_51 fmask_51 P_51 autos_51 T_51 R_51 = true)
def G_147 : Nat := 0xffffccccffffccccffffccccffffcccceeee0000eeee0000eeee0000eeee0000
def R_147 : List Nat := varsOf 147
lemma low_147_ok : liftCheck 1 0 R_147 G_147 R_146 G_146 [(VAR 0,17,16)] = true := by decide +kernel
lemma low_147 : Lower R_147 G_147 5 := lift_of low_147_ok low_146
def G_202 : Nat := 0xffffffffffffffffffccffccffccffccffccffccffccffcc0000000000000000
def R_202 : List Nat := varsOf 202
lemma low_202_ok : liftCheck 2 0 R_202 G_202 R_200 G_200 [(VAR 1,66,64)] = true := by decide +kernel
lemma low_202 : Lower R_202 G_202 5 := lift_of low_202_ok low_200
def G_53 : Nat := 0xfafafafaaaaa0000fafafafaaaaa0000fafafafaaaaa0000fafafafaaaaa0000
def R_53 : List Nat := varsOf 53
lemma low_53_ok : carryOK [(4,5),(1,2)] R_53 G_53 R_51 G_51 = true := by decide +kernel
lemma low_53 : Lower R_53 G_53 4 := carry_of low_53_ok low_51
def G_83 : Nat := 0xeeeecccceeeecccceeee0000eeee0000eeeecccceeeecccceeee0000eeee0000
def R_83 : List Nat := varsOf 83
lemma low_83_ok : carryOK [(5,6),(0,1)] R_83 G_83 R_51 G_51 = true := by decide +kernel
lemma low_83 : Lower R_83 G_83 4 := carry_of low_83_ok low_51
def G_86 : Nat := 0xfcfcfcfcfcfcfcfccccc0000cccc0000fcfcfcfcfcfcfcfccccc0000cccc0000
def R_86 : List Nat := varsOf 86
lemma low_86_ok : carryOK [(4,6),(4,5),(0,1),(0,2)] R_86 G_86 R_51 G_51 = true := by decide +kernel
lemma low_86 : Lower R_86 G_86 4 := carry_of low_86_ok low_51
def G_101 : Nat := 0xfafafafaf0f0f0f0fafafafa00000000fafafafaf0f0f0f0fafafafa00000000
def R_101 : List Nat := varsOf 101
lemma low_101_ok : carryOK [(4,5),(4,6),(0,2),(0,1)] R_101 G_101 R_51 G_51 = true := by decide +kernel
lemma low_101 : Lower R_101 G_101 4 := carry_of low_101_ok low_51
def G_102 : Nat := 0xfcfcfcfcfcfcfcfcf0f0f0f000000000fcfcfcfcfcfcfcfcf0f0f0f000000000
def R_102 : List Nat := varsOf 102
lemma low_102_ok : carryOK [(4,6),(0,2)] R_102 G_102 R_51 G_51 = true := by decide +kernel
lemma low_102 : Lower R_102 G_102 4 := carry_of low_102_ok low_51
def G_177 : Nat := 0xffffaaaaffff0000ffffaaaaffff0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000
def R_177 : List Nat := varsOf 177
lemma low_177_ok : carryOK [(1,7),(1,6),(1,3),(1,2)] R_177 G_177 R_51 G_51 = true := by decide +kernel
lemma low_177 : Lower R_177 G_177 4 := carry_of low_177_ok low_51
def G_198 : Nat := 0xffffffffffffffffccccccccccccccccfcfcfcfcfcfcfcfc0000000000000000
def R_198 : List Nat := varsOf 198
lemma low_198_ok : carryOK [(4,6),(4,5),(0,2)] R_198 G_198 R_147 G_147 = true := by decide +kernel
lemma low_198 : Lower R_198 G_198 5 := carry_of low_198_ok low_147
def G_209 : Nat := 0xffffffffffffffffffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa0000
def R_209 : List Nat := varsOf 209
lemma low_209_ok : carryOK [(4,7),(0,4),(1,6),(1,3),(1,2),(0,5)] R_209 G_209 R_51 G_51 = true := by decide +kernel
lemma low_209 : Lower R_209 G_209 4 := carry_of low_209_ok low_51
def G_210 : Nat := 0xffffffffffffffffffffccccffffcccccccccccccccccccccccc0000cccc0000
def R_210 : List Nat := varsOf 210
lemma low_210_ok : carryOK [(1,3),(3,4),(1,6)] R_210 G_210 R_202 G_202 = true := by decide +kernel
lemma low_210 : Lower R_210 G_210 5 := carry_of low_210_ok low_202
def G_212 : Nat := 0xffffffffffffffffffff0000ffff0000f0f0f0f0f0f0f0f00000000000000000
def R_212 : List Nat := varsOf 212
lemma low_212_ok : carryOK [(0,4),(0,7),(1,4),(1,6),(0,5),(1,3),(0,2)] R_212 G_212 R_51 G_51 = true := by decide +kernel
lemma low_212 : Lower R_212 G_212 4 := carry_of low_212_ok low_51
def G_228 : Nat := 0xfffffffffffffffff0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000
def R_228 : List Nat := varsOf 228
lemma low_228_ok : carryOK [(1,4),(4,7),(1,6),(1,3),(0,2)] R_228 G_228 R_51 G_51 = true := by decide +kernel
lemma low_228 : Lower R_228 G_228 4 := carry_of low_228_ok low_51
def G_55 : Nat := 0xfefefafaeeee0000fefefafaeeee0000fefefafaeeee0000fefefafaeeee0000
def R_55 : List Nat := varsOf 55
lemma low_55_ok : liftCheck 2 0 R_55 G_55 R_53 G_53 [(VAR 1,18,16)] = true := by decide +kernel
lemma low_55 : Lower R_55 G_55 5 := lift_of low_55_ok low_53
def G_179 : Nat := 0xffffeeeeffffccccffffeeeeffffcccceeeeaaaaeeee0000eeeeaaaaeeee0000
def R_179 : List Nat := varsOf 179
def pos_179 : List Nat := [17,17,17,18,18,18,33,33,33,33,33,130,130,130,130,144,144,144,17,17,18,18,130,144,144,17,18,33,130,144,17,17,18,18,33,33,130,130,144,144]
def neg_179 : List Nat := [3,48,129,3,34,48,3,34,48,129,160,3,34,129,160,48,129,160,34,160,129,160,48,3,34,0,0,0,0,0,1,16,2,16,1,32,2,128,16,128]
def fmask_179 : Nat := fullMask 40
def base_179 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcca0c07c7,0x440912a4d),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x3314707838,0x11018418d9),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xc3e7bf803f,0x4280408122),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xc080007c0,0x8016ed5b2),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xf031c3f800,0xa0003b6604)]
def steps_179 : List (Nat × Nat × Nat) := [(3,1,2),(1,1,2),(1,1,4),(1,0,1),(2,6,4)]
def W_179 : BT Decor := buildWiresBT 4 base_179 steps_179
def autosL_179 : List (List (Nat × Nat)) := [[],[(1,7)]]
def autos_179 : BT (List (Nat × Nat)) := btOfList 1 autosL_179
def slicesL_179 : List (Option (Nat × Nat)) := [some (subcubeFast 0 32,5),some (subcubeFast 32 0,5),some (subcubeFast 0 2,3),some (subcubeFast 128 0,4),some (subcubeFast 2 0,4),some (subcubeFast 1 0,4),some (subcubeFast 0 128,3),some (subcubeFast 1 32,4),some (subcubeFast 33 0,4)]
def slices_179 : BT (Option (Nat × Nat)) := btOfList 4 slicesL_179
lemma gp_179 : goodPairs G_179 pos_179 neg_179 := goodPairs_of (by decide +kernel)
lemma base_179_ok : ∀ x ∈ base_179, faithful pos_179 neg_179 x ∧ x.1 < 2^256 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_179_ok : btAll (fun x => faithful pos_179 neg_179 x ∧ x.1 < 2^256) W_179 := buildWiresBT_faithful base_179_ok
set_option maxRecDepth 500000 in
lemma autos_179_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_179 = G_179) autos_179 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_179_0_ok : sliceCheck 0 32 1 R_179 G_179 (varsOf 147) R_146 G_146 4 [(VAR 0,1,0)] 5 = true := by decide +kernel
lemma sl_179_0 : Slice R_179 G_179 (subcubeFast 0 32) 5 := slice_fast_of sl_179_0_ok (fun _ => low_146)
lemma sl_179_1_ok : sliceCheck 32 0 0 R_179 G_179 (varsOf 147) R_147 G_147 5 [] 5 = true := by decide +kernel
lemma sl_179_1 : Slice R_179 G_179 (subcubeFast 32 0) 5 := slice_fast_of sl_179_1_ok (fun _ => low_147)
lemma sl_179_2_ok : sliceCheck 0 2 144 R_179 G_179 (varsOf 177) R_33 G_33 1 [(VAR 4,16,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_179_2 : Slice R_179 G_179 (subcubeFast 0 2) 3 := slice_fast_of sl_179_2_ok (fun _ => low_33)
lemma sl_179_3_ok : sliceCheck 128 0 0 R_179 G_179 (varsOf 51) R_51 G_51 4 [] 4 = true := by decide +kernel
lemma sl_179_3 : Slice R_179 G_179 (subcubeFast 128 0) 4 := slice_fast_of sl_179_3_ok (fun _ => low_51)
lemma sl_179_4_ok : sliceCheck 2 0 0 R_179 G_179 (varsOf 177) R_177 G_177 4 [] 4 = true := by decide +kernel
lemma sl_179_4 : Slice R_179 G_179 (subcubeFast 2 0) 4 := slice_fast_of sl_179_4_ok (fun _ => low_177)
lemma sl_179_5_ok : sliceCheck 1 0 32 R_179 G_179 (varsOf 178) R_146 G_146 4 [] 4 = true := by decide +kernel
lemma sl_179_5 : Slice R_179 G_179 (subcubeFast 1 0) 4 := slice_fast_of sl_179_5_ok (fun _ => low_146)
lemma sl_179_6_ok : sliceCheck 0 128 18 R_179 G_179 (varsOf 51) R_33 G_33 1 [(VAR 1,2,0),(VAR 4,16,0)] 3 = true := by decide +kernel
lemma sl_179_6 : Slice R_179 G_179 (subcubeFast 0 128) 3 := slice_fast_of sl_179_6_ok (fun _ => low_33)
lemma sl_179_7_ok : sliceCheck 1 32 0 R_179 G_179 (varsOf 146) R_146 G_146 4 [] 4 = true := by decide +kernel
lemma sl_179_7 : Slice R_179 G_179 (subcubeFast 1 32) 4 := slice_fast_of sl_179_7_ok (fun _ => low_146)
lemma sl_179_8_ok : sliceCheck 33 0 0 R_179 G_179 (varsOf 146) R_146 G_146 4 [] 4 = true := by decide +kernel
lemma sl_179_8 : Slice R_179 G_179 (subcubeFast 33 0) 4 := slice_fast_of sl_179_8_ok (fun _ => low_146)
set_option maxRecDepth 500000 in
lemma slices_179_ok : btAll (fun o => ∀ p, o = some p → Slice R_179 G_179 p.1 p.2) slices_179 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_179 G_179 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_179_0) (forall_cons (fun _ h => by cases h; exact sl_179_1) (forall_cons (fun _ h => by cases h; exact sl_179_2) (forall_cons (fun _ h => by cases h; exact sl_179_3) (forall_cons (fun _ h => by cases h; exact sl_179_4) (forall_cons (fun _ h => by cases h; exact sl_179_5) (forall_cons (fun _ h => by cases h; exact sl_179_6) (forall_cons (fun _ h => by cases h; exact sl_179_7) (forall_cons (fun _ h => by cases h; exact sl_179_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def P_179 := buildPoolsBT 3 W_179 R_179 slices_179 [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(6,[]),(7,[]),(8,[])]
def T_179 : List (List NodeSpec) := [[],[],[],[],[([9,0,1,2,3],[0],[])],[([5,0,1,2,3,4],[0,1],[]),([0,1,2,6,3,4],[2,3],[0]),([0,1,2,3,4,7],[2,4],[]),([1,8,2,3,4],[6,7,2,4,5],[])],[([0,1,2,3,4],[6,4,1,3],[0,1])]]
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma low_179 : Lower R_179 G_179 7 := lower_of_checkForestBT (by decide) gp_179 W_179_ok (buildPoolsBT_sound slices_179_ok) autos_179_ok (by decide +kernel : forestRootCheck R_179 G_179 [(VAR 0,17,16),(VAR 1,18,16),(VAR 4,17,1),(VAR 5,33,1),(VAR 7,130,2)] = true) (by decide +kernel : checkForestBT W_179 G_179 fmask_179 P_179 autos_179 T_179 R_179 = true)
def G_182 : Nat := 0xfffffcfcffffccccfffffcfcffffccccfcfcf0f0cccc0000fcfcf0f0cccc0000
def R_182 : List Nat := varsOf 182
def pos_182 : List Nat := [18,18,18,18,36,36,36,36,36,36,130,130,130,130,144,144,144,144,18,18,130,130,144,144,18,36,130,144,18,18,36,36,130,130,144,144]
def neg_182 : List Nat := [6,20,34,48,6,20,34,48,132,160,6,34,132,160,20,48,132,160,132,160,20,48,6,34,0,0,0,0,2,16,4,32,2,128,16,128]
def fmask_182 : Nat := fullMask 36
def base_182 : List Decor := [(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x3353c3c0f,0x110c00c55),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc20003f0,0x40555533),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xc39cfc00f,0x42030c0aa),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xc20003f0,0x80aaaacc),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xf0cf3fc00,0xa000f3300)]
def steps_182 : List (Nat × Nat × Nat) := []
def W_182 : BT Decor := buildWiresBT 3 base_182 steps_182
def autosL_182 : List (List (Nat × Nat)) := []
def autos_182 : BT (List (Nat × Nat)) := btOfList 1 autosL_182
def slicesL_182 : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,5)]
def slices_182 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_182
lemma gp_182 : goodPairs G_182 pos_182 neg_182 := goodPairs_of (by decide +kernel)
lemma base_182_ok : ∀ x ∈ base_182, faithful pos_182 neg_182 x ∧ x.1 < 2^256 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_182_ok : btAll (fun x => faithful pos_182 neg_182 x ∧ x.1 < 2^256) W_182 := buildWiresBT_faithful base_182_ok
set_option maxRecDepth 500000 in
lemma autos_182_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_182 = G_182) autos_182 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_182_0_ok : sliceCheck 0 4 32 R_182 G_182 (varsOf 178) R_146 G_146 4 [(VAR 5,32,0)] 5 = true := by decide +kernel
lemma sl_182_0 : Slice R_182 G_182 (subcubeFast 0 4) 5 := slice_fast_of sl_182_0_ok (fun _ => low_146)
set_option maxRecDepth 500000 in
lemma slices_182_ok : btAll (fun o => ∀ p, o = some p → Slice R_182 G_182 p.1 p.2) slices_182 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_182 G_182 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_182_0) (fun _ h => (List.not_mem_nil h).elim))
def P_182 := buildPoolsBT 1 W_182 R_182 slices_182 [(0,[])]
def T_182 : List (List NodeSpec) := [[],[],[],[],[],[([0,1,2,3,4],[0],[])]]
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma low_182 : Lower R_182 G_182 6 := lower_of_checkForestBT (by decide) gp_182 W_182_ok (buildPoolsBT_sound slices_182_ok) autos_182_ok (by decide +kernel : forestRootCheck R_182 G_182 [(VAR 1,18,16),(VAR 2,36,32),(VAR 4,18,2),(VAR 5,36,4),(VAR 7,130,2)] = true) (by decide +kernel : checkForestBT W_182 G_182 fmask_182 P_182 autos_182 T_182 R_182 = true)
def G_211 : Nat := 0xffffffffffffffffffffccccffffcccceeeecccceeeecccceeee0000eeee0000
def R_211 : List Nat := varsOf 211
def pos_211 : List Nat := [17,17,17,17,18,18,66,66,66,130,130,144,144,192,192,192,18,18,66,130,130,144,144,192,17,18,66,130,144,192,17,17,18,18,66,66,130,130,144,144,192,192]
def neg_211 : List Nat := [3,65,80,129,3,80,3,65,80,3,129,80,129,65,80,129,65,129,129,65,80,3,65,3,0,0,0,0,0,0,1,16,2,16,2,64,2,128,16,128,64,128]
def fmask_211 : Nat := fullMask 42
def base_211 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xc100000f,0x40efb6db),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x3f0e1f07f0,0x1500a00251),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xc3d363183f,0x4280104924),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x30c2484e1c0,0x108005969a6),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0x3f038f8fe00,0x2a000069408)]
def steps_211 : List (Nat × Nat × Nat) := [(1,1,4),(3,3,5)]
def W_211 : BT Decor := buildWiresBT 3 base_211 steps_211
def autosL_211 : List (List (Nat × Nat)) := [[]]
def autos_211 : BT (List (Nat × Nat)) := btOfList 1 autosL_211
def slicesL_211 : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 1 0,5),some (subcubeFast 2 0,4),some (subcubeFast 64 0,5),some (subcubeFast 17 0,4),some (subcubeFast 128 0,4)]
def slices_211 : BT (Option (Nat × Nat)) := btOfList 3 slicesL_211
lemma gp_211 : goodPairs G_211 pos_211 neg_211 := goodPairs_of (by decide +kernel)
lemma base_211_ok : ∀ x ∈ base_211, faithful pos_211 neg_211 x ∧ x.1 < 2^256 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_211_ok : btAll (fun x => faithful pos_211 neg_211 x ∧ x.1 < 2^256) W_211 := buildWiresBT_faithful base_211_ok
set_option maxRecDepth 500000 in
lemma autos_211_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_211 = G_211) autos_211 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_211_0_ok : sliceCheck 0 1 16 R_211 G_211 (varsOf 210) R_194 G_194 4 [(VAR 4,16,0)] 5 = true := by decide +kernel
lemma sl_211_0 : Slice R_211 G_211 (subcubeFast 0 1) 5 := slice_fast_of sl_211_0_ok (fun _ => low_194)
lemma sl_211_1_ok : sliceCheck 1 0 0 R_211 G_211 (varsOf 210) R_210 G_210 5 [] 5 = true := by decide +kernel
lemma sl_211_1 : Slice R_211 G_211 (subcubeFast 1 0) 5 := slice_fast_of sl_211_1_ok (fun _ => low_210)
lemma sl_211_2_ok : sliceCheck 2 0 0 R_211 G_211 (varsOf 209) R_209 G_209 4 [] 4 = true := by decide +kernel
lemma sl_211_2 : Slice R_211 G_211 (subcubeFast 2 0) 4 := slice_fast_of sl_211_2_ok (fun _ => low_209)
lemma sl_211_3_ok : sliceCheck 64 0 0 R_211 G_211 (varsOf 147) R_147 G_147 5 [] 5 = true := by decide +kernel
lemma sl_211_3 : Slice R_211 G_211 (subcubeFast 64 0) 5 := slice_fast_of sl_211_3_ok (fun _ => low_147)
lemma sl_211_4_ok : sliceCheck 17 0 0 R_211 G_211 (varsOf 194) R_194 G_194 4 [] 4 = true := by decide +kernel
lemma sl_211_4 : Slice R_211 G_211 (subcubeFast 17 0) 4 := slice_fast_of sl_211_4_ok (fun _ => low_194)
lemma sl_211_5_ok : sliceCheck 128 0 0 R_211 G_211 (varsOf 83) R_83 G_83 4 [] 4 = true := by decide +kernel
lemma sl_211_5 : Slice R_211 G_211 (subcubeFast 128 0) 4 := slice_fast_of sl_211_5_ok (fun _ => low_83)
set_option maxRecDepth 500000 in
lemma slices_211_ok : btAll (fun o => ∀ p, o = some p → Slice R_211 G_211 p.1 p.2) slices_211 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_211 G_211 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_211_0) (forall_cons (fun _ h => by cases h; exact sl_211_1) (forall_cons (fun _ h => by cases h; exact sl_211_2) (forall_cons (fun _ h => by cases h; exact sl_211_3) (forall_cons (fun _ h => by cases h; exact sl_211_4) (forall_cons (fun _ h => by cases h; exact sl_211_5) (fun _ h => (List.not_mem_nil h).elim)))))))
def P_211 := buildPoolsBT 3 W_211 R_211 slices_211 [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])]
def T_211 : List (List NodeSpec) := [[],[],[],[],[([6,0,1,2,4],[0],[])],[([0,1,2,3,4,5],[0,1,2,3],[0])],[([0,1,2,3,4],[4,3,0,2,5],[0])]]
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma low_211 : Lower R_211 G_211 7 := lower_of_checkForestBT (by decide) gp_211 W_211_ok (buildPoolsBT_sound slices_211_ok) autos_211_ok (by decide +kernel : forestRootCheck R_211 G_211 [(VAR 0,17,16),(VAR 1,18,16),(VAR 4,17,1),(VAR 6,66,2),(VAR 7,130,2)] = true) (by decide +kernel : checkForestBT W_211 G_211 fmask_211 P_211 autos_211 T_211 R_211 = true)
def G_87 : Nat := 0xfefefcfcfefefcfceeee0000eeee0000fefefcfcfefefcfceeee0000eeee0000
def R_87 : List Nat := varsOf 87
lemma low_87_ok : carryOK [(5,6),(0,1)] R_87 G_87 R_55 G_55 = true := by decide +kernel
lemma low_87 : Lower R_87 G_87 5 := carry_of low_87_ok low_55
def G_103 : Nat := 0xfefefefefcfcfcfcfafafafa00000000fefefefefcfcfcfcfafafafa00000000
def R_103 : List Nat := varsOf 103
lemma low_103_ok : carryOK [(4,5),(4,6),(0,2),(0,1)] R_103 G_103 R_55 G_55 = true := by decide +kernel
lemma low_103 : Lower R_103 G_103 5 := carry_of low_103_ok low_55
def G_115 : Nat := 0xeeeeeeeeeeeecccceeeeaaaaeeee0000eeeeeeeeeeeecccceeeeaaaaeeee0000
def R_115 : List Nat := varsOf 115
lemma low_115_ok : carryOK [(2,6),(2,3),(1,5),(0,4)] R_115 G_115 R_55 G_55 = true := by decide +kernel
lemma low_115 : Lower R_115 G_115 5 := carry_of low_115_ok low_55
def G_117 : Nat := 0xfafafafafafaf0f0fafafafaaaaa0000fafafafafafaf0f0fafafafaaaaa0000
def R_117 : List Nat := varsOf 117
lemma low_117_ok : carryOK [(0,2),(0,1),(1,6),(2,5),(1,3),(0,4)] R_117 G_117 R_55 G_55 = true := by decide +kernel
lemma low_117 : Lower R_117 G_117 5 := carry_of low_117_ok low_55
def G_118 : Nat := 0xfcfcfcfcfcfcfcfcfcfcf0f0cccc0000fcfcfcfcfcfcfcfcfcfcf0f0cccc0000
def R_118 : List Nat := varsOf 118
lemma low_118_ok : carryOK [(0,6),(2,5),(1,4),(0,3)] R_118 G_118 R_55 G_55 = true := by decide +kernel
lemma low_118 : Lower R_118 G_118 5 := carry_of low_118_ok low_55
def G_181 : Nat := 0xfffffafaffff0000fffffafaffff0000fafafafaaaaa0000fafafafaaaaa0000
def R_181 : List Nat := varsOf 181
lemma low_181_ok : carryOK [(1,7),(1,6),(1,3)] R_181 G_181 R_55 G_55 = true := by decide +kernel
lemma low_181 : Lower R_181 G_181 5 := carry_of low_181_ok low_55
def G_213 : Nat := 0xffffffffffffffffffff0000ffff0000fafaf0f0fafaf0f0aaaa0000aaaa0000
def R_213 : List Nat := varsOf 213
lemma low_213_ok : carryOK [(0,5),(5,7),(0,6),(0,3),(0,1)] R_213 G_213 R_55 G_55 = true := by decide +kernel
lemma low_213 : Lower R_213 G_213 5 := carry_of low_213_ok low_55
def G_214 : Nat := 0xffffffffffffffffffffccccffffccccfcfcfcfcfcfcfcfccccc0000cccc0000
def R_214 : List Nat := varsOf 214
lemma low_214_ok : carryOK [(4,6),(0,2)] R_214 G_214 R_211 G_211 = true := by decide +kernel
lemma low_214 : Lower R_214 G_214 7 := carry_of low_214_ok low_211
def G_227 : Nat := 0xffffffffffffffffeeeeeeeecccccccceeeeeeeeccccccccaaaaaaaa00000000
def R_227 : List Nat := varsOf 227
lemma low_227_ok : carryOK [(4,6),(0,2)] R_227 G_227 R_182 G_182 = true := by decide +kernel
lemma low_227 : Lower R_227 G_227 6 := carry_of low_227_ok low_182
def G_229 : Nat := 0xfffffffffffffffffafafafa00000000fafafafaf0f0f0f0fafafafa00000000
def R_229 : List Nat := varsOf 229
lemma low_229_ok : carryOK [(2,5),(4,5),(4,7),(2,6),(0,2),(0,3),(0,1)] R_229 G_229 R_55 G_55 = true := by decide +kernel
lemma low_229 : Lower R_229 G_229 5 := carry_of low_229_ok low_55
def G_230 : Nat := 0xfffffffffffffffffcfcfcfcccccccccfcfcfcfcfcfcfcfcf0f0f0f000000000
def R_230 : List Nat := varsOf 230
lemma low_230_ok : carryOK [(4,6),(0,2)] R_230 G_230 R_179 G_179 = true := by decide +kernel
lemma low_230 : Lower R_230 G_230 7 := carry_of low_230_ok low_179
def G_241 : Nat := 0xffffffffffffffffffffaaaaffff0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000
def R_241 : List Nat := varsOf 241
lemma low_241_ok : carryOK [(1,5),(1,7),(2,6),(1,3),(0,4)] R_241 G_241 R_55 G_55 = true := by decide +kernel
lemma low_241 : Lower R_241 G_241 5 := carry_of low_241_ok low_55
def G_244 : Nat := 0xfffffffffffffffffffff0f0ffff0000f0f0f0f0f0f0f0f0f0f0f0f000000000
def R_244 : List Nat := varsOf 244
lemma low_244_ok : carryOK [(0,5),(1,5),(0,7),(2,4),(1,6),(0,3)] R_244 G_244 R_55 G_55 = true := by decide +kernel
lemma low_244 : Lower R_244 G_244 5 := carry_of low_244_ok low_55
def G_119 : Nat := 0xfefefefefefefcfcfefefafaeeee0000fefefefefefefcfcfefefafaeeee0000
def R_119 : List Nat := varsOf 119
def pos_119 : List Nat := [17,17,17,17,18,18,18,18,33,33,33,33,36,36,36,36,66,66,66,66,68,68,68,68,17,18,33,36,66,68,17,18,33,36,66,68,17,17,18,18,33,33,36,36,66,66,68,68]
def neg_119 : List Nat := [7,20,65,112,7,20,34,112,7,34,65,112,7,20,34,112,7,34,65,112,7,20,65,112,34,65,20,65,20,34,0,0,0,0,0,0,1,16,2,16,1,32,4,32,2,64,4,64]
def fmask_119 : Nat := fullMask 48
def base_119 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x33145000f0f,0x1100a551515),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x30c4920f00f0,0x104021135351),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcc0a28f0f000,0x440014313133),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xf0c30000ff,0xa014a8a8aa),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xf030c00ff00,0xa00218acac8),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xf00c30ff0000,0xa0000acc8c8c)]
def steps_119 : List (Nat × Nat × Nat) := [(1,0,5),(2,0,1),(2,0,5),(1,0,1),(1,1,4),(1,7,5),(2,9,3)]
def W_119 : BT Decor := buildWiresBT 4 base_119 steps_119
def autosL_119 : List (List (Nat × Nat)) := [[],[(4,5),(1,2)],[(5,6),(0,1)],[(4,5),(4,6),(0,2),(0,1)],[(2,5),(1,4),(0,6)],[(4,6),(4,5),(0,1),(0,2)],[(4,6),(0,2)],[(0,2),(0,1),(2,5),(1,6),(0,4)],[(2,6),(1,5),(0,4)],[(1,2),(0,1),(2,6),(1,4),(0,5)],[(2,4),(1,6),(0,5)],[(2,4),(1,5),(0,6)]]
def autos_119 : BT (List (Nat × Nat)) := btOfList 4 autosL_119
def slicesL_119 : List (Option (Nat × Nat)) := [some (subcubeFast 16 96,2),some (subcubeFast 0 112,2),some (subcubeFast 66 0,4),some (subcubeFast 0 2,4),some (subcubeFast 1 4,3),some (subcubeFast 17 0,4),some (subcubeFast 0 4,4),some (subcubeFast 0 1,4),some (subcubeFast 64 0,5),some (subcubeFast 1 0,5),some (subcubeFast 0 64,4),some (subcubeFast 4 3,2),some (subcubeFast 0 7,2),some (subcubeFast 2 0,5),some (subcubeFast 18 0,4),some (subcubeFast 33 0,4),some (subcubeFast 68 0,4),some (subcubeFast 16 0,5),some (subcubeFast 1 2,3),some (subcubeFast 0 32,4),some (subcubeFast 0 65,3),some (subcubeFast 4 0,5),some (subcubeFast 36 0,4)]
def slices_119 : BT (Option (Nat × Nat)) := btOfList 5 slicesL_119
lemma gp_119 : goodPairs G_119 pos_119 neg_119 := goodPairs_of (by decide +kernel)
lemma base_119_ok : ∀ x ∈ base_119, faithful pos_119 neg_119 x ∧ x.1 < 2^256 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_119_ok : btAll (fun x => faithful pos_119 neg_119 x ∧ x.1 < 2^256) W_119 := buildWiresBT_faithful base_119_ok
set_option maxRecDepth 500000 in
lemma autos_119_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_119 = G_119) autos_119 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_119_0_ok : sliceCheck 16 96 7 R_119 G_119 (varsOf 7) [] 0 0 [(VAR 0,1,0),(VAR 1,2,0),(VAR 2,4,0)] 2 = true := by decide +kernel
lemma sl_119_0 : Slice R_119 G_119 (subcubeFast 16 96) 2 := slice_fast_of sl_119_0_ok (fun h => (h rfl).elim)
lemma sl_119_1_ok : sliceCheck 0 112 7 R_119 G_119 (varsOf 7) [] 0 0 [(VAR 0,1,0),(VAR 1,2,0),(VAR 2,4,0)] 2 = true := by decide +kernel
lemma sl_119_1 : Slice R_119 G_119 (subcubeFast 0 112) 2 := slice_fast_of sl_119_1_ok (fun h => (h rfl).elim)
lemma sl_119_2_ok : sliceCheck 66 0 0 R_119 G_119 (varsOf 53) R_53 G_53 4 [] 4 = true := by decide +kernel
lemma sl_119_2 : Slice R_119 G_119 (subcubeFast 66 0) 4 := slice_fast_of sl_119_2_ok (fun _ => low_53)
lemma sl_119_3_ok : sliceCheck 0 2 80 R_119 G_119 (varsOf 117) R_37 G_37 2 [(VAR 4,16,0),(VAR 6,64,0)] 4 = true := by decide +kernel
lemma sl_119_3 : Slice R_119 G_119 (subcubeFast 0 2) 4 := slice_fast_of sl_119_3_ok (fun _ => low_37)
lemma sl_119_4_ok : sliceCheck 1 4 96 R_119 G_119 (varsOf 114) R_18 G_18 1 [(VAR 5,32,0),(VAR 6,64,0)] 3 = true := by decide +kernel
lemma sl_119_4 : Slice R_119 G_119 (subcubeFast 1 4) 3 := slice_fast_of sl_119_4_ok (fun _ => low_18)
lemma sl_119_5_ok : sliceCheck 17 0 0 R_119 G_119 (varsOf 102) R_102 G_102 4 [] 4 = true := by decide +kernel
lemma sl_119_5 : Slice R_119 G_119 (subcubeFast 17 0) 4 := slice_fast_of sl_119_5_ok (fun _ => low_102)
lemma sl_119_6_ok : sliceCheck 0 4 96 R_119 G_119 (varsOf 115) R_19 G_19 2 [(VAR 5,32,0),(VAR 6,64,0)] 4 = true := by decide +kernel
lemma sl_119_6 : Slice R_119 G_119 (subcubeFast 0 4) 4 := slice_fast_of sl_119_6_ok (fun _ => low_19)
lemma sl_119_7_ok : sliceCheck 0 1 48 R_119 G_119 (varsOf 118) R_70 G_70 2 [(VAR 4,16,0),(VAR 5,32,0)] 4 = true := by decide +kernel
lemma sl_119_7 : Slice R_119 G_119 (subcubeFast 0 1) 4 := slice_fast_of sl_119_7_ok (fun _ => low_70)
lemma sl_119_8_ok : sliceCheck 64 0 0 R_119 G_119 (varsOf 55) R_55 G_55 5 [] 5 = true := by decide +kernel
lemma sl_119_8 : Slice R_119 G_119 (subcubeFast 64 0) 5 := slice_fast_of sl_119_8_ok (fun _ => low_55)
lemma sl_119_9_ok : sliceCheck 1 0 0 R_119 G_119 (varsOf 118) R_118 G_118 5 [] 5 = true := by decide +kernel
lemma sl_119_9 : Slice R_119 G_119 (subcubeFast 1 0) 5 := slice_fast_of sl_119_9_ok (fun _ => low_118)
lemma sl_119_10_ok : sliceCheck 0 64 6 R_119 G_119 (varsOf 55) R_49 G_49 2 [(VAR 1,2,0),(VAR 2,4,0)] 4 = true := by decide +kernel
lemma sl_119_10 : Slice R_119 G_119 (subcubeFast 0 64) 4 := slice_fast_of sl_119_10_ok (fun _ => low_49)
lemma sl_119_11_ok : sliceCheck 4 3 112 R_119 G_119 (varsOf 112) [] 0 0 [(VAR 4,16,0),(VAR 5,32,0),(VAR 6,64,0)] 2 = true := by decide +kernel
lemma sl_119_11 : Slice R_119 G_119 (subcubeFast 4 3) 2 := slice_fast_of sl_119_11_ok (fun h => (h rfl).elim)
lemma sl_119_12_ok : sliceCheck 0 7 112 R_119 G_119 (varsOf 112) [] 0 0 [(VAR 4,16,0),(VAR 5,32,0),(VAR 6,64,0)] 2 = true := by decide +kernel
lemma sl_119_12 : Slice R_119 G_119 (subcubeFast 0 7) 2 := slice_fast_of sl_119_12_ok (fun h => (h rfl).elim)
lemma sl_119_13_ok : sliceCheck 2 0 0 R_119 G_119 (varsOf 117) R_117 G_117 5 [] 5 = true := by decide +kernel
lemma sl_119_13 : Slice R_119 G_119 (subcubeFast 2 0) 5 := slice_fast_of sl_119_13_ok (fun _ => low_117)
lemma sl_119_14_ok : sliceCheck 18 0 0 R_119 G_119 (varsOf 101) R_101 G_101 4 [] 4 = true := by decide +kernel
lemma sl_119_14 : Slice R_119 G_119 (subcubeFast 18 0) 4 := slice_fast_of sl_119_14_ok (fun _ => low_101)
lemma sl_119_15_ok : sliceCheck 33 0 0 R_119 G_119 (varsOf 86) R_86 G_86 4 [] 4 = true := by decide +kernel
lemma sl_119_15 : Slice R_119 G_119 (subcubeFast 33 0) 4 := slice_fast_of sl_119_15_ok (fun _ => low_86)
lemma sl_119_16_ok : sliceCheck 68 0 0 R_119 G_119 (varsOf 51) R_51 G_51 4 [] 4 = true := by decide +kernel
lemma sl_119_16 : Slice R_119 G_119 (subcubeFast 68 0) 4 := slice_fast_of sl_119_16_ok (fun _ => low_51)
lemma sl_119_17_ok : sliceCheck 16 0 0 R_119 G_119 (varsOf 103) R_103 G_103 5 [] 5 = true := by decide +kernel
lemma sl_119_17 : Slice R_119 G_119 (subcubeFast 16 0) 5 := slice_fast_of sl_119_17_ok (fun _ => low_103)
lemma sl_119_18_ok : sliceCheck 1 2 80 R_119 G_119 (varsOf 116) R_36 G_36 1 [(VAR 4,16,0),(VAR 6,64,0)] 3 = true := by decide +kernel
lemma sl_119_18 : Slice R_119 G_119 (subcubeFast 1 2) 3 := slice_fast_of sl_119_18_ok (fun _ => low_36)
lemma sl_119_19_ok : sliceCheck 0 32 5 R_119 G_119 (varsOf 87) R_82 G_82 2 [(VAR 0,1,0),(VAR 2,4,0)] 4 = true := by decide +kernel
lemma sl_119_19 : Slice R_119 G_119 (subcubeFast 0 32) 4 := slice_fast_of sl_119_19_ok (fun _ => low_82)
lemma sl_119_20_ok : sliceCheck 0 65 54 R_119 G_119 (varsOf 54) [] 0 0 [(VAR 1,2,0),(VAR 2,4,0),(VAR 4,16,0),(VAR 5,32,0)] 3 = true := by decide +kernel
lemma sl_119_20 : Slice R_119 G_119 (subcubeFast 0 65) 3 := slice_fast_of sl_119_20_ok (fun h => (h rfl).elim)
lemma sl_119_21_ok : sliceCheck 4 0 0 R_119 G_119 (varsOf 115) R_115 G_115 5 [] 5 = true := by decide +kernel
lemma sl_119_21 : Slice R_119 G_119 (subcubeFast 4 0) 5 := slice_fast_of sl_119_21_ok (fun _ => low_115)
lemma sl_119_22_ok : sliceCheck 36 0 0 R_119 G_119 (varsOf 83) R_83 G_83 4 [] 4 = true := by decide +kernel
lemma sl_119_22 : Slice R_119 G_119 (subcubeFast 36 0) 4 := slice_fast_of sl_119_22_ok (fun _ => low_83)
set_option maxRecDepth 500000 in
lemma slices_119_ok : btAll (fun o => ∀ p, o = some p → Slice R_119 G_119 p.1 p.2) slices_119 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_119 G_119 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_119_0) (forall_cons (fun _ h => by cases h; exact sl_119_1) (forall_cons (fun _ h => by cases h; exact sl_119_2) (forall_cons (fun _ h => by cases h; exact sl_119_3) (forall_cons (fun _ h => by cases h; exact sl_119_4) (forall_cons (fun _ h => by cases h; exact sl_119_5) (forall_cons (fun _ h => by cases h; exact sl_119_6) (forall_cons (fun _ h => by cases h; exact sl_119_7) (forall_cons (fun _ h => by cases h; exact sl_119_8) (forall_cons (fun _ h => by cases h; exact sl_119_9) (forall_cons (fun _ h => by cases h; exact sl_119_10) (forall_cons (fun _ h => by cases h; exact sl_119_11) (forall_cons (fun _ h => by cases h; exact sl_119_12) (forall_cons (fun _ h => by cases h; exact sl_119_13) (forall_cons (fun _ h => by cases h; exact sl_119_14) (forall_cons (fun _ h => by cases h; exact sl_119_15) (forall_cons (fun _ h => by cases h; exact sl_119_16) (forall_cons (fun _ h => by cases h; exact sl_119_17) (forall_cons (fun _ h => by cases h; exact sl_119_18) (forall_cons (fun _ h => by cases h; exact sl_119_19) (forall_cons (fun _ h => by cases h; exact sl_119_20) (forall_cons (fun _ h => by cases h; exact sl_119_21) (forall_cons (fun _ h => by cases h; exact sl_119_22) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))
def P_119 := buildPoolsBT 5 W_119 R_119 slices_119 [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(10,[]),(11,[]),(12,[]),(14,[]),(15,[]),(16,[]),(17,[]),(20,[]),(22,[])]
def T_119 : List (List NodeSpec) := [[],[],[],[],[],[([2,3,10,6],[1,0],[]),([1,2,3,4,6],[1,0,2],[]),([1,2,3,4,11],[3,4,5,2],[]),([12,0,1,2,4,5],[6,7,3],[])],[([0,1,2,3,4,5,6],[7,1,9,8],[]),([1,2,3,4,6],[11,1,10,2],[0,1]),([7,1,2,3,4,5],[12,13,2,4,6],[0]),([8,1,2,3,4,5],[1,2,14],[0]),([0,1,9,2,3,4,5],[7,3,11,15],[0]),([0,1,2,3,4,6],[11,13,5],[]),([0,9,2,3,4,5],[16,5,13,4],[])],[([0,1,2,3,4,5],[5,2,17,13,12,14],[0,2,1,3,4,5,6,7,8,9,10,11])]]
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma low_119 : Lower R_119 G_119 8 := lower_of_checkForestBT (by decide) gp_119 W_119_ok (buildPoolsBT_sound slices_119_ok) autos_119_ok (by decide +kernel : forestRootCheck R_119 G_119 [(VAR 0,17,16),(VAR 1,18,16),(VAR 2,36,32),(VAR 4,17,1),(VAR 5,33,1),(VAR 6,66,2)] = true) (by decide +kernel : checkForestBT W_119 G_119 fmask_119 P_119 autos_119 T_119 R_119 = true)
def G_183 : Nat := 0xfffffefeffffccccfffffefeffffccccfefefafaeeee0000fefefafaeeee0000
def R_183 : List Nat := varsOf 183
lemma low_183_ok : liftCheck 4 0 R_183 G_183 R_179 G_179 [(VAR 2,36,32)] = true := by decide +kernel
lemma low_183 : Lower R_183 G_183 8 := lift_of low_183_ok low_179
def G_215 : Nat := 0xffffffffffffffffffffccccffffccccfefefcfcfefefcfceeee0000eeee0000
def R_215 : List Nat := varsOf 215
lemma low_215_ok : liftCheck 1 0 R_215 G_215 R_214 G_214 [(VAR 0,17,16)] = true := by decide +kernel
lemma low_215 : Lower R_215 G_215 8 := lift_of low_215_ok low_214
def G_243 : Nat := 0xffffffffffffffffffffeeeeffffcccceeeeeeeeeeeecccceeeeaaaaeeee0000
def R_243 : List Nat := varsOf 243
lemma low_243_ok : liftCheck 32 0 R_243 G_243 R_211 G_211 [(VAR 5,33,1)] = true := by decide +kernel
lemma low_243 : Lower R_243 G_243 8 := lift_of low_243_ok low_211
def G_231 : Nat := 0xfffffffffffffffffefefefeccccccccfefefefefcfcfcfcfafafafa00000000
def R_231 : List Nat := varsOf 231
lemma low_231_ok : carryOK [(4,6),(0,2)] R_231 G_231 R_183 G_183 = true := by decide +kernel
lemma low_231 : Lower R_231 G_231 8 := carry_of low_231_ok low_183
def G_245 : Nat := 0xfffffffffffffffffffffafaffff0000fafafafafafaf0f0fafafafaaaaa0000
def R_245 : List Nat := varsOf 245
lemma low_245_ok : carryOK [(4,5),(2,7),(1,2),(1,3)] R_245 G_245 R_119 G_119 = true := by decide +kernel
lemma low_245 : Lower R_245 G_245 8 := carry_of low_245_ok low_119
def G_246 : Nat := 0xfffffffffffffffffffffcfcffffccccfcfcfcfcfcfcfcfcfcfcf0f0cccc0000
def R_246 : List Nat := varsOf 246
lemma low_246_ok : carryOK [(4,6),(0,2)] R_246 G_246 R_243 G_243 = true := by decide +kernel
lemma low_246 : Lower R_246 G_246 8 := carry_of low_246_ok low_243
def G_247 : Nat := 0xfffffffffffffffffffffefeffffccccfefefefefefefcfcfefefafaeeee0000
def R_247 : List Nat := varsOf 247
def pos_247 : List Nat := [17,17,17,17,17,18,18,18,18,33,33,33,33,33,33,36,36,36,36,36,36,66,66,66,66,68,68,68,68,68,130,130,130,130,144,144,144,144,192,192,192,192,17,17,18,18,18,33,36,66,66,66,68,68,130,130,130,144,144,144,192,192,192,17,18,33,36,66,68,130,144,192,17,17,18,18,33,33,36,36,66,66,68,68,130,130,144,144,192,192]
def neg_247 : List Nat := [7,20,65,112,133,7,20,34,112,7,34,65,112,133,160,7,20,34,112,133,160,7,34,65,112,7,20,65,112,133,7,34,133,160,20,112,133,160,65,112,133,160,34,160,65,133,160,20,65,20,133,160,34,160,20,65,112,7,34,65,7,20,34,0,0,0,0,0,0,0,0,0,1,16,2,16,1,32,4,32,2,64,4,64,2,128,16,128,64,128]
def fmask_247 : Nat := fullMask 90
def base_247 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x330280008c0000007e1f,0x11001a8531516aa8aa35),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x330c2901ce7003c1e001e0,0x11040056100400c26286a1),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcc014003100003e1f8000,0x440003246a1156629a273),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xc00f418e007c3c000001ff,0x400a002142808c1505114a),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xf00600018000001ffe00,0xa00045384eaa91565588),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x30f0098703e03c03fe00000,0x10a0000098110c81984190c),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0x3f000e07fc003ffc0000000,0x2a00000002c6b3320186010)]
def steps_247 : List (Nat × Nat × Nat) := [(2,3,5),(1,3,5),(1,3,4),(1,0,1),(1,1,6),(3,1,4),(2,1,4),(1,1,4),(2,0,1),(1,0,2),(3,3,4),(2,0,2),(1,1,3),(2,0,5),(1,0,5),(3,0,5),(2,3,4),(3,0,1),(3,1,8),(1,1,8),(1,2,8),(1,23,2),(3,0,9),(1,4,11),(3,3,11),(2,0,11),(1,12,3),(2,14,6),(1,0,11),(1,5,6),(2,4,6),(1,4,6),(2,19,6),(3,19,4),(1,19,4),(1,17,1),(1,2,19),(1,1,5),(1,20,1),(1,2,3),(3,2,3),(1,18,5),(1,18,1),(2,16,4),(1,4,8),(1,4,5),(1,2,6),(1,17,5),(2,4,5),(3,4,5),(2,19,5),(3,4,6),(1,15,6),(2,2,19),(3,1,21),(2,9,5),(2,10,6),(2,4,8),(2,10,5),(3,1,16),(1,1,2),(3,3,5),(1,15,5),(2,4,11),(2,2,3),(1,12,6),(3,2,6),(3,3,14),(3,1,9),(2,2,6),(1,3,6),(1,19,6),(1,10,5),(3,2,8),(1,7,2),(2,26,6),(3,1,51),(1,70,1),(2,8,11),(3,3,72),(1,33,5),(1,55,1),(1,39,5),(1,40,6),(1,26,6),(2,41,6),(2,8,6),(3,19,38),(1,60,3),(1,3,72),(1,60,1),(3,1,52),(3,3,43),(3,5,11),(3,3,44),(1,61,6),(1,17,6),(3,1,38),(1,45,6),(3,3,35),(2,42,5),(1,66,6),(3,5,59),(1,32,1),(2,42,6),(2,45,6),(0,16,52),(1,65,6),(1,37,5),(3,5,38),(1,32,5),(1,55,6),(1,52,6),(2,79,6),(2,74,5),(0,26,6),(2,21,6),(3,1,35),(3,5,35),(1,25,6),(1,71,6),(1,37,19),(1,76,1),(1,75,5),(1,75,6),(1,8,6),(3,2,52),(1,63,5),(2,65,6),(3,1,36),(2,44,6),(1,69,6),(1,44,6),(2,14,5),(1,34,3),(3,3,52),(1,9,6),(2,49,6),(2,67,6),(2,52,6),(3,3,38)]
def W_247 : BT Decor := buildWiresBT 8 base_247 steps_247
def autosL_247 : List (List (Nat × Nat)) := [[],[(1,7)],[(4,6),(0,2)],[(4,6),(1,7),(0,2)]]
def autos_247 : BT (List (Nat × Nat)) := btOfList 2 autosL_247
def slicesL_247 : List (Option (Nat × Nat)) := [some (subcubeFast 0 32,7),some (subcubeFast 0 64,5),some (subcubeFast 0 16,5),some (subcubeFast 48 1,5),some (subcubeFast 49 0,5),some (subcubeFast 16 2,4),some (subcubeFast 2 64,4),some (subcubeFast 52 1,4),some (subcubeFast 32 20,3),some (subcubeFast 128 16,4),some (subcubeFast 2 0,8),some (subcubeFast 130 0,5),some (subcubeFast 64 32,6),some (subcubeFast 1 2,4),some (subcubeFast 32 64,4),some (subcubeFast 32 80,3),some (subcubeFast 4 64,4),some (subcubeFast 18 0,5),some (subcubeFast 0 20,4),some (subcubeFast 2 20,3),some (subcubeFast 0 34,4),some (subcubeFast 64 133,2),some (subcubeFast 146 0,4),some (subcubeFast 17 32,5),some (subcubeFast 96 4,5),some (subcubeFast 101 0,4),some (subcubeFast 17 0,7),some (subcubeFast 0 80,3),some (subcubeFast 34 16,3),some (subcubeFast 0 133,3),some (subcubeFast 21 32,4),some (subcubeFast 130 64,3),some (subcubeFast 64 2,4),some (subcubeFast 16 128,4),some (subcubeFast 6 64,3),some (subcubeFast 34 64,3),some (subcubeFast 128 2,4),some (subcubeFast 2 128,4),some (subcubeFast 18 64,3),some (subcubeFast 33 4,5),some (subcubeFast 68 2,3),some (subcubeFast 2 16,4),some (subcubeFast 20 1,5),some (subcubeFast 128 32,4),some (subcubeFast 1 132,3),some (subcubeFast 16 5,3),some (subcubeFast 1 6,3),some (subcubeFast 64 160,3),some (subcubeFast 128 1,4),some (subcubeFast 194 0,4),some (subcubeFast 145 0,4),some (subcubeFast 17 128,3),some (subcubeFast 1 34,3),some (subcubeFast 2 1,4),some (subcubeFast 20 2,3),some (subcubeFast 16 1,6),some (subcubeFast 64 4,6),some (subcubeFast 0 65,4),some (subcubeFast 1 16,4),some (subcubeFast 32 16,4),some (subcubeFast 1 32,6),some (subcubeFast 0 2,5),some (subcubeFast 16 32,6),some (subcubeFast 0 128,5),some (subcubeFast 4 32,6),some (subcubeFast 100 0,5),some (subcubeFast 68 32,5),some (subcubeFast 128 64,4),some (subcubeFast 4 128,4),some (subcubeFast 4 129,3),some (subcubeFast 64 128,4),some (subcubeFast 64 0,8),some (subcubeFast 32 0,8),some (subcubeFast 16 0,8),some (subcubeFast 32 1,6),some (subcubeFast 33 0,7),some (subcubeFast 32 4,6),some (subcubeFast 36 0,7),some (subcubeFast 1 0,8),some (subcubeFast 0 160,4),some (subcubeFast 34 0,5),some (subcubeFast 96 0,5),some (subcubeFast 160 0,5),some (subcubeFast 164 0,4),some (subcubeFast 2 112,2),some (subcubeFast 160 64,3),some (subcubeFast 80 128,3),some (subcubeFast 4 2,4),some (subcubeFast 128 0,8),some (subcubeFast 64 16,4),some (subcubeFast 20 32,5),some (subcubeFast 48 0,5),some (subcubeFast 192 2,3),some (subcubeFast 128 112,2),some (subcubeFast 20 0,6),some (subcubeFast 4 1,6),some (subcubeFast 5 32,5),some (subcubeFast 65 32,5),some (subcubeFast 18 96,2),some (subcubeFast 146 1,2),some (subcubeFast 0 129,3),some (subcubeFast 34 80,2),some (subcubeFast 0 3,3),some (subcubeFast 16 34,3),some (subcubeFast 146 64,2),some (subcubeFast 130 16,3),some (subcubeFast 4 3,3),some (subcubeFast 0 112,3),some (subcubeFast 1 128,4),some (subcubeFast 65 0,6),some (subcubeFast 65 4,5),some (subcubeFast 3 0,5),some (subcubeFast 132 3,2),some (subcubeFast 0 7,3),some (subcubeFast 36 1,5),some (subcubeFast 2 133,2),some (subcubeFast 68 0,7),some (subcubeFast 1 4,6),some (subcubeFast 129 0,5),some (subcubeFast 16 64,4),some (subcubeFast 66 0,5),some (subcubeFast 16 96,3),some (subcubeFast 70 0,4),some (subcubeFast 144 64,3),some (subcubeFast 192 16,3),some (subcubeFast 66 128,3),some (subcubeFast 130 5,2),some (subcubeFast 69 32,4),some (subcubeFast 35 0,4),some (subcubeFast 0 1,7),some (subcubeFast 161 0,4),some (subcubeFast 19 0,4),some (subcubeFast 160 1,3),some (subcubeFast 194 16,2),some (subcubeFast 128 4,4),some (subcubeFast 2 4,4),some (subcubeFast 5 0,5),some (subcubeFast 34 1,3),some (subcubeFast 37 0,5),some (subcubeFast 18 128,3),some (subcubeFast 0 4,7),some (subcubeFast 4 34,3),some (subcubeFast 0 132,3),some (subcubeFast 80 2,3),some (subcubeFast 128 65,3),some (subcubeFast 129 6,2),some (subcubeFast 97 4,4),some (subcubeFast 3 16,3),some (subcubeFast 128 34,3),some (subcubeFast 52 0,4),some (subcubeFast 66 16,3),some (subcubeFast 68 128,3),some (subcubeFast 16 65,3),some (subcubeFast 64 20,3),some (subcubeFast 82 128,2),some (subcubeFast 0 6,3),some (subcubeFast 192 0,5),some (subcubeFast 18 32,3),some (subcubeFast 144 0,5),some (subcubeFast 97 0,4),some (subcubeFast 16 133,2),some (subcubeFast 128 20,3),some (subcubeFast 129 16,3),some (subcubeFast 128 7,2),some (subcubeFast 130 4,3),some (subcubeFast 132 64,3),some (subcubeFast 20 3,2),some (subcubeFast 6 0,5),some (subcubeFast 144 2,3),some (subcubeFast 4 0,8),some (subcubeFast 130 1,3),some (subcubeFast 32 133,2),some (subcubeFast 2 160,3),some (subcubeFast 208 2,2),some (subcubeFast 1 160,3),some (subcubeFast 4 160,3),some (subcubeFast 16 160,3),some (subcubeFast 80 5,2),some (subcubeFast 2 65,3),some (subcubeFast 80 32,3),some (subcubeFast 134 64,2),some (subcubeFast 64 7,2),some (subcubeFast 64 34,3),some (subcubeFast 132 2,3),some (subcubeFast 194 4,2),some (subcubeFast 131 16,2),some (subcubeFast 144 34,2),some (subcubeFast 162 1,2)]
def slices_247 : BT (Option (Nat × Nat)) := btOfList 8 slicesL_247
lemma gp_247 : goodPairs G_247 pos_247 neg_247 := goodPairs_of (by decide +kernel)
lemma base_247_ok : ∀ x ∈ base_247, faithful pos_247 neg_247 x ∧ x.1 < 2^256 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_247_ok : btAll (fun x => faithful pos_247 neg_247 x ∧ x.1 < 2^256) W_247 := buildWiresBT_faithful base_247_ok
set_option maxRecDepth 500000 in
lemma autos_247_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_247 = G_247) autos_247 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_247_0_ok : sliceCheck 0 32 5 R_247 G_247 (varsOf 215) R_210 G_210 5 [(VAR 0,1,0),(VAR 2,4,0)] 7 = true := by decide +kernel
lemma sl_247_0 : Slice R_247 G_247 (subcubeFast 0 32) 7 := slice_fast_of sl_247_0_ok (fun _ => low_210)
lemma sl_247_1_ok : sliceCheck 0 64 134 R_247 G_247 (varsOf 183) R_49 G_49 2 [(VAR 1,2,0),(VAR 2,4,0),(VAR 7,128,0)] 5 = true := by decide +kernel
lemma sl_247_1 : Slice R_247 G_247 (subcubeFast 0 64) 5 := slice_fast_of sl_247_1_ok (fun _ => low_49)
lemma sl_247_2_ok : sliceCheck 0 16 131 R_247 G_247 (varsOf 231) R_100 G_100 2 [(VAR 0,1,0),(VAR 1,2,0),(VAR 7,128,0)] 5 = true := by decide +kernel
lemma sl_247_2 : Slice R_247 G_247 (subcubeFast 0 16) 5 := slice_fast_of sl_247_2_ok (fun _ => low_100)
lemma sl_247_3_ok : sliceCheck 48 1 0 R_247 G_247 (varsOf 198) R_198 G_198 5 [] 5 = true := by decide +kernel
lemma sl_247_3 : Slice R_247 G_247 (subcubeFast 48 1) 5 := slice_fast_of sl_247_3_ok (fun _ => low_198)
lemma sl_247_4_ok : sliceCheck 49 0 0 R_247 G_247 (varsOf 198) R_198 G_198 5 [] 5 = true := by decide +kernel
lemma sl_247_4 : Slice R_247 G_247 (subcubeFast 49 0) 5 := slice_fast_of sl_247_4_ok (fun _ => low_198)
lemma sl_247_5_ok : sliceCheck 16 2 192 R_247 G_247 (varsOf 229) R_37 G_37 2 [(VAR 6,64,0),(VAR 7,128,0)] 4 = true := by decide +kernel
lemma sl_247_5 : Slice R_247 G_247 (subcubeFast 16 2) 4 := slice_fast_of sl_247_5_ok (fun _ => low_37)
lemma sl_247_6_ok : sliceCheck 2 64 132 R_247 G_247 (varsOf 181) R_49 G_49 2 [(VAR 2,4,0),(VAR 7,128,0)] 4 = true := by decide +kernel
lemma sl_247_6 : Slice R_247 G_247 (subcubeFast 2 64) 4 := slice_fast_of sl_247_6_ok (fun _ => low_49)
lemma sl_247_7_ok : sliceCheck 52 1 0 R_247 G_247 (varsOf 194) R_194 G_194 4 [] 4 = true := by decide +kernel
lemma sl_247_7 : Slice R_247 G_247 (subcubeFast 52 1) 4 := slice_fast_of sl_247_7_ok (fun _ => low_194)
lemma sl_247_8_ok : sliceCheck 32 20 195 R_247 G_247 (varsOf 195) [] 0 0 [(VAR 0,1,0),(VAR 1,2,0),(VAR 6,64,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_8 : Slice R_247 G_247 (subcubeFast 32 20) 3 := slice_fast_of sl_247_8_ok (fun h => (h rfl).elim)
lemma sl_247_9_ok : sliceCheck 128 16 3 R_247 G_247 (varsOf 103) R_100 G_100 2 [(VAR 0,1,0),(VAR 1,2,0)] 4 = true := by decide +kernel
lemma sl_247_9 : Slice R_247 G_247 (subcubeFast 128 16) 4 := slice_fast_of sl_247_9_ok (fun _ => low_100)
lemma sl_247_10_ok : sliceCheck 2 0 0 R_247 G_247 (varsOf 245) R_245 G_245 8 [] 8 = true := by decide +kernel
lemma sl_247_10 : Slice R_247 G_247 (subcubeFast 2 0) 8 := slice_fast_of sl_247_10_ok (fun _ => low_245)
lemma sl_247_11_ok : sliceCheck 130 0 0 R_247 G_247 (varsOf 117) R_117 G_117 5 [] 5 = true := by decide +kernel
lemma sl_247_11 : Slice R_247 G_247 (subcubeFast 130 0) 5 := slice_fast_of sl_247_11_ok (fun _ => low_117)
lemma sl_247_12_ok : sliceCheck 64 32 5 R_247 G_247 (varsOf 151) R_146 G_146 4 [(VAR 0,1,0),(VAR 2,4,0)] 6 = true := by decide +kernel
lemma sl_247_12 : Slice R_247 G_247 (subcubeFast 64 32) 6 := slice_fast_of sl_247_12_ok (fun _ => low_146)
lemma sl_247_13_ok : sliceCheck 1 2 208 R_247 G_247 (varsOf 244) R_36 G_36 1 [(VAR 4,16,0),(VAR 6,64,0),(VAR 7,128,0)] 4 = true := by decide +kernel
lemma sl_247_13 : Slice R_247 G_247 (subcubeFast 1 2) 4 := slice_fast_of sl_247_13_ok (fun _ => low_36)
lemma sl_247_14_ok : sliceCheck 32 64 134 R_247 G_247 (varsOf 151) R_17 G_17 1 [(VAR 1,2,0),(VAR 2,4,0),(VAR 7,128,0)] 4 = true := by decide +kernel
lemma sl_247_14 : Slice R_247 G_247 (subcubeFast 32 64) 4 := slice_fast_of sl_247_14_ok (fun _ => low_17)
lemma sl_247_15_ok : sliceCheck 32 80 135 R_247 G_247 (varsOf 135) [] 0 0 [(VAR 0,1,0),(VAR 1,2,0),(VAR 2,4,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_15 : Slice R_247 G_247 (subcubeFast 32 80) 3 := slice_fast_of sl_247_15_ok (fun h => (h rfl).elim)
lemma sl_247_16_ok : sliceCheck 4 64 130 R_247 G_247 (varsOf 179) R_49 G_49 2 [(VAR 1,2,0),(VAR 7,128,0)] 4 = true := by decide +kernel
lemma sl_247_16 : Slice R_247 G_247 (subcubeFast 4 64) 4 := slice_fast_of sl_247_16_ok (fun _ => low_49)
lemma sl_247_17_ok : sliceCheck 18 0 0 R_247 G_247 (varsOf 229) R_229 G_229 5 [] 5 = true := by decide +kernel
lemma sl_247_17 : Slice R_247 G_247 (subcubeFast 18 0) 5 := slice_fast_of sl_247_17_ok (fun _ => low_229)
lemma sl_247_18_ok : sliceCheck 0 20 227 R_247 G_247 (varsOf 227) [] 0 0 [(VAR 0,1,0),(VAR 1,2,0),(VAR 5,32,0),(VAR 6,64,0),(VAR 7,128,0)] 4 = true := by decide +kernel
lemma sl_247_18 : Slice R_247 G_247 (subcubeFast 0 20) 4 := slice_fast_of sl_247_18_ok (fun h => (h rfl).elim)
lemma sl_247_19_ok : sliceCheck 2 20 225 R_247 G_247 (varsOf 225) [] 0 0 [(VAR 0,1,0),(VAR 5,32,0),(VAR 6,64,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_19 : Slice R_247 G_247 (subcubeFast 2 20) 3 := slice_fast_of sl_247_19_ok (fun h => (h rfl).elim)
lemma sl_247_20_ok : sliceCheck 0 34 213 R_247 G_247 (varsOf 213) [] 0 0 [(VAR 0,1,0),(VAR 2,4,0),(VAR 4,16,0),(VAR 6,64,0),(VAR 7,128,0)] 4 = true := by decide +kernel
lemma sl_247_20 : Slice R_247 G_247 (subcubeFast 0 34) 4 := slice_fast_of sl_247_20_ok (fun h => (h rfl).elim)
lemma sl_247_21_ok : sliceCheck 64 133 50 R_247 G_247 (varsOf 50) [] 0 0 [(VAR 1,2,0),(VAR 4,16,0),(VAR 5,32,0)] 2 = true := by decide +kernel
lemma sl_247_21 : Slice R_247 G_247 (subcubeFast 64 133) 2 := slice_fast_of sl_247_21_ok (fun h => (h rfl).elim)
lemma sl_247_22_ok : sliceCheck 146 0 0 R_247 G_247 (varsOf 101) R_101 G_101 4 [] 4 = true := by decide +kernel
lemma sl_247_22 : Slice R_247 G_247 (subcubeFast 146 0) 4 := slice_fast_of sl_247_22_ok (fun _ => low_101)
lemma sl_247_23_ok : sliceCheck 17 32 4 R_247 G_247 (varsOf 198) R_194 G_194 4 [(VAR 2,4,0)] 5 = true := by decide +kernel
lemma sl_247_23 : Slice R_247 G_247 (subcubeFast 17 32) 5 := slice_fast_of sl_247_23_ok (fun _ => low_194)
lemma sl_247_24_ok : sliceCheck 96 4 0 R_247 G_247 (varsOf 147) R_147 G_147 5 [] 5 = true := by decide +kernel
lemma sl_247_24 : Slice R_247 G_247 (subcubeFast 96 4) 5 := slice_fast_of sl_247_24_ok (fun _ => low_147)
lemma sl_247_25_ok : sliceCheck 101 0 0 R_247 G_247 (varsOf 146) R_146 G_146 4 [] 4 = true := by decide +kernel
lemma sl_247_25 : Slice R_247 G_247 (subcubeFast 101 0) 4 := slice_fast_of sl_247_25_ok (fun _ => low_146)
lemma sl_247_26_ok : sliceCheck 17 0 0 R_247 G_247 (varsOf 230) R_230 G_230 7 [] 7 = true := by decide +kernel
lemma sl_247_26 : Slice R_247 G_247 (subcubeFast 17 0) 7 := slice_fast_of sl_247_26_ok (fun _ => low_230)
lemma sl_247_27_ok : sliceCheck 0 80 167 R_247 G_247 (varsOf 167) [] 0 0 [(VAR 0,1,0),(VAR 1,2,0),(VAR 2,4,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_27 : Slice R_247 G_247 (subcubeFast 0 80) 3 := slice_fast_of sl_247_27_ok (fun h => (h rfl).elim)
lemma sl_247_28_ok : sliceCheck 34 16 129 R_247 G_247 (varsOf 197) R_68 G_68 1 [(VAR 0,1,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_28 : Slice R_247 G_247 (subcubeFast 34 16) 3 := slice_fast_of sl_247_28_ok (fun _ => low_68)
lemma sl_247_29_ok : sliceCheck 0 133 114 R_247 G_247 (varsOf 114) [] 0 0 [(VAR 1,2,0),(VAR 4,16,0),(VAR 5,32,0),(VAR 6,64,0)] 3 = true := by decide +kernel
lemma sl_247_29 : Slice R_247 G_247 (subcubeFast 0 133) 3 := slice_fast_of sl_247_29_ok (fun h => (h rfl).elim)
lemma sl_247_30_ok : sliceCheck 21 32 0 R_247 G_247 (varsOf 194) R_194 G_194 4 [] 4 = true := by decide +kernel
lemma sl_247_30 : Slice R_247 G_247 (subcubeFast 21 32) 4 := slice_fast_of sl_247_30_ok (fun _ => low_194)
lemma sl_247_31_ok : sliceCheck 130 64 4 R_247 G_247 (varsOf 53) R_49 G_49 2 [(VAR 2,4,0)] 3 = true := by decide +kernel
lemma sl_247_31 : Slice R_247 G_247 (subcubeFast 130 64) 3 := slice_fast_of sl_247_31_ok (fun _ => low_49)
lemma sl_247_32_ok : sliceCheck 64 2 144 R_247 G_247 (varsOf 181) R_37 G_37 2 [(VAR 4,16,0),(VAR 7,128,0)] 4 = true := by decide +kernel
lemma sl_247_32 : Slice R_247 G_247 (subcubeFast 64 2) 4 := slice_fast_of sl_247_32_ok (fun _ => low_37)
lemma sl_247_33_ok : sliceCheck 16 128 66 R_247 G_247 (varsOf 103) R_37 G_37 2 [(VAR 1,2,0),(VAR 6,64,0)] 4 = true := by decide +kernel
lemma sl_247_33 : Slice R_247 G_247 (subcubeFast 16 128) 4 := slice_fast_of sl_247_33_ok (fun _ => low_37)
lemma sl_247_34_ok : sliceCheck 6 64 128 R_247 G_247 (varsOf 177) R_49 G_49 2 [(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_34 : Slice R_247 G_247 (subcubeFast 6 64) 3 := slice_fast_of sl_247_34_ok (fun _ => low_49)
lemma sl_247_35_ok : sliceCheck 34 64 132 R_247 G_247 (varsOf 149) R_17 G_17 1 [(VAR 2,4,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_35 : Slice R_247 G_247 (subcubeFast 34 64) 3 := slice_fast_of sl_247_35_ok (fun _ => low_17)
lemma sl_247_36_ok : sliceCheck 128 2 80 R_247 G_247 (varsOf 117) R_37 G_37 2 [(VAR 4,16,0),(VAR 6,64,0)] 4 = true := by decide +kernel
lemma sl_247_36 : Slice R_247 G_247 (subcubeFast 128 2) 4 := slice_fast_of sl_247_36_ok (fun _ => low_37)
lemma sl_247_37_ok : sliceCheck 2 128 80 R_247 G_247 (varsOf 117) R_37 G_37 2 [(VAR 4,16,0),(VAR 6,64,0)] 4 = true := by decide +kernel
lemma sl_247_37 : Slice R_247 G_247 (subcubeFast 2 128) 4 := slice_fast_of sl_247_37_ok (fun _ => low_37)
lemma sl_247_38_ok : sliceCheck 18 64 132 R_247 G_247 (varsOf 165) R_33 G_33 1 [(VAR 2,4,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_38 : Slice R_247 G_247 (subcubeFast 18 64) 3 := slice_fast_of sl_247_38_ok (fun _ => low_33)
lemma sl_247_39_ok : sliceCheck 33 4 64 R_247 G_247 (varsOf 210) R_146 G_146 4 [(VAR 6,64,0)] 5 = true := by decide +kernel
lemma sl_247_39 : Slice R_247 G_247 (subcubeFast 33 4) 5 := slice_fast_of sl_247_39_ok (fun _ => low_146)
lemma sl_247_40_ok : sliceCheck 68 2 144 R_247 G_247 (varsOf 177) R_33 G_33 1 [(VAR 4,16,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_40 : Slice R_247 G_247 (subcubeFast 68 2) 3 := slice_fast_of sl_247_40_ok (fun _ => low_33)
lemma sl_247_41_ok : sliceCheck 2 16 129 R_247 G_247 (varsOf 229) R_100 G_100 2 [(VAR 0,1,0),(VAR 7,128,0)] 4 = true := by decide +kernel
lemma sl_247_41 : Slice R_247 G_247 (subcubeFast 2 16) 4 := slice_fast_of sl_247_41_ok (fun _ => low_100)
lemma sl_247_42_ok : sliceCheck 20 1 32 R_247 G_247 (varsOf 226) R_194 G_194 4 [(VAR 5,32,0)] 5 = true := by decide +kernel
lemma sl_247_42 : Slice R_247 G_247 (subcubeFast 20 1) 5 := slice_fast_of sl_247_42_ok (fun _ => low_194)
lemma sl_247_43_ok : sliceCheck 128 32 5 R_247 G_247 (varsOf 87) R_82 G_82 2 [(VAR 0,1,0),(VAR 2,4,0)] 4 = true := by decide +kernel
lemma sl_247_43 : Slice R_247 G_247 (subcubeFast 128 32) 4 := slice_fast_of sl_247_43_ok (fun _ => low_82)
lemma sl_247_44_ok : sliceCheck 1 132 114 R_247 G_247 (varsOf 114) [] 0 0 [(VAR 1,2,0),(VAR 4,16,0),(VAR 5,32,0),(VAR 6,64,0)] 3 = true := by decide +kernel
lemma sl_247_44 : Slice R_247 G_247 (subcubeFast 1 132) 3 := slice_fast_of sl_247_44_ok (fun h => (h rfl).elim)
lemma sl_247_45_ok : sliceCheck 16 5 96 R_247 G_247 (varsOf 226) R_130 G_130 1 [(VAR 5,32,0),(VAR 6,64,0)] 3 = true := by decide +kernel
lemma sl_247_45 : Slice R_247 G_247 (subcubeFast 16 5) 3 := slice_fast_of sl_247_45_ok (fun _ => low_130)
lemma sl_247_46_ok : sliceCheck 1 6 240 R_247 G_247 (varsOf 240) [] 0 0 [(VAR 4,16,0),(VAR 5,32,0),(VAR 6,64,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_46 : Slice R_247 G_247 (subcubeFast 1 6) 3 := slice_fast_of sl_247_46_ok (fun h => (h rfl).elim)
lemma sl_247_47_ok : sliceCheck 64 160 23 R_247 G_247 (varsOf 23) [] 0 0 [(VAR 0,1,0),(VAR 1,2,0),(VAR 2,4,0),(VAR 4,16,0)] 3 = true := by decide +kernel
lemma sl_247_47 : Slice R_247 G_247 (subcubeFast 64 160) 3 := slice_fast_of sl_247_47_ok (fun h => (h rfl).elim)
lemma sl_247_48_ok : sliceCheck 128 1 48 R_247 G_247 (varsOf 118) R_70 G_70 2 [(VAR 4,16,0),(VAR 5,32,0)] 4 = true := by decide +kernel
lemma sl_247_48 : Slice R_247 G_247 (subcubeFast 128 1) 4 := slice_fast_of sl_247_48_ok (fun _ => low_70)
lemma sl_247_49_ok : sliceCheck 194 0 0 R_247 G_247 (varsOf 53) R_53 G_53 4 [] 4 = true := by decide +kernel
lemma sl_247_49 : Slice R_247 G_247 (subcubeFast 194 0) 4 := slice_fast_of sl_247_49_ok (fun _ => low_53)
lemma sl_247_50_ok : sliceCheck 145 0 0 R_247 G_247 (varsOf 102) R_102 G_102 4 [] 4 = true := by decide +kernel
lemma sl_247_50 : Slice R_247 G_247 (subcubeFast 145 0) 4 := slice_fast_of sl_247_50_ok (fun _ => low_102)
lemma sl_247_51_ok : sliceCheck 17 128 66 R_247 G_247 (varsOf 102) R_36 G_36 1 [(VAR 1,2,0),(VAR 6,64,0)] 3 = true := by decide +kernel
lemma sl_247_51 : Slice R_247 G_247 (subcubeFast 17 128) 3 := slice_fast_of sl_247_51_ok (fun _ => low_36)
lemma sl_247_52_ok : sliceCheck 1 34 212 R_247 G_247 (varsOf 212) [] 0 0 [(VAR 2,4,0),(VAR 4,16,0),(VAR 6,64,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_52 : Slice R_247 G_247 (subcubeFast 1 34) 3 := slice_fast_of sl_247_52_ok (fun h => (h rfl).elim)
lemma sl_247_53_ok : sliceCheck 2 1 48 R_247 G_247 (varsOf 244) R_196 G_196 2 [(VAR 4,16,0),(VAR 5,32,0)] 4 = true := by decide +kernel
lemma sl_247_53 : Slice R_247 G_247 (subcubeFast 2 1) 4 := slice_fast_of sl_247_53_ok (fun _ => low_196)
lemma sl_247_54_ok : sliceCheck 20 2 192 R_247 G_247 (varsOf 225) R_33 G_33 1 [(VAR 6,64,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_54 : Slice R_247 G_247 (subcubeFast 20 2) 3 := slice_fast_of sl_247_54_ok (fun _ => low_33)
lemma sl_247_55_ok : sliceCheck 16 1 32 R_247 G_247 (varsOf 230) R_198 G_198 5 [(VAR 5,32,0)] 6 = true := by decide +kernel
lemma sl_247_55 : Slice R_247 G_247 (subcubeFast 16 1) 6 := slice_fast_of sl_247_55_ok (fun _ => low_198)
lemma sl_247_56_ok : sliceCheck 64 4 32 R_247 G_247 (varsOf 179) R_147 G_147 5 [(VAR 5,32,0)] 6 = true := by decide +kernel
lemma sl_247_56 : Slice R_247 G_247 (subcubeFast 64 4) 6 := slice_fast_of sl_247_56_ok (fun _ => low_147)
lemma sl_247_57_ok : sliceCheck 0 65 182 R_247 G_247 (varsOf 182) [] 0 0 [(VAR 1,2,0),(VAR 2,4,0),(VAR 4,16,0),(VAR 5,32,0),(VAR 7,128,0)] 4 = true := by decide +kernel
lemma sl_247_57 : Slice R_247 G_247 (subcubeFast 0 65) 4 := slice_fast_of sl_247_57_ok (fun h => (h rfl).elim)
lemma sl_247_58_ok : sliceCheck 1 16 130 R_247 G_247 (varsOf 230) R_100 G_100 2 [(VAR 1,2,0),(VAR 7,128,0)] 4 = true := by decide +kernel
lemma sl_247_58 : Slice R_247 G_247 (subcubeFast 1 16) 4 := slice_fast_of sl_247_58_ok (fun _ => low_100)
lemma sl_247_59_ok : sliceCheck 32 16 131 R_247 G_247 (varsOf 199) R_68 G_68 1 [(VAR 0,1,0),(VAR 1,2,0),(VAR 7,128,0)] 4 = true := by decide +kernel
lemma sl_247_59 : Slice R_247 G_247 (subcubeFast 32 16) 4 := slice_fast_of sl_247_59_ok (fun _ => low_68)
lemma sl_247_60_ok : sliceCheck 1 32 4 R_247 G_247 (varsOf 214) R_210 G_210 5 [(VAR 2,4,0)] 6 = true := by decide +kernel
lemma sl_247_60 : Slice R_247 G_247 (subcubeFast 1 32) 6 := slice_fast_of sl_247_60_ok (fun _ => low_210)
lemma sl_247_61_ok : sliceCheck 0 2 208 R_247 G_247 (varsOf 245) R_37 G_37 2 [(VAR 4,16,0),(VAR 6,64,0),(VAR 7,128,0)] 5 = true := by decide +kernel
lemma sl_247_61 : Slice R_247 G_247 (subcubeFast 0 2) 5 := slice_fast_of sl_247_61_ok (fun _ => low_37)
lemma sl_247_62_ok : sliceCheck 16 32 5 R_247 G_247 (varsOf 199) R_194 G_194 4 [(VAR 0,1,0),(VAR 2,4,0)] 6 = true := by decide +kernel
lemma sl_247_62 : Slice R_247 G_247 (subcubeFast 16 32) 6 := slice_fast_of sl_247_62_ok (fun _ => low_194)
lemma sl_247_63_ok : sliceCheck 0 128 82 R_247 G_247 (varsOf 119) R_37 G_37 2 [(VAR 1,2,0),(VAR 4,16,0),(VAR 6,64,0)] 5 = true := by decide +kernel
lemma sl_247_63 : Slice R_247 G_247 (subcubeFast 0 128) 5 := slice_fast_of sl_247_63_ok (fun _ => low_37)
lemma sl_247_64_ok : sliceCheck 4 32 1 R_247 G_247 (varsOf 211) R_210 G_210 5 [(VAR 0,1,0)] 6 = true := by decide +kernel
lemma sl_247_64 : Slice R_247 G_247 (subcubeFast 4 32) 6 := slice_fast_of sl_247_64_ok (fun _ => low_210)
lemma sl_247_65_ok : sliceCheck 100 0 0 R_247 G_247 (varsOf 147) R_147 G_147 5 [] 5 = true := by decide +kernel
lemma sl_247_65 : Slice R_247 G_247 (subcubeFast 100 0) 5 := slice_fast_of sl_247_65_ok (fun _ => low_147)
lemma sl_247_66_ok : sliceCheck 68 32 1 R_247 G_247 (varsOf 147) R_146 G_146 4 [(VAR 0,1,0)] 5 = true := by decide +kernel
lemma sl_247_66 : Slice R_247 G_247 (subcubeFast 68 32) 5 := slice_fast_of sl_247_66_ok (fun _ => low_146)
lemma sl_247_67_ok : sliceCheck 128 64 6 R_247 G_247 (varsOf 55) R_49 G_49 2 [(VAR 1,2,0),(VAR 2,4,0)] 4 = true := by decide +kernel
lemma sl_247_67 : Slice R_247 G_247 (subcubeFast 128 64) 4 := slice_fast_of sl_247_67_ok (fun _ => low_49)
lemma sl_247_68_ok : sliceCheck 4 128 82 R_247 G_247 (varsOf 115) R_33 G_33 1 [(VAR 1,2,0),(VAR 4,16,0),(VAR 6,64,0)] 4 = true := by decide +kernel
lemma sl_247_68 : Slice R_247 G_247 (subcubeFast 4 128) 4 := slice_fast_of sl_247_68_ok (fun _ => low_33)
lemma sl_247_69_ok : sliceCheck 4 129 114 R_247 G_247 (varsOf 114) [] 0 0 [(VAR 1,2,0),(VAR 4,16,0),(VAR 5,32,0),(VAR 6,64,0)] 3 = true := by decide +kernel
lemma sl_247_69 : Slice R_247 G_247 (subcubeFast 4 129) 3 := slice_fast_of sl_247_69_ok (fun h => (h rfl).elim)
lemma sl_247_70_ok : sliceCheck 64 128 18 R_247 G_247 (varsOf 55) R_37 G_37 2 [(VAR 1,2,0),(VAR 4,16,0)] 4 = true := by decide +kernel
lemma sl_247_70 : Slice R_247 G_247 (subcubeFast 64 128) 4 := slice_fast_of sl_247_70_ok (fun _ => low_37)
lemma sl_247_71_ok : sliceCheck 64 0 0 R_247 G_247 (varsOf 183) R_183 G_183 8 [] 8 = true := by decide +kernel
lemma sl_247_71 : Slice R_247 G_247 (subcubeFast 64 0) 8 := slice_fast_of sl_247_71_ok (fun _ => low_183)
lemma sl_247_72_ok : sliceCheck 32 0 0 R_247 G_247 (varsOf 215) R_215 G_215 8 [] 8 = true := by decide +kernel
lemma sl_247_72 : Slice R_247 G_247 (subcubeFast 32 0) 8 := slice_fast_of sl_247_72_ok (fun _ => low_215)
lemma sl_247_73_ok : sliceCheck 16 0 0 R_247 G_247 (varsOf 231) R_231 G_231 8 [] 8 = true := by decide +kernel
lemma sl_247_73 : Slice R_247 G_247 (subcubeFast 16 0) 8 := slice_fast_of sl_247_73_ok (fun _ => low_231)
lemma sl_247_74_ok : sliceCheck 32 1 16 R_247 G_247 (varsOf 214) R_198 G_198 5 [(VAR 4,16,0)] 6 = true := by decide +kernel
lemma sl_247_74 : Slice R_247 G_247 (subcubeFast 32 1) 6 := slice_fast_of sl_247_74_ok (fun _ => low_198)
lemma sl_247_75_ok : sliceCheck 33 0 0 R_247 G_247 (varsOf 214) R_214 G_214 7 [] 7 = true := by decide +kernel
lemma sl_247_75 : Slice R_247 G_247 (subcubeFast 33 0) 7 := slice_fast_of sl_247_75_ok (fun _ => low_214)
lemma sl_247_76_ok : sliceCheck 32 4 64 R_247 G_247 (varsOf 211) R_147 G_147 5 [(VAR 6,64,0)] 6 = true := by decide +kernel
lemma sl_247_76 : Slice R_247 G_247 (subcubeFast 32 4) 6 := slice_fast_of sl_247_76_ok (fun _ => low_147)
lemma sl_247_77_ok : sliceCheck 36 0 0 R_247 G_247 (varsOf 211) R_211 G_211 7 [] 7 = true := by decide +kernel
lemma sl_247_77 : Slice R_247 G_247 (subcubeFast 36 0) 7 := slice_fast_of sl_247_77_ok (fun _ => low_211)
lemma sl_247_78_ok : sliceCheck 1 0 0 R_247 G_247 (varsOf 246) R_246 G_246 8 [] 8 = true := by decide +kernel
lemma sl_247_78 : Slice R_247 G_247 (subcubeFast 1 0) 8 := slice_fast_of sl_247_78_ok (fun _ => low_246)
lemma sl_247_79_ok : sliceCheck 0 160 87 R_247 G_247 (varsOf 87) [] 0 0 [(VAR 0,1,0),(VAR 1,2,0),(VAR 2,4,0),(VAR 4,16,0),(VAR 6,64,0)] 4 = true := by decide +kernel
lemma sl_247_79 : Slice R_247 G_247 (subcubeFast 0 160) 4 := slice_fast_of sl_247_79_ok (fun h => (h rfl).elim)
lemma sl_247_80_ok : sliceCheck 34 0 0 R_247 G_247 (varsOf 213) R_213 G_213 5 [] 5 = true := by decide +kernel
lemma sl_247_80 : Slice R_247 G_247 (subcubeFast 34 0) 5 := slice_fast_of sl_247_80_ok (fun _ => low_213)
lemma sl_247_81_ok : sliceCheck 96 0 4 R_247 G_247 (varsOf 151) R_147 G_147 5 [] 5 = true := by decide +kernel
lemma sl_247_81 : Slice R_247 G_247 (subcubeFast 96 0) 5 := slice_fast_of sl_247_81_ok (fun _ => low_147)
lemma sl_247_82_ok : sliceCheck 160 0 0 R_247 G_247 (varsOf 87) R_87 G_87 5 [] 5 = true := by decide +kernel
lemma sl_247_82 : Slice R_247 G_247 (subcubeFast 160 0) 5 := slice_fast_of sl_247_82_ok (fun _ => low_87)
lemma sl_247_83_ok : sliceCheck 164 0 0 R_247 G_247 (varsOf 83) R_83 G_83 4 [] 4 = true := by decide +kernel
lemma sl_247_83 : Slice R_247 G_247 (subcubeFast 164 0) 4 := slice_fast_of sl_247_83_ok (fun _ => low_83)
lemma sl_247_84_ok : sliceCheck 2 112 133 R_247 G_247 (varsOf 133) [] 0 0 [(VAR 0,1,0),(VAR 2,4,0),(VAR 7,128,0)] 2 = true := by decide +kernel
lemma sl_247_84 : Slice R_247 G_247 (subcubeFast 2 112) 2 := slice_fast_of sl_247_84_ok (fun h => (h rfl).elim)
lemma sl_247_85_ok : sliceCheck 160 64 6 R_247 G_247 (varsOf 23) R_17 G_17 1 [(VAR 1,2,0),(VAR 2,4,0)] 3 = true := by decide +kernel
lemma sl_247_85 : Slice R_247 G_247 (subcubeFast 160 64) 3 := slice_fast_of sl_247_85_ok (fun _ => low_17)
lemma sl_247_86_ok : sliceCheck 80 128 2 R_247 G_247 (varsOf 39) R_37 G_37 2 [(VAR 1,2,0)] 3 = true := by decide +kernel
lemma sl_247_86 : Slice R_247 G_247 (subcubeFast 80 128) 3 := slice_fast_of sl_247_86_ok (fun _ => low_37)
lemma sl_247_87_ok : sliceCheck 4 2 208 R_247 G_247 (varsOf 241) R_33 G_33 1 [(VAR 4,16,0),(VAR 6,64,0),(VAR 7,128,0)] 4 = true := by decide +kernel
lemma sl_247_87 : Slice R_247 G_247 (subcubeFast 4 2) 4 := slice_fast_of sl_247_87_ok (fun _ => low_33)
lemma sl_247_88_ok : sliceCheck 128 0 0 R_247 G_247 (varsOf 119) R_119 G_119 8 [] 8 = true := by decide +kernel
lemma sl_247_88 : Slice R_247 G_247 (subcubeFast 128 0) 8 := slice_fast_of sl_247_88_ok (fun _ => low_119)
lemma sl_247_89_ok : sliceCheck 64 16 131 R_247 G_247 (varsOf 167) R_36 G_36 1 [(VAR 0,1,0),(VAR 1,2,0),(VAR 7,128,0)] 4 = true := by decide +kernel
lemma sl_247_89 : Slice R_247 G_247 (subcubeFast 64 16) 4 := slice_fast_of sl_247_89_ok (fun _ => low_36)
lemma sl_247_90_ok : sliceCheck 20 32 1 R_247 G_247 (varsOf 195) R_194 G_194 4 [(VAR 0,1,0)] 5 = true := by decide +kernel
lemma sl_247_90 : Slice R_247 G_247 (subcubeFast 20 32) 5 := slice_fast_of sl_247_90_ok (fun _ => low_194)
lemma sl_247_91_ok : sliceCheck 48 0 1 R_247 G_247 (varsOf 199) R_198 G_198 5 [] 5 = true := by decide +kernel
lemma sl_247_91 : Slice R_247 G_247 (subcubeFast 48 0) 5 := slice_fast_of sl_247_91_ok (fun _ => low_198)
lemma sl_247_92_ok : sliceCheck 192 2 16 R_247 G_247 (varsOf 53) R_37 G_37 2 [(VAR 4,16,0)] 3 = true := by decide +kernel
lemma sl_247_92 : Slice R_247 G_247 (subcubeFast 192 2) 3 := slice_fast_of sl_247_92_ok (fun _ => low_37)
lemma sl_247_93_ok : sliceCheck 128 112 7 R_247 G_247 (varsOf 7) [] 0 0 [(VAR 0,1,0),(VAR 1,2,0),(VAR 2,4,0)] 2 = true := by decide +kernel
lemma sl_247_93 : Slice R_247 G_247 (subcubeFast 128 112) 2 := slice_fast_of sl_247_93_ok (fun h => (h rfl).elim)
lemma sl_247_94_ok : sliceCheck 20 0 0 R_247 G_247 (varsOf 227) R_227 G_227 6 [] 6 = true := by decide +kernel
lemma sl_247_94 : Slice R_247 G_247 (subcubeFast 20 0) 6 := slice_fast_of sl_247_94_ok (fun _ => low_227)
lemma sl_247_95_ok : sliceCheck 4 1 48 R_247 G_247 (varsOf 242) R_194 G_194 4 [(VAR 4,16,0),(VAR 5,32,0)] 6 = true := by decide +kernel
lemma sl_247_95 : Slice R_247 G_247 (subcubeFast 4 1) 6 := slice_fast_of sl_247_95_ok (fun _ => low_194)
lemma sl_247_96_ok : sliceCheck 5 32 0 R_247 G_247 (varsOf 210) R_210 G_210 5 [] 5 = true := by decide +kernel
lemma sl_247_96 : Slice R_247 G_247 (subcubeFast 5 32) 5 := slice_fast_of sl_247_96_ok (fun _ => low_210)
lemma sl_247_97_ok : sliceCheck 65 32 4 R_247 G_247 (varsOf 150) R_146 G_146 4 [(VAR 2,4,0)] 5 = true := by decide +kernel
lemma sl_247_97 : Slice R_247 G_247 (subcubeFast 65 32) 5 := slice_fast_of sl_247_97_ok (fun _ => low_146)
lemma sl_247_98_ok : sliceCheck 18 96 133 R_247 G_247 (varsOf 133) [] 0 0 [(VAR 0,1,0),(VAR 2,4,0),(VAR 7,128,0)] 2 = true := by decide +kernel
lemma sl_247_98 : Slice R_247 G_247 (subcubeFast 18 96) 2 := slice_fast_of sl_247_98_ok (fun h => (h rfl).elim)
lemma sl_247_99_ok : sliceCheck 146 1 32 R_247 G_247 (varsOf 100) R_68 G_68 1 [(VAR 5,32,0)] 2 = true := by decide +kernel
lemma sl_247_99 : Slice R_247 G_247 (subcubeFast 146 1) 2 := slice_fast_of sl_247_99_ok (fun _ => low_68)
lemma sl_247_100_ok : sliceCheck 0 129 118 R_247 G_247 (varsOf 118) [] 0 0 [(VAR 1,2,0),(VAR 4,16,0),(VAR 5,32,0),(VAR 6,64,0)] 3 = true := by decide +kernel
lemma sl_247_100 : Slice R_247 G_247 (subcubeFast 0 129) 3 := slice_fast_of sl_247_100_ok (fun h => (h rfl).elim)
lemma sl_247_101_ok : sliceCheck 34 80 133 R_247 G_247 (varsOf 133) [] 0 0 [(VAR 0,1,0),(VAR 2,4,0),(VAR 7,128,0)] 2 = true := by decide +kernel
lemma sl_247_101 : Slice R_247 G_247 (subcubeFast 34 80) 2 := slice_fast_of sl_247_101_ok (fun h => (h rfl).elim)
lemma sl_247_102_ok : sliceCheck 0 3 244 R_247 G_247 (varsOf 244) [] 0 0 [(VAR 4,16,0),(VAR 5,32,0),(VAR 6,64,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_102 : Slice R_247 G_247 (subcubeFast 0 3) 3 := slice_fast_of sl_247_102_ok (fun h => (h rfl).elim)
lemma sl_247_103_ok : sliceCheck 16 34 197 R_247 G_247 (varsOf 197) [] 0 0 [(VAR 0,1,0),(VAR 2,4,0),(VAR 6,64,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_103 : Slice R_247 G_247 (subcubeFast 16 34) 3 := slice_fast_of sl_247_103_ok (fun h => (h rfl).elim)
lemma sl_247_104_ok : sliceCheck 146 64 4 R_247 G_247 (varsOf 37) R_33 G_33 1 [(VAR 2,4,0)] 2 = true := by decide +kernel
lemma sl_247_104 : Slice R_247 G_247 (subcubeFast 146 64) 2 := slice_fast_of sl_247_104_ok (fun _ => low_33)
lemma sl_247_105_ok : sliceCheck 130 16 1 R_247 G_247 (varsOf 101) R_100 G_100 2 [(VAR 0,1,0)] 3 = true := by decide +kernel
lemma sl_247_105 : Slice R_247 G_247 (subcubeFast 130 16) 3 := slice_fast_of sl_247_105_ok (fun _ => low_100)
lemma sl_247_106_ok : sliceCheck 4 3 240 R_247 G_247 (varsOf 240) [] 0 0 [(VAR 4,16,0),(VAR 5,32,0),(VAR 6,64,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_106 : Slice R_247 G_247 (subcubeFast 4 3) 3 := slice_fast_of sl_247_106_ok (fun h => (h rfl).elim)
lemma sl_247_107_ok : sliceCheck 0 112 135 R_247 G_247 (varsOf 135) [] 0 0 [(VAR 0,1,0),(VAR 1,2,0),(VAR 2,4,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_107 : Slice R_247 G_247 (subcubeFast 0 112) 3 := slice_fast_of sl_247_107_ok (fun h => (h rfl).elim)
lemma sl_247_108_ok : sliceCheck 1 128 82 R_247 G_247 (varsOf 118) R_36 G_36 1 [(VAR 1,2,0),(VAR 4,16,0),(VAR 6,64,0)] 4 = true := by decide +kernel
lemma sl_247_108 : Slice R_247 G_247 (subcubeFast 1 128) 4 := slice_fast_of sl_247_108_ok (fun _ => low_36)
lemma sl_247_109_ok : sliceCheck 65 0 0 R_247 G_247 (varsOf 182) R_182 G_182 6 [] 6 = true := by decide +kernel
lemma sl_247_109 : Slice R_247 G_247 (subcubeFast 65 0) 6 := slice_fast_of sl_247_109_ok (fun _ => low_182)
lemma sl_247_110_ok : sliceCheck 65 4 32 R_247 G_247 (varsOf 178) R_146 G_146 4 [(VAR 5,32,0)] 5 = true := by decide +kernel
lemma sl_247_110 : Slice R_247 G_247 (subcubeFast 65 4) 5 := slice_fast_of sl_247_110_ok (fun _ => low_146)
lemma sl_247_111_ok : sliceCheck 3 0 0 R_247 G_247 (varsOf 244) R_244 G_244 5 [] 5 = true := by decide +kernel
lemma sl_247_111 : Slice R_247 G_247 (subcubeFast 3 0) 5 := slice_fast_of sl_247_111_ok (fun _ => low_244)
lemma sl_247_112_ok : sliceCheck 132 3 112 R_247 G_247 (varsOf 112) [] 0 0 [(VAR 4,16,0),(VAR 5,32,0),(VAR 6,64,0)] 2 = true := by decide +kernel
lemma sl_247_112 : Slice R_247 G_247 (subcubeFast 132 3) 2 := slice_fast_of sl_247_112_ok (fun h => (h rfl).elim)
lemma sl_247_113_ok : sliceCheck 0 7 240 R_247 G_247 (varsOf 240) [] 0 0 [(VAR 4,16,0),(VAR 5,32,0),(VAR 6,64,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_113 : Slice R_247 G_247 (subcubeFast 0 7) 3 := slice_fast_of sl_247_113_ok (fun h => (h rfl).elim)
lemma sl_247_114_ok : sliceCheck 36 1 16 R_247 G_247 (varsOf 210) R_194 G_194 4 [(VAR 4,16,0)] 5 = true := by decide +kernel
lemma sl_247_114 : Slice R_247 G_247 (subcubeFast 36 1) 5 := slice_fast_of sl_247_114_ok (fun _ => low_194)
lemma sl_247_115_ok : sliceCheck 2 133 112 R_247 G_247 (varsOf 112) [] 0 0 [(VAR 4,16,0),(VAR 5,32,0),(VAR 6,64,0)] 2 = true := by decide +kernel
lemma sl_247_115 : Slice R_247 G_247 (subcubeFast 2 133) 2 := slice_fast_of sl_247_115_ok (fun h => (h rfl).elim)
lemma sl_247_116_ok : sliceCheck 68 0 0 R_247 G_247 (varsOf 179) R_179 G_179 7 [] 7 = true := by decide +kernel
lemma sl_247_116 : Slice R_247 G_247 (subcubeFast 68 0) 7 := slice_fast_of sl_247_116_ok (fun _ => low_179)
lemma sl_247_117_ok : sliceCheck 1 4 96 R_247 G_247 (varsOf 242) R_146 G_146 4 [(VAR 5,32,0),(VAR 6,64,0)] 6 = true := by decide +kernel
lemma sl_247_117 : Slice R_247 G_247 (subcubeFast 1 4) 6 := slice_fast_of sl_247_117_ok (fun _ => low_146)
lemma sl_247_118_ok : sliceCheck 129 0 0 R_247 G_247 (varsOf 118) R_118 G_118 5 [] 5 = true := by decide +kernel
lemma sl_247_118 : Slice R_247 G_247 (subcubeFast 129 0) 5 := slice_fast_of sl_247_118_ok (fun _ => low_118)
lemma sl_247_119_ok : sliceCheck 16 64 134 R_247 G_247 (varsOf 167) R_33 G_33 1 [(VAR 1,2,0),(VAR 2,4,0),(VAR 7,128,0)] 4 = true := by decide +kernel
lemma sl_247_119 : Slice R_247 G_247 (subcubeFast 16 64) 4 := slice_fast_of sl_247_119_ok (fun _ => low_33)
lemma sl_247_120_ok : sliceCheck 66 0 0 R_247 G_247 (varsOf 181) R_181 G_181 5 [] 5 = true := by decide +kernel
lemma sl_247_120 : Slice R_247 G_247 (subcubeFast 66 0) 5 := slice_fast_of sl_247_120_ok (fun _ => low_181)
lemma sl_247_121_ok : sliceCheck 16 96 135 R_247 G_247 (varsOf 135) [] 0 0 [(VAR 0,1,0),(VAR 1,2,0),(VAR 2,4,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_121 : Slice R_247 G_247 (subcubeFast 16 96) 3 := slice_fast_of sl_247_121_ok (fun h => (h rfl).elim)
lemma sl_247_122_ok : sliceCheck 70 0 0 R_247 G_247 (varsOf 177) R_177 G_177 4 [] 4 = true := by decide +kernel
lemma sl_247_122 : Slice R_247 G_247 (subcubeFast 70 0) 4 := slice_fast_of sl_247_122_ok (fun _ => low_177)
lemma sl_247_123_ok : sliceCheck 144 64 6 R_247 G_247 (varsOf 39) R_33 G_33 1 [(VAR 1,2,0),(VAR 2,4,0)] 3 = true := by decide +kernel
lemma sl_247_123 : Slice R_247 G_247 (subcubeFast 144 64) 3 := slice_fast_of sl_247_123_ok (fun _ => low_33)
lemma sl_247_124_ok : sliceCheck 192 16 3 R_247 G_247 (varsOf 39) R_36 G_36 1 [(VAR 0,1,0),(VAR 1,2,0)] 3 = true := by decide +kernel
lemma sl_247_124 : Slice R_247 G_247 (subcubeFast 192 16) 3 := slice_fast_of sl_247_124_ok (fun _ => low_36)
lemma sl_247_125_ok : sliceCheck 66 128 16 R_247 G_247 (varsOf 53) R_37 G_37 2 [(VAR 4,16,0)] 3 = true := by decide +kernel
lemma sl_247_125 : Slice R_247 G_247 (subcubeFast 66 128) 3 := slice_fast_of sl_247_125_ok (fun _ => low_37)
lemma sl_247_126_ok : sliceCheck 130 5 112 R_247 G_247 (varsOf 112) [] 0 0 [(VAR 4,16,0),(VAR 5,32,0),(VAR 6,64,0)] 2 = true := by decide +kernel
lemma sl_247_126 : Slice R_247 G_247 (subcubeFast 130 5) 2 := slice_fast_of sl_247_126_ok (fun h => (h rfl).elim)
lemma sl_247_127_ok : sliceCheck 69 32 0 R_247 G_247 (varsOf 146) R_146 G_146 4 [] 4 = true := by decide +kernel
lemma sl_247_127 : Slice R_247 G_247 (subcubeFast 69 32) 4 := slice_fast_of sl_247_127_ok (fun _ => low_146)
lemma sl_247_128_ok : sliceCheck 35 0 0 R_247 G_247 (varsOf 212) R_212 G_212 4 [] 4 = true := by decide +kernel
lemma sl_247_128 : Slice R_247 G_247 (subcubeFast 35 0) 4 := slice_fast_of sl_247_128_ok (fun _ => low_212)
lemma sl_247_129_ok : sliceCheck 0 1 48 R_247 G_247 (varsOf 246) R_198 G_198 5 [(VAR 4,16,0),(VAR 5,32,0)] 7 = true := by decide +kernel
lemma sl_247_129 : Slice R_247 G_247 (subcubeFast 0 1) 7 := slice_fast_of sl_247_129_ok (fun _ => low_198)
lemma sl_247_130_ok : sliceCheck 161 0 0 R_247 G_247 (varsOf 86) R_86 G_86 4 [] 4 = true := by decide +kernel
lemma sl_247_130 : Slice R_247 G_247 (subcubeFast 161 0) 4 := slice_fast_of sl_247_130_ok (fun _ => low_86)
lemma sl_247_131_ok : sliceCheck 19 0 0 R_247 G_247 (varsOf 228) R_228 G_228 4 [] 4 = true := by decide +kernel
lemma sl_247_131 : Slice R_247 G_247 (subcubeFast 19 0) 4 := slice_fast_of sl_247_131_ok (fun _ => low_228)
lemma sl_247_132_ok : sliceCheck 160 1 16 R_247 G_247 (varsOf 86) R_70 G_70 2 [(VAR 4,16,0)] 3 = true := by decide +kernel
lemma sl_247_132 : Slice R_247 G_247 (subcubeFast 160 1) 3 := slice_fast_of sl_247_132_ok (fun _ => low_70)
lemma sl_247_133_ok : sliceCheck 194 16 1 R_247 G_247 (varsOf 37) R_36 G_36 1 [(VAR 0,1,0)] 2 = true := by decide +kernel
lemma sl_247_133 : Slice R_247 G_247 (subcubeFast 194 16) 2 := slice_fast_of sl_247_133_ok (fun _ => low_36)
lemma sl_247_134_ok : sliceCheck 128 4 96 R_247 G_247 (varsOf 115) R_19 G_19 2 [(VAR 5,32,0),(VAR 6,64,0)] 4 = true := by decide +kernel
lemma sl_247_134 : Slice R_247 G_247 (subcubeFast 128 4) 4 := slice_fast_of sl_247_134_ok (fun _ => low_19)
lemma sl_247_135_ok : sliceCheck 2 4 96 R_247 G_247 (varsOf 241) R_145 G_145 2 [(VAR 5,32,0),(VAR 6,64,0)] 4 = true := by decide +kernel
lemma sl_247_135 : Slice R_247 G_247 (subcubeFast 2 4) 4 := slice_fast_of sl_247_135_ok (fun _ => low_145)
lemma sl_247_136_ok : sliceCheck 5 0 32 R_247 G_247 (varsOf 242) R_210 G_210 5 [] 5 = true := by decide +kernel
lemma sl_247_136 : Slice R_247 G_247 (subcubeFast 5 0) 5 := slice_fast_of sl_247_136_ok (fun _ => low_210)
lemma sl_247_137_ok : sliceCheck 34 1 16 R_247 G_247 (varsOf 212) R_196 G_196 2 [(VAR 4,16,0)] 3 = true := by decide +kernel
lemma sl_247_137 : Slice R_247 G_247 (subcubeFast 34 1) 3 := slice_fast_of sl_247_137_ok (fun _ => low_196)
lemma sl_247_138_ok : sliceCheck 37 0 0 R_247 G_247 (varsOf 210) R_210 G_210 5 [] 5 = true := by decide +kernel
lemma sl_247_138 : Slice R_247 G_247 (subcubeFast 37 0) 5 := slice_fast_of sl_247_138_ok (fun _ => low_210)
lemma sl_247_139_ok : sliceCheck 18 128 64 R_247 G_247 (varsOf 101) R_37 G_37 2 [(VAR 6,64,0)] 3 = true := by decide +kernel
lemma sl_247_139 : Slice R_247 G_247 (subcubeFast 18 128) 3 := slice_fast_of sl_247_139_ok (fun _ => low_37)
lemma sl_247_140_ok : sliceCheck 0 4 96 R_247 G_247 (varsOf 243) R_147 G_147 5 [(VAR 5,32,0),(VAR 6,64,0)] 7 = true := by decide +kernel
lemma sl_247_140 : Slice R_247 G_247 (subcubeFast 0 4) 7 := slice_fast_of sl_247_140_ok (fun _ => low_147)
lemma sl_247_141_ok : sliceCheck 4 34 209 R_247 G_247 (varsOf 209) [] 0 0 [(VAR 0,1,0),(VAR 4,16,0),(VAR 6,64,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_141 : Slice R_247 G_247 (subcubeFast 4 34) 3 := slice_fast_of sl_247_141_ok (fun h => (h rfl).elim)
lemma sl_247_142_ok : sliceCheck 0 132 115 R_247 G_247 (varsOf 115) [] 0 0 [(VAR 1,2,0),(VAR 4,16,0),(VAR 5,32,0),(VAR 6,64,0)] 3 = true := by decide +kernel
lemma sl_247_142 : Slice R_247 G_247 (subcubeFast 0 132) 3 := slice_fast_of sl_247_142_ok (fun h => (h rfl).elim)
lemma sl_247_143_ok : sliceCheck 80 2 128 R_247 G_247 (varsOf 165) R_37 G_37 2 [(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_143 : Slice R_247 G_247 (subcubeFast 80 2) 3 := slice_fast_of sl_247_143_ok (fun _ => low_37)
lemma sl_247_144_ok : sliceCheck 128 65 54 R_247 G_247 (varsOf 54) [] 0 0 [(VAR 1,2,0),(VAR 2,4,0),(VAR 4,16,0),(VAR 5,32,0)] 3 = true := by decide +kernel
lemma sl_247_144 : Slice R_247 G_247 (subcubeFast 128 65) 3 := slice_fast_of sl_247_144_ok (fun h => (h rfl).elim)
lemma sl_247_145_ok : sliceCheck 129 6 112 R_247 G_247 (varsOf 112) [] 0 0 [(VAR 4,16,0),(VAR 5,32,0),(VAR 6,64,0)] 2 = true := by decide +kernel
lemma sl_247_145 : Slice R_247 G_247 (subcubeFast 129 6) 2 := slice_fast_of sl_247_145_ok (fun h => (h rfl).elim)
lemma sl_247_146_ok : sliceCheck 97 4 0 R_247 G_247 (varsOf 146) R_146 G_146 4 [] 4 = true := by decide +kernel
lemma sl_247_146 : Slice R_247 G_247 (subcubeFast 97 4) 4 := slice_fast_of sl_247_146_ok (fun _ => low_146)
lemma sl_247_147_ok : sliceCheck 3 16 128 R_247 G_247 (varsOf 228) R_100 G_100 2 [(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_147 : Slice R_247 G_247 (subcubeFast 3 16) 3 := slice_fast_of sl_247_147_ok (fun _ => low_100)
lemma sl_247_148_ok : sliceCheck 128 34 85 R_247 G_247 (varsOf 85) [] 0 0 [(VAR 0,1,0),(VAR 2,4,0),(VAR 4,16,0),(VAR 6,64,0)] 3 = true := by decide +kernel
lemma sl_247_148 : Slice R_247 G_247 (subcubeFast 128 34) 3 := slice_fast_of sl_247_148_ok (fun h => (h rfl).elim)
lemma sl_247_149_ok : sliceCheck 52 0 1 R_247 G_247 (varsOf 195) R_194 G_194 4 [] 4 = true := by decide +kernel
lemma sl_247_149 : Slice R_247 G_247 (subcubeFast 52 0) 4 := slice_fast_of sl_247_149_ok (fun _ => low_194)
lemma sl_247_150_ok : sliceCheck 66 16 129 R_247 G_247 (varsOf 165) R_36 G_36 1 [(VAR 0,1,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_150 : Slice R_247 G_247 (subcubeFast 66 16) 3 := slice_fast_of sl_247_150_ok (fun _ => low_36)
lemma sl_247_151_ok : sliceCheck 68 128 18 R_247 G_247 (varsOf 51) R_33 G_33 1 [(VAR 1,2,0),(VAR 4,16,0)] 3 = true := by decide +kernel
lemma sl_247_151 : Slice R_247 G_247 (subcubeFast 68 128) 3 := slice_fast_of sl_247_151_ok (fun _ => low_33)
lemma sl_247_152_ok : sliceCheck 16 65 166 R_247 G_247 (varsOf 166) [] 0 0 [(VAR 1,2,0),(VAR 2,4,0),(VAR 5,32,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_152 : Slice R_247 G_247 (subcubeFast 16 65) 3 := slice_fast_of sl_247_152_ok (fun h => (h rfl).elim)
lemma sl_247_153_ok : sliceCheck 64 20 163 R_247 G_247 (varsOf 163) [] 0 0 [(VAR 0,1,0),(VAR 1,2,0),(VAR 5,32,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_153 : Slice R_247 G_247 (subcubeFast 64 20) 3 := slice_fast_of sl_247_153_ok (fun h => (h rfl).elim)
lemma sl_247_154_ok : sliceCheck 82 128 0 R_247 G_247 (varsOf 37) R_37 G_37 2 [] 2 = true := by decide +kernel
lemma sl_247_154 : Slice R_247 G_247 (subcubeFast 82 128) 2 := slice_fast_of sl_247_154_ok (fun _ => low_37)
lemma sl_247_155_ok : sliceCheck 0 6 241 R_247 G_247 (varsOf 241) [] 0 0 [(VAR 4,16,0),(VAR 5,32,0),(VAR 6,64,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_155 : Slice R_247 G_247 (subcubeFast 0 6) 3 := slice_fast_of sl_247_155_ok (fun h => (h rfl).elim)
lemma sl_247_156_ok : sliceCheck 192 0 0 R_247 G_247 (varsOf 55) R_55 G_55 5 [] 5 = true := by decide +kernel
lemma sl_247_156 : Slice R_247 G_247 (subcubeFast 192 0) 5 := slice_fast_of sl_247_156_ok (fun _ => low_55)
lemma sl_247_157_ok : sliceCheck 18 32 5 R_247 G_247 (varsOf 197) R_192 G_192 1 [(VAR 0,1,0),(VAR 2,4,0)] 3 = true := by decide +kernel
lemma sl_247_157 : Slice R_247 G_247 (subcubeFast 18 32) 3 := slice_fast_of sl_247_157_ok (fun _ => low_192)
lemma sl_247_158_ok : sliceCheck 144 0 0 R_247 G_247 (varsOf 103) R_103 G_103 5 [] 5 = true := by decide +kernel
lemma sl_247_158 : Slice R_247 G_247 (subcubeFast 144 0) 5 := slice_fast_of sl_247_158_ok (fun _ => low_103)
lemma sl_247_159_ok : sliceCheck 97 0 4 R_247 G_247 (varsOf 150) R_146 G_146 4 [] 4 = true := by decide +kernel
lemma sl_247_159 : Slice R_247 G_247 (subcubeFast 97 0) 4 := slice_fast_of sl_247_159_ok (fun _ => low_146)
lemma sl_247_160_ok : sliceCheck 16 133 98 R_247 G_247 (varsOf 98) [] 0 0 [(VAR 1,2,0),(VAR 5,32,0),(VAR 6,64,0)] 2 = true := by decide +kernel
lemma sl_247_160 : Slice R_247 G_247 (subcubeFast 16 133) 2 := slice_fast_of sl_247_160_ok (fun h => (h rfl).elim)
lemma sl_247_161_ok : sliceCheck 128 20 99 R_247 G_247 (varsOf 99) [] 0 0 [(VAR 0,1,0),(VAR 1,2,0),(VAR 5,32,0),(VAR 6,64,0)] 3 = true := by decide +kernel
lemma sl_247_161 : Slice R_247 G_247 (subcubeFast 128 20) 3 := slice_fast_of sl_247_161_ok (fun h => (h rfl).elim)
lemma sl_247_162_ok : sliceCheck 129 16 2 R_247 G_247 (varsOf 102) R_100 G_100 2 [(VAR 1,2,0)] 3 = true := by decide +kernel
lemma sl_247_162 : Slice R_247 G_247 (subcubeFast 129 16) 3 := slice_fast_of sl_247_162_ok (fun _ => low_100)
lemma sl_247_163_ok : sliceCheck 128 7 112 R_247 G_247 (varsOf 112) [] 0 0 [(VAR 4,16,0),(VAR 5,32,0),(VAR 6,64,0)] 2 = true := by decide +kernel
lemma sl_247_163 : Slice R_247 G_247 (subcubeFast 128 7) 2 := slice_fast_of sl_247_163_ok (fun h => (h rfl).elim)
lemma sl_247_164_ok : sliceCheck 130 4 96 R_247 G_247 (varsOf 113) R_17 G_17 1 [(VAR 5,32,0),(VAR 6,64,0)] 3 = true := by decide +kernel
lemma sl_247_164 : Slice R_247 G_247 (subcubeFast 130 4) 3 := slice_fast_of sl_247_164_ok (fun _ => low_17)
lemma sl_247_165_ok : sliceCheck 132 64 2 R_247 G_247 (varsOf 51) R_49 G_49 2 [(VAR 1,2,0)] 3 = true := by decide +kernel
lemma sl_247_165 : Slice R_247 G_247 (subcubeFast 132 64) 3 := slice_fast_of sl_247_165_ok (fun _ => low_49)
lemma sl_247_166_ok : sliceCheck 20 3 224 R_247 G_247 (varsOf 224) [] 0 0 [(VAR 5,32,0),(VAR 6,64,0),(VAR 7,128,0)] 2 = true := by decide +kernel
lemma sl_247_166 : Slice R_247 G_247 (subcubeFast 20 3) 2 := slice_fast_of sl_247_166_ok (fun h => (h rfl).elim)
lemma sl_247_167_ok : sliceCheck 6 0 0 R_247 G_247 (varsOf 241) R_241 G_241 5 [] 5 = true := by decide +kernel
lemma sl_247_167 : Slice R_247 G_247 (subcubeFast 6 0) 5 := slice_fast_of sl_247_167_ok (fun _ => low_241)
lemma sl_247_168_ok : sliceCheck 144 2 64 R_247 G_247 (varsOf 101) R_37 G_37 2 [(VAR 6,64,0)] 3 = true := by decide +kernel
lemma sl_247_168 : Slice R_247 G_247 (subcubeFast 144 2) 3 := slice_fast_of sl_247_168_ok (fun _ => low_37)
lemma sl_247_169_ok : sliceCheck 4 0 0 R_247 G_247 (varsOf 243) R_243 G_243 8 [] 8 = true := by decide +kernel
lemma sl_247_169 : Slice R_247 G_247 (subcubeFast 4 0) 8 := slice_fast_of sl_247_169_ok (fun _ => low_243)
lemma sl_247_170_ok : sliceCheck 130 1 48 R_247 G_247 (varsOf 116) R_68 G_68 1 [(VAR 4,16,0),(VAR 5,32,0)] 3 = true := by decide +kernel
lemma sl_247_170 : Slice R_247 G_247 (subcubeFast 130 1) 3 := slice_fast_of sl_247_170_ok (fun _ => low_68)
lemma sl_247_171_ok : sliceCheck 32 133 82 R_247 G_247 (varsOf 82) [] 0 0 [(VAR 1,2,0),(VAR 4,16,0),(VAR 6,64,0)] 2 = true := by decide +kernel
lemma sl_247_171 : Slice R_247 G_247 (subcubeFast 32 133) 2 := slice_fast_of sl_247_171_ok (fun h => (h rfl).elim)
lemma sl_247_172_ok : sliceCheck 2 160 85 R_247 G_247 (varsOf 85) [] 0 0 [(VAR 0,1,0),(VAR 2,4,0),(VAR 4,16,0),(VAR 6,64,0)] 3 = true := by decide +kernel
lemma sl_247_172 : Slice R_247 G_247 (subcubeFast 2 160) 3 := slice_fast_of sl_247_172_ok (fun h => (h rfl).elim)
lemma sl_247_173_ok : sliceCheck 208 2 0 R_247 G_247 (varsOf 37) R_37 G_37 2 [] 2 = true := by decide +kernel
lemma sl_247_173 : Slice R_247 G_247 (subcubeFast 208 2) 2 := slice_fast_of sl_247_173_ok (fun _ => low_37)
lemma sl_247_174_ok : sliceCheck 1 160 86 R_247 G_247 (varsOf 86) [] 0 0 [(VAR 1,2,0),(VAR 2,4,0),(VAR 4,16,0),(VAR 6,64,0)] 3 = true := by decide +kernel
lemma sl_247_174 : Slice R_247 G_247 (subcubeFast 1 160) 3 := slice_fast_of sl_247_174_ok (fun h => (h rfl).elim)
lemma sl_247_175_ok : sliceCheck 4 160 83 R_247 G_247 (varsOf 83) [] 0 0 [(VAR 0,1,0),(VAR 1,2,0),(VAR 4,16,0),(VAR 6,64,0)] 3 = true := by decide +kernel
lemma sl_247_175 : Slice R_247 G_247 (subcubeFast 4 160) 3 := slice_fast_of sl_247_175_ok (fun h => (h rfl).elim)
lemma sl_247_176_ok : sliceCheck 16 160 71 R_247 G_247 (varsOf 71) [] 0 0 [(VAR 0,1,0),(VAR 1,2,0),(VAR 2,4,0),(VAR 6,64,0)] 3 = true := by decide +kernel
lemma sl_247_176 : Slice R_247 G_247 (subcubeFast 16 160) 3 := slice_fast_of sl_247_176_ok (fun h => (h rfl).elim)
lemma sl_247_177_ok : sliceCheck 80 5 32 R_247 G_247 (varsOf 162) R_130 G_130 1 [(VAR 5,32,0)] 2 = true := by decide +kernel
lemma sl_247_177 : Slice R_247 G_247 (subcubeFast 80 5) 2 := slice_fast_of sl_247_177_ok (fun _ => low_130)
lemma sl_247_178_ok : sliceCheck 2 65 180 R_247 G_247 (varsOf 180) [] 0 0 [(VAR 2,4,0),(VAR 4,16,0),(VAR 5,32,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_178 : Slice R_247 G_247 (subcubeFast 2 65) 3 := slice_fast_of sl_247_178_ok (fun h => (h rfl).elim)
lemma sl_247_179_ok : sliceCheck 80 32 5 R_247 G_247 (varsOf 135) R_130 G_130 1 [(VAR 0,1,0),(VAR 2,4,0)] 3 = true := by decide +kernel
lemma sl_247_179 : Slice R_247 G_247 (subcubeFast 80 32) 3 := slice_fast_of sl_247_179_ok (fun _ => low_130)
lemma sl_247_180_ok : sliceCheck 134 64 0 R_247 G_247 (varsOf 49) R_49 G_49 2 [] 2 = true := by decide +kernel
lemma sl_247_180 : Slice R_247 G_247 (subcubeFast 134 64) 2 := slice_fast_of sl_247_180_ok (fun _ => low_49)
lemma sl_247_181_ok : sliceCheck 64 7 176 R_247 G_247 (varsOf 176) [] 0 0 [(VAR 4,16,0),(VAR 5,32,0),(VAR 7,128,0)] 2 = true := by decide +kernel
lemma sl_247_181 : Slice R_247 G_247 (subcubeFast 64 7) 2 := slice_fast_of sl_247_181_ok (fun h => (h rfl).elim)
lemma sl_247_182_ok : sliceCheck 64 34 149 R_247 G_247 (varsOf 149) [] 0 0 [(VAR 0,1,0),(VAR 2,4,0),(VAR 4,16,0),(VAR 7,128,0)] 3 = true := by decide +kernel
lemma sl_247_182 : Slice R_247 G_247 (subcubeFast 64 34) 3 := slice_fast_of sl_247_182_ok (fun h => (h rfl).elim)
lemma sl_247_183_ok : sliceCheck 132 2 80 R_247 G_247 (varsOf 113) R_33 G_33 1 [(VAR 4,16,0),(VAR 6,64,0)] 3 = true := by decide +kernel
lemma sl_247_183 : Slice R_247 G_247 (subcubeFast 132 2) 3 := slice_fast_of sl_247_183_ok (fun _ => low_33)
lemma sl_247_184_ok : sliceCheck 194 4 32 R_247 G_247 (varsOf 49) R_17 G_17 1 [(VAR 5,32,0)] 2 = true := by decide +kernel
lemma sl_247_184 : Slice R_247 G_247 (subcubeFast 194 4) 2 := slice_fast_of sl_247_184_ok (fun _ => low_17)
lemma sl_247_185_ok : sliceCheck 131 16 0 R_247 G_247 (varsOf 100) R_100 G_100 2 [] 2 = true := by decide +kernel
lemma sl_247_185 : Slice R_247 G_247 (subcubeFast 131 16) 2 := slice_fast_of sl_247_185_ok (fun _ => low_100)
lemma sl_247_186_ok : sliceCheck 144 34 69 R_247 G_247 (varsOf 69) [] 0 0 [(VAR 0,1,0),(VAR 2,4,0),(VAR 6,64,0)] 2 = true := by decide +kernel
lemma sl_247_186 : Slice R_247 G_247 (subcubeFast 144 34) 2 := slice_fast_of sl_247_186_ok (fun h => (h rfl).elim)
lemma sl_247_187_ok : sliceCheck 162 1 16 R_247 G_247 (varsOf 84) R_68 G_68 1 [(VAR 4,16,0)] 2 = true := by decide +kernel
lemma sl_247_187 : Slice R_247 G_247 (subcubeFast 162 1) 2 := slice_fast_of sl_247_187_ok (fun _ => low_68)
set_option maxRecDepth 500000 in
lemma slices_247_ok : btAll (fun o => ∀ p, o = some p → Slice R_247 G_247 p.1 p.2) slices_247 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_247 G_247 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_247_0) (forall_cons (fun _ h => by cases h; exact sl_247_1) (forall_cons (fun _ h => by cases h; exact sl_247_2) (forall_cons (fun _ h => by cases h; exact sl_247_3) (forall_cons (fun _ h => by cases h; exact sl_247_4) (forall_cons (fun _ h => by cases h; exact sl_247_5) (forall_cons (fun _ h => by cases h; exact sl_247_6) (forall_cons (fun _ h => by cases h; exact sl_247_7) (forall_cons (fun _ h => by cases h; exact sl_247_8) (forall_cons (fun _ h => by cases h; exact sl_247_9) (forall_cons (fun _ h => by cases h; exact sl_247_10) (forall_cons (fun _ h => by cases h; exact sl_247_11) (forall_cons (fun _ h => by cases h; exact sl_247_12) (forall_cons (fun _ h => by cases h; exact sl_247_13) (forall_cons (fun _ h => by cases h; exact sl_247_14) (forall_cons (fun _ h => by cases h; exact sl_247_15) (forall_cons (fun _ h => by cases h; exact sl_247_16) (forall_cons (fun _ h => by cases h; exact sl_247_17) (forall_cons (fun _ h => by cases h; exact sl_247_18) (forall_cons (fun _ h => by cases h; exact sl_247_19) (forall_cons (fun _ h => by cases h; exact sl_247_20) (forall_cons (fun _ h => by cases h; exact sl_247_21) (forall_cons (fun _ h => by cases h; exact sl_247_22) (forall_cons (fun _ h => by cases h; exact sl_247_23) (forall_cons (fun _ h => by cases h; exact sl_247_24) (forall_cons (fun _ h => by cases h; exact sl_247_25) (forall_cons (fun _ h => by cases h; exact sl_247_26) (forall_cons (fun _ h => by cases h; exact sl_247_27) (forall_cons (fun _ h => by cases h; exact sl_247_28) (forall_cons (fun _ h => by cases h; exact sl_247_29) (forall_cons (fun _ h => by cases h; exact sl_247_30) (forall_cons (fun _ h => by cases h; exact sl_247_31) (forall_cons (fun _ h => by cases h; exact sl_247_32) (forall_cons (fun _ h => by cases h; exact sl_247_33) (forall_cons (fun _ h => by cases h; exact sl_247_34) (forall_cons (fun _ h => by cases h; exact sl_247_35) (forall_cons (fun _ h => by cases h; exact sl_247_36) (forall_cons (fun _ h => by cases h; exact sl_247_37) (forall_cons (fun _ h => by cases h; exact sl_247_38) (forall_cons (fun _ h => by cases h; exact sl_247_39) (forall_cons (fun _ h => by cases h; exact sl_247_40) (forall_cons (fun _ h => by cases h; exact sl_247_41) (forall_cons (fun _ h => by cases h; exact sl_247_42) (forall_cons (fun _ h => by cases h; exact sl_247_43) (forall_cons (fun _ h => by cases h; exact sl_247_44) (forall_cons (fun _ h => by cases h; exact sl_247_45) (forall_cons (fun _ h => by cases h; exact sl_247_46) (forall_cons (fun _ h => by cases h; exact sl_247_47) (forall_cons (fun _ h => by cases h; exact sl_247_48) (forall_cons (fun _ h => by cases h; exact sl_247_49) (forall_cons (fun _ h => by cases h; exact sl_247_50) (forall_cons (fun _ h => by cases h; exact sl_247_51) (forall_cons (fun _ h => by cases h; exact sl_247_52) (forall_cons (fun _ h => by cases h; exact sl_247_53) (forall_cons (fun _ h => by cases h; exact sl_247_54) (forall_cons (fun _ h => by cases h; exact sl_247_55) (forall_cons (fun _ h => by cases h; exact sl_247_56) (forall_cons (fun _ h => by cases h; exact sl_247_57) (forall_cons (fun _ h => by cases h; exact sl_247_58) (forall_cons (fun _ h => by cases h; exact sl_247_59) (forall_cons (fun _ h => by cases h; exact sl_247_60) (forall_cons (fun _ h => by cases h; exact sl_247_61) (forall_cons (fun _ h => by cases h; exact sl_247_62) (forall_cons (fun _ h => by cases h; exact sl_247_63) (forall_cons (fun _ h => by cases h; exact sl_247_64) (forall_cons (fun _ h => by cases h; exact sl_247_65) (forall_cons (fun _ h => by cases h; exact sl_247_66) (forall_cons (fun _ h => by cases h; exact sl_247_67) (forall_cons (fun _ h => by cases h; exact sl_247_68) (forall_cons (fun _ h => by cases h; exact sl_247_69) (forall_cons (fun _ h => by cases h; exact sl_247_70) (forall_cons (fun _ h => by cases h; exact sl_247_71) (forall_cons (fun _ h => by cases h; exact sl_247_72) (forall_cons (fun _ h => by cases h; exact sl_247_73) (forall_cons (fun _ h => by cases h; exact sl_247_74) (forall_cons (fun _ h => by cases h; exact sl_247_75) (forall_cons (fun _ h => by cases h; exact sl_247_76) (forall_cons (fun _ h => by cases h; exact sl_247_77) (forall_cons (fun _ h => by cases h; exact sl_247_78) (forall_cons (fun _ h => by cases h; exact sl_247_79) (forall_cons (fun _ h => by cases h; exact sl_247_80) (forall_cons (fun _ h => by cases h; exact sl_247_81) (forall_cons (fun _ h => by cases h; exact sl_247_82) (forall_cons (fun _ h => by cases h; exact sl_247_83) (forall_cons (fun _ h => by cases h; exact sl_247_84) (forall_cons (fun _ h => by cases h; exact sl_247_85) (forall_cons (fun _ h => by cases h; exact sl_247_86) (forall_cons (fun _ h => by cases h; exact sl_247_87) (forall_cons (fun _ h => by cases h; exact sl_247_88) (forall_cons (fun _ h => by cases h; exact sl_247_89) (forall_cons (fun _ h => by cases h; exact sl_247_90) (forall_cons (fun _ h => by cases h; exact sl_247_91) (forall_cons (fun _ h => by cases h; exact sl_247_92) (forall_cons (fun _ h => by cases h; exact sl_247_93) (forall_cons (fun _ h => by cases h; exact sl_247_94) (forall_cons (fun _ h => by cases h; exact sl_247_95) (forall_cons (fun _ h => by cases h; exact sl_247_96) (forall_cons (fun _ h => by cases h; exact sl_247_97) (forall_cons (fun _ h => by cases h; exact sl_247_98) (forall_cons (fun _ h => by cases h; exact sl_247_99) (forall_cons (fun _ h => by cases h; exact sl_247_100) (forall_cons (fun _ h => by cases h; exact sl_247_101) (forall_cons (fun _ h => by cases h; exact sl_247_102) (forall_cons (fun _ h => by cases h; exact sl_247_103) (forall_cons (fun _ h => by cases h; exact sl_247_104) (forall_cons (fun _ h => by cases h; exact sl_247_105) (forall_cons (fun _ h => by cases h; exact sl_247_106) (forall_cons (fun _ h => by cases h; exact sl_247_107) (forall_cons (fun _ h => by cases h; exact sl_247_108) (forall_cons (fun _ h => by cases h; exact sl_247_109) (forall_cons (fun _ h => by cases h; exact sl_247_110) (forall_cons (fun _ h => by cases h; exact sl_247_111) (forall_cons (fun _ h => by cases h; exact sl_247_112) (forall_cons (fun _ h => by cases h; exact sl_247_113) (forall_cons (fun _ h => by cases h; exact sl_247_114) (forall_cons (fun _ h => by cases h; exact sl_247_115) (forall_cons (fun _ h => by cases h; exact sl_247_116) (forall_cons (fun _ h => by cases h; exact sl_247_117) (forall_cons (fun _ h => by cases h; exact sl_247_118) (forall_cons (fun _ h => by cases h; exact sl_247_119) (forall_cons (fun _ h => by cases h; exact sl_247_120) (forall_cons (fun _ h => by cases h; exact sl_247_121) (forall_cons (fun _ h => by cases h; exact sl_247_122) (forall_cons (fun _ h => by cases h; exact sl_247_123) (forall_cons (fun _ h => by cases h; exact sl_247_124) (forall_cons (fun _ h => by cases h; exact sl_247_125) (forall_cons (fun _ h => by cases h; exact sl_247_126) (forall_cons (fun _ h => by cases h; exact sl_247_127) (forall_cons (fun _ h => by cases h; exact sl_247_128) (forall_cons (fun _ h => by cases h; exact sl_247_129) (forall_cons (fun _ h => by cases h; exact sl_247_130) (forall_cons (fun _ h => by cases h; exact sl_247_131) (forall_cons (fun _ h => by cases h; exact sl_247_132) (forall_cons (fun _ h => by cases h; exact sl_247_133) (forall_cons (fun _ h => by cases h; exact sl_247_134) (forall_cons (fun _ h => by cases h; exact sl_247_135) (forall_cons (fun _ h => by cases h; exact sl_247_136) (forall_cons (fun _ h => by cases h; exact sl_247_137) (forall_cons (fun _ h => by cases h; exact sl_247_138) (forall_cons (fun _ h => by cases h; exact sl_247_139) (forall_cons (fun _ h => by cases h; exact sl_247_140) (forall_cons (fun _ h => by cases h; exact sl_247_141) (forall_cons (fun _ h => by cases h; exact sl_247_142) (forall_cons (fun _ h => by cases h; exact sl_247_143) (forall_cons (fun _ h => by cases h; exact sl_247_144) (forall_cons (fun _ h => by cases h; exact sl_247_145) (forall_cons (fun _ h => by cases h; exact sl_247_146) (forall_cons (fun _ h => by cases h; exact sl_247_147) (forall_cons (fun _ h => by cases h; exact sl_247_148) (forall_cons (fun _ h => by cases h; exact sl_247_149) (forall_cons (fun _ h => by cases h; exact sl_247_150) (forall_cons (fun _ h => by cases h; exact sl_247_151) (forall_cons (fun _ h => by cases h; exact sl_247_152) (forall_cons (fun _ h => by cases h; exact sl_247_153) (forall_cons (fun _ h => by cases h; exact sl_247_154) (forall_cons (fun _ h => by cases h; exact sl_247_155) (forall_cons (fun _ h => by cases h; exact sl_247_156) (forall_cons (fun _ h => by cases h; exact sl_247_157) (forall_cons (fun _ h => by cases h; exact sl_247_158) (forall_cons (fun _ h => by cases h; exact sl_247_159) (forall_cons (fun _ h => by cases h; exact sl_247_160) (forall_cons (fun _ h => by cases h; exact sl_247_161) (forall_cons (fun _ h => by cases h; exact sl_247_162) (forall_cons (fun _ h => by cases h; exact sl_247_163) (forall_cons (fun _ h => by cases h; exact sl_247_164) (forall_cons (fun _ h => by cases h; exact sl_247_165) (forall_cons (fun _ h => by cases h; exact sl_247_166) (forall_cons (fun _ h => by cases h; exact sl_247_167) (forall_cons (fun _ h => by cases h; exact sl_247_168) (forall_cons (fun _ h => by cases h; exact sl_247_169) (forall_cons (fun _ h => by cases h; exact sl_247_170) (forall_cons (fun _ h => by cases h; exact sl_247_171) (forall_cons (fun _ h => by cases h; exact sl_247_172) (forall_cons (fun _ h => by cases h; exact sl_247_173) (forall_cons (fun _ h => by cases h; exact sl_247_174) (forall_cons (fun _ h => by cases h; exact sl_247_175) (forall_cons (fun _ h => by cases h; exact sl_247_176) (forall_cons (fun _ h => by cases h; exact sl_247_177) (forall_cons (fun _ h => by cases h; exact sl_247_178) (forall_cons (fun _ h => by cases h; exact sl_247_179) (forall_cons (fun _ h => by cases h; exact sl_247_180) (forall_cons (fun _ h => by cases h; exact sl_247_181) (forall_cons (fun _ h => by cases h; exact sl_247_182) (forall_cons (fun _ h => by cases h; exact sl_247_183) (forall_cons (fun _ h => by cases h; exact sl_247_184) (forall_cons (fun _ h => by cases h; exact sl_247_185) (forall_cons (fun _ h => by cases h; exact sl_247_186) (forall_cons (fun _ h => by cases h; exact sl_247_187) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def ps_247 : BT (Option PoolSpec) := btOfList 9 [some (0,[]),some (1,[]),some (2,[]),some (3,[]),some (4,[]),some (5,[]),some (6,[]),some (7,[]),some (8,[]),some (9,[]),some (10,[]),some (11,[]),some (12,[]),some (13,[]),some (14,[]),some (15,[]),some (16,[]),some (17,[]),some (18,[]),some (19,[]),some (20,[]),some (21,[]),some (22,[]),some (23,[]),some (24,[]),some (25,[]),some (26,[]),some (27,[]),some (28,[]),some (29,[]),some (30,[]),some (31,[]),some (32,[]),some (33,[]),some (34,[]),some (35,[]),some (36,[]),some (37,[]),some (38,[]),some (39,[]),some (40,[]),some (41,[]),some (42,[]),some (43,[]),some (44,[]),some (45,[]),some (46,[]),some (47,[]),some (48,[]),some (49,[]),some (10,[(1,0,5)]),some (50,[]),some (51,[]),some (52,[]),some (53,[]),some (54,[]),some (55,[]),some (56,[]),some (57,[]),some (58,[]),some (59,[]),some (60,[]),some (61,[]),some (62,[]),some (63,[]),some (64,[]),some (65,[]),some (66,[]),some (67,[]),some (68,[]),some (69,[]),some (70,[]),some (71,[]),some (72,[]),some (73,[]),some (10,[(1,3,5),(2,8,11)]),some (10,[(2,3,4),(1,23,2)]),some (74,[]),some (75,[]),some (76,[]),some (77,[]),some (78,[(1,1,6),(3,3,11)]),some (79,[]),some (10,[(1,3,4),(3,0,9)]),some (80,[]),some (81,[]),some (82,[]),some (83,[]),some (84,[]),some (85,[]),some (86,[]),some (87,[]),some (88,[]),some (71,[(1,1,3),(2,19,6)]),some (89,[]),some (90,[]),some (91,[]),some (92,[]),some (93,[]),some (10,[(1,3,5),(2,8,6)]),some (94,[]),some (95,[]),some (96,[]),some (97,[]),some (98,[]),some (99,[]),some (100,[]),some (101,[]),some (102,[]),some (103,[]),some (104,[]),some (105,[]),some (106,[]),some (107,[]),some (88,[(1,1,4)]),some (108,[]),some (10,[(2,0,5),(1,20,5)]),some (109,[]),some (110,[]),some (111,[]),some (112,[]),some (113,[]),some (114,[]),some (115,[]),some (10,[(1,0,2),(2,16,4)]),some (116,[]),some (117,[]),some (118,[]),some (119,[]),some (120,[]),some (121,[]),some (122,[]),some (123,[]),some (124,[]),some (125,[]),some (126,[]),some (127,[]),some (128,[]),some (129,[]),some (131,[]),some (88,[(1,0,5)]),some (132,[]),some (133,[]),some (10,[(1,0,11),(3,3,35)]),some (134,[]),some (135,[]),some (136,[]),some (137,[]),some (138,[]),some (139,[]),some (140,[]),some (78,[]),some (141,[]),some (142,[]),some (143,[]),some (144,[]),some (145,[]),some (10,[(2,0,11),(1,32,5)]),some (10,[(2,3,5),(1,7,2)]),some (10,[(1,19,5),(2,26,6)]),some (146,[]),some (147,[]),some (88,[(1,3,5),(3,1,8)]),some (148,[]),some (150,[]),some (151,[]),some (152,[]),some (153,[]),some (154,[]),some (155,[]),some (156,[]),some (157,[]),some (158,[]),some (10,[(1,0,5),(1,14,6)]),some (159,[]),some (160,[]),some (161,[]),some (162,[]),some (163,[]),some (10,[(2,0,2),(1,18,5)]),some (164,[]),some (140,[(1,1,6)]),some (165,[]),some (166,[]),some (167,[]),some (168,[]),some (10,[(1,0,5),(1,2,3)]),some (10,[(1,3,5)]),some (88,[(1,3,5)]),some (88,[(2,3,4),(1,23,2)]),some (10,[(1,4,11)]),some (88,[(1,4,11)]),some (169,[]),some (170,[]),some (171,[]),some (10,[(3,3,4)]),some (78,[(1,1,6)]),some (3,[(1,1,6)]),some (10,[(1,3,4)]),some (10,[(2,0,11)]),some (173,[]),some (10,[(1,0,11)]),some (174,[]),some (175,[]),some (176,[]),some (10,[(2,14,6)]),some (10,[(1,4,6)]),some (10,[(1,19,5)]),some (71,[(1,1,3)]),some (88,[(3,3,4),(1,17,1)]),some (10,[(3,0,5)]),some (10,[(2,0,5)]),some (88,[(2,0,5),(1,20,5)]),some (116,[(1,20,1)]),some (88,[(1,0,1)]),some (88,[(2,0,2),(1,18,5)]),some (10,[(2,0,2)]),some (88,[(1,0,2),(2,16,4)]),some (177,[]),some (178,[]),some (179,[]),some (73,[(3,1,8)]),some (71,[(3,1,8)]),some (180,[]),some (10,[(2,3,5)]),some (10,[(1,2,19)]),some (181,[]),some (182,[]),some (10,[(1,15,6)]),some (10,[(1,2,3)]),some (88,[(1,0,5),(1,2,3)]),some (88,[(1,2,3)]),some (71,[(1,0,1)]),some (10,[(2,4,5)]),some (129,[(1,1,6)]),some (10,[(1,2,6)]),some (183,[]),some (10,[(1,0,2)]),some (72,[(1,1,6)]),some (88,[(1,0,5),(1,1,4)]),some (116,[(1,0,1)]),some (10,[(3,3,5)]),some (10,[(1,15,5)]),some (88,[(2,0,1),(1,15,5)]),some (10,[(2,4,11)]),some (184,[]),some (185,[]),some (10,[(1,12,6)]),some (88,[(3,1,4)]),some (10,[(1,10,6)]),some (10,[(3,3,14)]),some (10,[(1,4,5)]),some (186,[]),some (187,[]),some (10,[(2,3,4)]),some (10,[(1,14,6)]),some (10,[(2,2,3)]),some (10,[(2,10,5)]),some (10,[(2,10,6)]),some (73,[(1,19,5)]),some (88,[(1,3,4),(3,0,9)]),some (10,[(1,10,5)]),some (88,[(2,3,5),(1,7,2)]),some (88,[(2,3,5)]),some (88,[(1,3,4)]),some (26,[(1,1,6)]),some (75,[(1,1,6)]),some (77,[(1,1,6)]),some (116,[(1,1,6)]),some (88,[(2,0,1)]),some (88,[(1,0,2)]),some (88,[(3,3,4)]),some (88,[(2,0,2)]),some (116,[(1,1,3)]),some (88,[(2,0,5)]),some (88,[(3,0,5)]),some (88,[(2,3,4)]),some (88,[(3,0,1)])]
def bk_247_init : BT (List (List Nat)) := BT.empty
lemma bk_247_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_247 (0 - 1) xs.toFinset) bk_247_init := trivial
def nodes_247_0 : List NodeSpec := []
def P_247_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_247 R_247 slices_247 ps_247 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_247_0 : checkNodesBT W_247 G_247 fmask_247 P_247_0 autos_247 bk_247_init 0 nodes_247_0 = true := by decide +kernel
def bk_247_0 : BT (List (List Nat)) := buildBucketsBT W_247 nodes_247_0
set_option maxRecDepth 500000 in
lemma bk_247_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_247 0 xs.toFinset) bk_247_0 :=
  buildBucketsBT_sound (by decide) gp_247 W_247_ok (buildPoolsSubBT_sound slices_247_ok) autos_247_ok bk_247_init_ok chk_247_0
def nodes_247_1 : List NodeSpec := []
def P_247_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_247 R_247 slices_247 ps_247 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_247_1 : checkNodesBT W_247 G_247 fmask_247 P_247_1 autos_247 bk_247_0 1 nodes_247_1 = true := by decide +kernel
def bk_247_1 : BT (List (List Nat)) := buildBucketsBT W_247 nodes_247_1
set_option maxRecDepth 500000 in
lemma bk_247_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_247 1 xs.toFinset) bk_247_1 :=
  buildBucketsBT_sound (by decide) gp_247 W_247_ok (buildPoolsSubBT_sound slices_247_ok) autos_247_ok bk_247_0_ok chk_247_1
def nodes_247_2 : List NodeSpec := []
def P_247_2 : BT (Option BoundPool) := buildPoolsSubBT 9 W_247 R_247 slices_247 ps_247 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_247_2 : checkNodesBT W_247 G_247 fmask_247 P_247_2 autos_247 bk_247_1 2 nodes_247_2 = true := by decide +kernel
def bk_247_2 : BT (List (List Nat)) := buildBucketsBT W_247 nodes_247_2
set_option maxRecDepth 500000 in
lemma bk_247_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_247 2 xs.toFinset) bk_247_2 :=
  buildBucketsBT_sound (by decide) gp_247 W_247_ok (buildPoolsSubBT_sound slices_247_ok) autos_247_ok bk_247_1_ok chk_247_2
def nodes_247_3 : List NodeSpec := []
def P_247_3 : BT (Option BoundPool) := buildPoolsSubBT 9 W_247 R_247 slices_247 ps_247 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_247_3 : checkNodesBT W_247 G_247 fmask_247 P_247_3 autos_247 bk_247_2 3 nodes_247_3 = true := by decide +kernel
def bk_247_3 : BT (List (List Nat)) := buildBucketsBT W_247 nodes_247_3
set_option maxRecDepth 500000 in
lemma bk_247_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_247 3 xs.toFinset) bk_247_3 :=
  buildBucketsBT_sound (by decide) gp_247 W_247_ok (buildPoolsSubBT_sound slices_247_ok) autos_247_ok bk_247_2_ok chk_247_3
def nodes_247_4 : List NodeSpec := []
def P_247_4 : BT (Option BoundPool) := buildPoolsSubBT 9 W_247 R_247 slices_247 ps_247 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_247_4 : checkNodesBT W_247 G_247 fmask_247 P_247_4 autos_247 bk_247_3 4 nodes_247_4 = true := by decide +kernel
def bk_247_4 : BT (List (List Nat)) := buildBucketsBT W_247 nodes_247_4
set_option maxRecDepth 500000 in
lemma bk_247_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_247 4 xs.toFinset) bk_247_4 :=
  buildBucketsBT_sound (by decide) gp_247 W_247_ok (buildPoolsSubBT_sound slices_247_ok) autos_247_ok bk_247_3_ok chk_247_4
def nodes_247_5 : List NodeSpec := []
def P_247_5 : BT (Option BoundPool) := buildPoolsSubBT 9 W_247 R_247 slices_247 ps_247 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_247_5 : checkNodesBT W_247 G_247 fmask_247 P_247_5 autos_247 bk_247_4 5 nodes_247_5 = true := by decide +kernel
def bk_247_5 : BT (List (List Nat)) := buildBucketsBT W_247 nodes_247_5
set_option maxRecDepth 500000 in
lemma bk_247_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_247 5 xs.toFinset) bk_247_5 :=
  buildBucketsBT_sound (by decide) gp_247 W_247_ok (buildPoolsSubBT_sound slices_247_ok) autos_247_ok bk_247_4_ok chk_247_5
def nodes_247_6 : List NodeSpec := [([82,0,1,2,3,4,5],[0,1,2],[]),([0,88,2,19,8,6],[7,8,4,5,6],[]),([0,2,19,4,5,11,132],[10,6,9],[]),([0,2,19,4,8,11,36],[6,9,11],[]),([82,1,2,3,4,21],[15,16,13],[]),([39,10,2,4,8,6],[21,22,19,20],[]),([98,10,2,8,6],[25,6,5],[]),([31,10,46,4,5,6],[22,29,27],[]),([10,2,19,8,52,6],[30,31,32],[]),([10,2,19,8,6,38],[22,30,3,21,6],[]),([10,2,4,8,11,36],[34,35,32],[]),([10,2,19,5,77,38],[36,30,22,37,15,38],[]),([1,46,21,72],[29],[]),([10,2,4,8,6,78],[28,40,22],[]),([10,19,4,8,6,53],[22,42,30,31,33],[]),([25,0,2,3,4,5,122],[43,1,2],[]),([2,19,4,21,11,77],[23,49,45,50,48,54,44,46,47,52,53,51],[]),([10,2,4,8,11,77],[28,55],[]),([39,0,1,2,8,38],[21,22],[]),([63,2,19,4,8,6],[33,22,3,42,31],[])]
def P_247_6 : BT (Option BoundPool) := buildPoolsSubBT 9 W_247 R_247 slices_247 ps_247 [0,1,2,3,4,5,6,7,8,9,10,11,13,15,16,19,20,21,22,23,25,27,28,29,30,31,32,33,34,35,36,37,38,40,42,43,44,45,46,47,48,49,50,51,52,53,54,55]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_247_6 : checkNodesBT W_247 G_247 fmask_247 P_247_6 autos_247 bk_247_5 6 nodes_247_6 = true := by decide +kernel
def bk_247_6 : BT (List (List Nat)) := buildBucketsBT W_247 nodes_247_6
set_option maxRecDepth 500000 in
lemma bk_247_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_247 6 xs.toFinset) bk_247_6 :=
  buildBucketsBT_sound (by decide) gp_247 W_247_ok (buildPoolsSubBT_sound slices_247_ok) autos_247_ok bk_247_5_ok chk_247_6
def nd_247_7_0 : List NodeSpec := [([82,0,1,2,3,4,8],[41,18,9,59,60],[]),([83,0,1,2,3,5,6],[36,61,63,65,12],[]),([62,0,1,2,8,6],[6,3,67,68],[]),([0,84,2,3,5,6,11],[70,5,71,44],[]),([85,0,1,2,3,4,5,6],[72,0,73,74,70,75,44],[]),([0,1,28,4,5,6,11],[47,29,76],[]),([31,0,1,2,4,9,5,6],[20,82,77,78,79,80,81],[]),([29,1,2,3,4,5,6,11],[82,29,53,62,83],[]),([7,0,1,2,5,6,72],[24,3,5,66,4],[]),([0,1,2,3,8,6,72],[22,3,33,24,2],[]),([86,0,1,2,3,5,72],[88,87,3],[]),([0,1,2,3,5,8,72],[90,3,24,32,5,84],[]),([0,1,2,3,5,87,6],[3,24,2,4,66,1,0,64],[]),([0,1,2,33,5,8,6],[4,24,9,5,17],[]),([0,1,2,33,8,6],[18,3,9,5],[]),([34,7,0,1,2,5,6],[23,67,5,33,44],[]),([0,88,2,3,19,5,6],[46,3,36,6,63],[0]),([39,0,1,2,3,5,38],[70,71,44,33,37,79],[0]),([0,1,2,3,4,5,89,6],[1,93,9,71],[]),([82,0,1,2,3,4,5,6],[64,68,9],[]),([82,0,1,2,3,4,5,26],[1,62,2,20,92],[]),([25,0,2,3,4,5,26,6],[6,72,2],[0]),([0,1,2,3,19,5,90],[94,3,18,9,62],[]),([0,1,2,33,19,5,6],[3,18,17,9,4,62],[]),([0,1,2,3,4,5,6,91],[1,2],[1,0]),([74,0,1,2,19,5,6],[23,9,17,95,94,62],[]),([92,0,1,2,3,5,6],[9,61,64,12,65,62],[]),([75,0,1,2,8,6],[19,7,4],[2]),([93,0,1,2,19,4,5,6],[98,99,97,31,74],[]),([55,0,1,2,19,8,6],[31,7,94,12],[0]),([25,0,2,19,4,5,8,6],[6,63,10],[]),([94,0,1,2,3,5,6],[23,86,95,94,62,73],[]),([37,0,1,2,19,8,6],[7,9,22],[]),([0,1,2,41,8,6],[9,23,67,5,3],[]),([25,0,2,19,4,8,6],[9,18,60,59,17,63,6],[]),([0,1,95,19,4,5,6],[13,95,9,94,62],[]),([0,1,2,3,5,72,96],[44,3,37,71,4],[]),([0,97,3,19,4,5,6],[9,42,94,95,13],[]),([1,2,3,69,6,38],[102,104,23,20,103,78,62],[]),([0,2,19,4,5,11,77],[22,56,105,110,109,19,63,44,46,107,10,106,108,82],[0,1]),([10,2,19,4,5,6,77],[97,42,23,37],[0]),([63,1,2,3,4,8,6],[111,33,42,3],[0]),([0,2,3,14,5,26,6],[112,36,113,114],[]),([34,20,1,2,3,5,6],[44,23,12,13,70,78,64,62],[]),([98,10,2,3,5,6],[91,5,36,58,1],[0]),([1,2,3,4,21,6,11],[29,49,112,116],[]),([1,10,2,4,8,6,36],[49,58,118,103],[0,3]),([1,2,3,14,21,6],[120,121,23],[]),([37,65,1,2,3,5,6],[122,68,3,36],[]),([99,0,1,19,4,5,6],[94,62,9,42,95],[]),([1,10,3,46,5,6,38],[123,111,29,23,15,38],[]),([50,0,1,2,3,5,6,11],[20,70,82,44,62,124],[]),([1,45,2,3,5,6,38],[21,23,20,62],[]),([1,2,3,5,52,6,59],[31,118,23,102,64],[]),([25,1,2,3,4,21,6],[31,121,53,112],[]),([100,1,2,3,4,21,6],[15,16,6,68,126,12,78],[2,3]),([101,1,2,3,4,21,6],[49,130,131,15,128],[]),([1,2,3,9,21,44,6],[132,67,13],[]),([15,1,2,4,8,6,36],[49,103,118,6],[]),([1,2,3,5,21,72],[104,24],[]),([1,2,3,14,21,6,36],[98,6,67,112,50],[]),([1,2,3,4,5,6,102],[118,33,103,62],[]),([1,2,3,14,21,8,6],[31,67,113],[]),([1,2,3,4,21,26,6],[15,112,68],[0]),([57,0,1,2,4,8,6],[68,17,58,14,16,12],[]),([0,2,3,19,4,5,11,36],[38,133,33,17],[0,3]),([1,10,2,3,5,6,103],[70,134,23],[]),([63,17,1,2,3,5,6],[90,42,5,77],[]),([1,2,3,21,6,72],[29,3,112,104],[]),([1,2,19,4,21,8,6],[31,42,23,50,57,94],[]),([1,3,46,4,21,6,11],[107,135,121],[]),([0,2,19,14,5,6,77],[113,23,95,37,86,10],[1]),([1,2,3,4,21,6,102],[38,136,70,118],[]),([1,46,4,21,6],[107,29,102,121],[]),([34,1,2,3,4,21,6],[29,23,137,78],[]),([0,2,3,4,5,26,6,11],[112,46,92],[1,3]),([1,2,3,4,21,6,78],[15,70,13,51],[]),([71,1,3,14,21,6],[107,112,121],[]),([63,7,1,2,4,5,6],[33,42,3,5,71],[]),([39,1,2,3,4,21,6],[29,139,113,15,47],[]),([1,2,19,4,21,6,77],[120,113,50,140],[0]),([0,1,81,14,5,6],[23,79,67,5,17,44],[]),([104,0,10,2,3,5,6],[141,23,112,103,78],[]),([1,19,46,4,21,6],[107,113,121,135,29],[]),([2,3,19,4,21,6,11],[120,23,53,121,107,49,140,47],[0]),([2,3,19,14,21,6],[120,113],[]),([71,1,3,4,21,6,11],[107,70,29],[]),([34,18,1,2,3,5,6],[70,23,67,13],[]),([1,2,3,14,48,6],[102,23,103,79,13,119,70],[]),([1,2,3,4,5,6,105],[5,69,6,20,37],[]),([106,0,1,2,4,5,6,11],[5,64,70,143],[]),([49,2,3,4,5,6,11],[5,20,32,145,115,144],[]),([107,0,1,2,3,5,6],[23,66,58,24,64],[]),([34,0,1,16,3,5,6],[147,23,103,115],[]),([0,1,3,4,5,6,108],[102,71,62,33],[]),([0,1,2,19,4,8,6,36],[15,97,149,1,2],[0]),([2,3,4,21,44,6,11],[132,121,89,140],[]),([15,1,2,8,52,6],[31,118],[]),([75,0,1,2,5,8,6],[97,4,67,41],[]),([109,1,2,3,4,5,6],[16,71,14,6,118,103,127],[]),([110,2,3,4,5,6,11],[5,71,69,20],[]),([61,1,2,3,4,8,6],[31,42,3,118],[]),([111,0,1,2,3,5,6],[71,23,95,62,73],[]),([31,1,2,3,4,21,6],[15,49,29,121,12,78,125],[]),([10,2,3,5,52,6,11],[109,31,152,62],[]),([1,2,3,4,69,6,36],[6,103,128,16,14],[]),([1,2,3,5,21,6,72],[104,70,24],[]),([45,2,3,4,5,6,11],[5,20,6,91,68,115],[]),([63,0,1,2,3,5,38],[44,3,37,71],[]),([1,2,3,4,79,6,36],[70,128,6,103],[]),([0,2,19,4,5,8,6,11],[31,90,9,15,11],[0]),([10,2,3,4,5,11,77],[109,70,154],[0]),([112,1,2,3,4,5,6],[33,6,69,20],[]),([63,0,1,46,4,5,6],[21,3,139],[]),([1,2,3,21,72],[104,3,39,66],[0]),([0,1,113,3,5,6],[155,23,85],[]),([0,1,2,3,4,5,6,114],[37,68,32,69,44],[]),([0,10,46,14,5,6],[156,136,3],[]),([1,10,2,3,5,115,6],[6,3,49,39,62],[]),([63,1,2,3,4,5,38],[122,37,3,71],[]),([116,1,10,2,3,5,6],[38,136,49,58],[]),([2,3,14,21,44,6],[120,113],[]),([10,3,19,4,5,6,53],[97,7,37],[0]),([10,2,3,19,5,6,38],[97,30,70],[0]),([65,1,2,3,5,6,38],[21,68,15,136,62],[]),([1,2,3,4,117,6,11],[37,5,69,20,6,157,117],[]),([1,10,2,3,5,6,118],[70,3,103,37],[]),([39,10,2,3,4,5,6],[97,139,70,20],[0]),([1,10,2,3,5,6,119],[102,37,58,23,62],[]),([1,10,2,3,8,52,6],[109,34,31,41,5],[0]),([1,49,2,3,5,6,38],[20,23,79,103,115],[]),([1,10,2,8,52,6],[31,58,118],[0]),([120,1,2,3,4,5,6],[101,56,64,77,1,62],[]),([0,84,2,3,19,5,6],[46,3,32,37,86,63],[]),([37,1,10,2,5,8,6],[7,49,58],[]),([121,0,1,2,3,5,6],[23,18,84,67,58,64],[]),([0,1,2,3,4,5,122,26],[1,62,2],[0]),([31,10,2,3,4,5,6],[55,49,20],[0]),([123,1,2,3,4,44,6],[25,49,103,15,68],[]),([0,1,2,19,8,6,38],[22,23,9,95],[0])]
def P_247_7_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_247 R_247 slices_247 ps_247 [0,1,2,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,29,30,31,32,33,34,36,37,38,39,41,42,44,46,47,49,50,51,53,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,97,98,99,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,130,131,132,133,134,135,136,137,139,140,141,143,144,145,147,149,152,154,155,156,157]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_247_7_0 : checkNodesBT W_247 G_247 fmask_247 P_247_7_0 autos_247 bk_247_6 7 nd_247_7_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_247_7_0 : ∀ ns ∈ nd_247_7_0, Impossible G_247 7 (nodeValsBT W_247 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_247 W_247_ok (buildPoolsSubBT_sound slices_247_ok) autos_247_ok bk_247_6_ok chk_247_7_0
def nd_247_7_1 : List NodeSpec := [([1,10,2,4,8,6,77],[22,42,41,23],[0]),([0,1,81,4,5,6,11],[44,22,6,46,109,158],[]),([124,2,3,4,5,6,11],[71,5,69,20],[]),([86,0,1,2,3,5,6],[3,18,5,94,64],[]),([82,0,1,2,3,19,4,5],[62,15,159,63],[]),([10,2,19,4,5,8,6],[97,42,3,6,15],[0]),([125,1,2,3,4,5,6],[1,101,56,62,64,77],[]),([17,1,10,2,5,8,6],[160,154,35,42,58,134,90],[]),([1,10,2,5,8,6,38],[136,49,3,58],[]),([1,10,2,9,5,8,6],[154,111,19,161,3],[]),([1,10,2,3,5,53,38],[30,39,136,37,122],[]),([0,1,2,3,4,5,6,126],[6,162,41,64],[]),([63,1,3,46,4,5,6],[90,5,3,42],[]),([7,1,10,2,5,6,38],[30,22,103,3],[]),([10,3,46,4,5,6,11],[154,22,152,41],[0]),([10,2,3,4,5,11,36],[154,70,163],[0]),([10,2,4,5,8,6,11],[31,40,109],[0]),([7,1,10,4,5,6,53],[22,118,42,30,102],[]),([1,10,3,9,5,6,53],[19,7,149,22,132],[]),([1,10,3,4,5,6,127],[134,42,102],[]),([1,10,46,4,5,6,77],[164,29,23],[]),([1,2,3,4,5,6,114],[33,37,1,69,82],[]),([1,10,46,4,5,8,6],[111,154,23,42],[]),([10,2,3,4,8,6,11],[111,109,55],[0]),([63,1,10,2,3,5,38],[70,36,137,3],[]),([0,1,2,3,128,5,6],[9,3,18,94,62],[]),([63,55,1,2,3,5,6],[122,71,3,32],[]),([29,1,2,19,4,5,6],[163,42,23,96,15,58],[]),([63,1,2,4,5,8,6],[31,71,97,153,20],[]),([63,1,2,46,4,5,6],[165,122,153,91],[]),([17,1,10,3,5,6,53],[160,42,20,82,91,37],[]),([74,0,1,2,5,8,6],[67,23,9,5],[]),([1,46,4,21,8,6],[107,113,42,118,135,29],[]),([1,10,3,46,5,52,6],[109,164,160,30,90],[]),([1,10,2,4,8,52,6],[109,25,31],[]),([129,10,3,4,5,6],[32,42,102,37,11],[]),([63,1,2,3,5,52,6],[31,165,90],[]),([0,1,2,3,5,130,6],[32,3,68,67],[]),([0,1,2,19,8,52,6],[31,95,23,94,2],[0]),([63,1,2,3,9,5,6],[111,42,82,3,128],[]),([0,2,19,4,44,8,6],[98,166,167,56,57,108,169],[]),([74,1,2,3,5,21,6],[27,67,23,133,32],[]),([34,0,2,3,19,5,6],[120,156,22,128],[]),([63,1,2,3,4,5,53],[122,71,37,42,126],[]),([57,0,2,3,14,5,6],[40,139,22,113],[]),([63,71,1,3,4,5,6],[90,101,5,3],[]),([0,1,2,3,5,6,131],[3,36,41,4,37],[]),([0,1,2,19,4,5,6,132],[15,10,97,37],[0]),([57,1,2,3,4,21,6],[130,6,68,16,15,126,78],[]),([133,1,10,3,4,5,6],[20,118,23,102,29,82],[]),([68,1,10,2,3,6,38],[22,30,103,3],[]),([39,0,1,2,4,8,6],[139,9,18,47,171],[0]),([1,10,2,3,5,77,38],[29,22,15,38],[0]),([0,1,2,4,8,6,78],[59,9,60,18,5,172],[0,1]),([1,2,3,5,79,6,38],[70,3,20,103],[]),([1,2,3,4,5,134,6],[16,6,14,128,64],[]),([39,0,1,2,4,5,8,6],[98,9,38,97,93,1,71],[]),([0,1,2,3,4,5,134,6],[48,36,71,15],[]),([135,1,2,3,4,5,6],[33,16,119,82],[]),([1,10,2,3,5,38,36],[70,149,136],[]),([1,2,4,5,8,6,35],[32,58,71,42,3],[]),([1,10,2,3,5,51,6],[31,102,23,20,62],[]),([12,1,46,21,6],[121,29],[0]),([136,0,10,2,3,4,5,6],[58,61,78,70,46],[]),([137,1,2,3,4,21,6],[132,29,89,129],[]),([29,1,2,9,8,6],[18,42,9,23,96],[]),([17,1,2,3,21,44,6],[89,66,94,112,12,26],[]),([1,2,3,21,6,30],[29,23,173],[]),([65,1,2,3,4,8,6],[161,68,42,15],[]),([133,1,10,3,5,52,6],[174,102,58,23,82],[]),([46,4,14,21,6],[102,3,39],[]),([104,0,2,3,5,6,11],[70,5,71,44],[]),([1,2,3,4,5,6,138],[118,37,33,14],[]),([0,1,42,2,5,8,6],[97,66,23,2],[2]),([1,10,2,3,5,54,6],[31,109,39,62],[]),([34,1,2,3,21,6],[120,175,29,78],[]),([65,1,3,4,5,6,53],[132,118,36,136],[]),([82,0,1,2,3,4,5,8],[1,2,12],[]),([25,0,2,3,19,4,5,6],[63,15,2],[]),([1,2,3,4,21,6,139],[15,16,13,115,170,129],[]),([68,10,2,3,4,6,11],[109,40,22],[]),([140,0,2,3,19,5,6],[166,27,132,95],[]),([0,2,19,4,8,6,11],[177,22,176,109,56,63],[1,3]),([13,46,4,21,6],[102,3,39],[]),([1,46,14,21,6],[178],[]),([1,10,2,3,8,6,38],[22,30,41,3,103],[0]),([34,1,2,3,5,21,6],[123,67,120,35,78],[]),([1,10,3,4,8,6,53],[19,22,118,56,102],[0]),([10,2,3,19,5,52,6],[30,97],[0]),([1,2,3,5,52,6,35],[122,3,58,20,82,1],[]),([0,1,2,3,141,5,6],[23,94,95,5,64,2],[]),([142,1,10,2,3,5,6],[30,160,109,41,90],[]),([1,2,3,4,48,6,11],[180,112,70,179,150,125],[]),([1,10,2,3,5,6,143],[37,3,103,102,41],[]),([1,10,2,9,8,6],[111,42],[]),([17,10,2,3,5,6,11],[109,154,55,37,17],[]),([10,2,3,9,5,6,11],[111,154,152],[]),([63,47,1,2,4,5,6],[90,69,5,3],[]),([12,1,2,3,21,6,36],[15,6,24,70],[]),([1,46,4,14,21,6],[107,102,121],[]),([144,1,2,3,4,5,6],[122,71,42,62],[]),([1,2,4,5,8,6,59],[31,118,23,33],[]),([55,10,2,3,5,6,11],[154,31,40],[]),([63,10,2,3,4,5,11],[5,119,20,32,91,36],[]),([10,2,3,4,5,11,53],[55,40,152,169,126,181],[]),([1,42,2,3,5,21,6],[112,38,25,24,23,71],[]),([1,2,3,19,21,6,38],[104,113,30,168],[]),([65,1,2,3,4,52,6],[20,68,3,118],[]),([63,2,3,19,4,5,6],[97,42,3],[0]),([65,1,2,3,9,5,6],[161,132,42],[]),([2,3,4,14,21,6,11],[183,47,78,120,121,140,12],[]),([1,3,4,5,79,6,53],[68,42,118,91,122],[]),([2,3,4,5,79,6,11],[70,68,5,20],[]),([7,10,2,4,5,6,11],[109,40,22],[]),([145,10,2,3,4,5,6],[185,39,118,70],[]),([133,1,3,4,21,6],[23,118,122,29,68],[]),([65,2,3,4,5,6,11],[132,182,20,29,119],[]),([71,1,10,3,5,6,38],[70,22,136],[]),([63,2,67,3,4,5,6],[97,122,42],[]),([146,1,10,2,3,5,6],[25,149,31,20],[]),([63,68,1,2,3,4,6],[42,71,5,3],[]),([0,1,2,54,8,6],[58,66,6,24,23],[]),([1,3,46,14,21,6],[107,113,3,121],[]),([1,2,3,4,69,6,138],[54,103,128,16,115],[]),([0,1,2,4,5,8,6,78],[15,32,31,72,71],[]),([147,1,10,2,3,5,6],[149,30,41,3,22,27],[]),([65,17,1,2,3,5,6],[89,42,5],[]),([34,0,1,2,3,8,6],[22,23,33,95,2,12],[]),([1,46,4,21,6,11],[135,29,121,186],[]),([71,10,3,4,5,6,11],[152,22,40],[]),([82,0,1,2,3,4,5],[58,18,62,82,9,0,70,1,44],[0,2]),([10,2,3,4,5,6,78],[5,32,20,91,37,17],[0]),([10,2,19,4,8,6],[3,42,41,22,154],[0])]
def P_247_7_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_247 R_247 slices_247 ps_247 [0,1,2,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19,20,22,23,24,25,26,27,29,30,31,32,33,35,36,37,38,39,40,41,42,44,46,47,48,49,54,55,56,57,58,59,60,61,62,63,64,66,67,68,69,70,71,72,77,78,82,89,90,91,93,94,95,96,97,98,101,102,103,104,107,108,109,111,112,113,115,118,119,120,121,122,123,125,126,128,129,130,132,133,134,135,136,137,139,140,149,150,152,153,154,156,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,185,186]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_247_7_1 : checkNodesBT W_247 G_247 fmask_247 P_247_7_1 autos_247 bk_247_6 7 nd_247_7_1 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_247_7_1 : ∀ ns ∈ nd_247_7_1, Impossible G_247 7 (nodeValsBT W_247 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_247 W_247_ok (buildPoolsSubBT_sound slices_247_ok) autos_247_ok bk_247_6_ok chk_247_7_1
def nodes_247_7 : List NodeSpec := nd_247_7_0 ++ nd_247_7_1
def bk_247_7 : BT (List (List Nat)) := buildBucketsBT W_247 nodes_247_7
set_option maxRecDepth 500000 in
lemma bk_247_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_247 7 xs.toFinset) bk_247_7 := buildBucketsBT_of_mem (forall_append (mem_247_7_0) mem_247_7_1)
def nd_247_8_0 : List NodeSpec := [([25,0,1,2,3,4,5,8,6],[6,41,187,12,74],[0,2]),([0,1,2,3,4,5,8,26,6],[1,2,187,130,129,17,188],[0]),([0,1,2,3,4,8,27,6],[41,95,118,9,125],[]),([25,0,1,2,3,4,8,6],[111,161,28,18,125,26,46],[0]),([0,1,28,4,5,6],[12,26,150,80,76,189],[0]),([0,1,2,9,5,8,6],[67,26,111,1],[0,1,2,3]),([29,1,2,3,9,5,6],[96,65,12,111,61],[2,3,0]),([0,1,2,3,5,6,11,30],[70,5,71,190,44,191,73],[0,1]),([31,0,1,2,3,4,5,6],[49,22,18,193,113,81,138,150,192,0,73,109,175,183,180,151],[0,1,2]),([0,1,2,3,4,5,8,6,11],[31,111,154,22,90,187,74,72],[0,2,1,3]),([17,0,1,2,3,5,6,11],[142,19,194,77,78,80,105,195,183,79,63],[0,1,2,3]),([17,0,1,2,5,8,6],[66,26,111,24,12],[0,1,2,3]),([0,1,2,3,4,9,5,6,11],[20,111,82,197,0,198,163,196],[0]),([0,1,2,4,9,5,6,11],[53,47,152,198],[]),([0,1,2,3,9,5,6,11],[142,19,175,3,105,78,80,111,22,198,183,0],[0,1,2,3]),([32,1,2,3,4,5,6,11],[5,71,11,20,69,199,138],[0,1]),([12,0,1,2,3,5,8,6],[200,66,3,4,24],[0,2]),([12,0,1,2,3,8,6],[7,187,41,154,4,24],[0,3,1]),([0,1,2,3,33,5,6],[3,80,133,5,78,17,0],[0,3,1]),([34,0,1,2,3,4,5,6],[84,61,65,63,12,64,73,86],[0,2]),([1,2,3,4,5,6,11,35],[5,71,11,20,69,201,151],[0,1]),([0,2,3,4,14,5,6,11],[47,203,204,202,114,73,0],[0,2]),([34,0,1,2,3,5,6],[70,205,90,44,114,61],[0,1,2,3]),([0,1,2,3,14,5,8,6],[200,23,67,187],[0,2]),([0,1,2,3,19,4,5,6,36],[15,97,149,49,22],[0,3]),([37,0,1,2,3,19,5,6],[168,7,79],[0,3]),([0,1,2,3,19,5,6,38],[168,23,95,206,92],[0,3,2,1]),([39,0,1,2,3,4,5,6],[139,22,82,38,176,93,192,150,0,73,98,44,171],[0,2,3]),([0,1,2,3,19,4,5,26,6],[62,207,22,15,129],[0]),([40,0,1,2,3,19,5,6],[9,17,3,18,94,63],[0]),([0,1,2,3,4,8,26,6],[9,187,18,59,60,188],[2,0]),([0,1,2,3,19,41,5,6],[9,17,23,94,95,3,62],[0]),([0,1,2,19,4,5,8,6],[187,26,208,18,63,66,168,9,57,170,46,3,17,12,100],[0]),([0,1,42,2,3,5,6],[63,78,97,80,195,209],[0,1,2,3]),([0,1,2,3,19,43,4,5,6],[42,18,17,184,62,2],[]),([0,2,3,19,4,5,6,11],[22,20,112,98,56,176,46,105,110,63,92,70,44,82],[0,1,2,3]),([0,2,3,19,4,5,44,6],[98,166,167,56,112,46,57,12,63],[0]),([22,0,1,2,3,4,6,11],[29,49,121,53,142,126,210,138,125,111],[0]),([22,0,1,2,3,14,6],[120,23,121],[0]),([20,1,2,3,4,5,6,11],[31,98,53,44,126,107,125,142,49,211,46,78,26,12,180],[0,1,2,3]),([1,2,3,4,21,6],[78,125,26,138,116,212],[0,1]),([1,45,2,3,4,5,6],[213,78,26,211,62,119],[0,3]),([0,1,2,3,4,5,21,6,11],[29,49,193,121,31,117,138,50,126,125],[]),([1,2,3,4,21,8,6],[3,125,31,50,140],[2,0,3,1]),([20,1,2,3,14,5,6],[102,98,12,23,13,78,119,62],[0,1,2,3]),([17,1,2,3,5,21,6],[25,142,26,24,77],[0,1]),([1,3,46,4,5,21,6],[15,42,118,142,113],[0]),([12,1,2,3,5,21,6],[25,3,50,24,120],[0]),([37,1,10,2,3,5,6],[122,3,214,36,84,39],[0]),([0,1,2,3,4,21,6,11],[183,194,126,138,121,50,125],[]),([0,1,2,3,14,21,6],[120,23,77,121],[]),([47,1,2,4,21,6],[135,102,66,121,29,26,125],[0]),([1,2,3,4,48,6],[57,78,26,125,179,215],[0,1]),([1,49,2,3,4,5,6],[57,78,26,101,216],[0]),([50,0,1,2,3,5,6],[77,150,63,12,78,80,124,217],[0]),([0,1,2,3,5,8,51,6],[58,18,6,9,3,66],[]),([0,1,16,3,5,52,6],[155,23,102,24,77],[0]),([0,1,16,3,4,5,44,6],[155,103,166,24,62],[]),([0,10,3,4,5,6,53],[42,118,102,115,127],[]),([0,1,16,3,14,5,6],[23,77,103,13,119,102],[0]),([25,0,1,2,3,4,5,6],[187,221,222,219,90,19,20,162,73,0,218,151,138,192,150,112,46,220],[0,2,1,3]),([24,0,2,3,5,6,38],[102,77,23,103,37],[]),([1,2,3,4,21,44,6],[15,125,50,12,128,117,129,26,78,140],[0,2,3,1]),([0,1,2,3,5,54,6],[24,78,63,31,80],[0,1]),([24,0,2,3,5,52,6],[25,58,23,118],[]),([24,0,2,4,5,8,6],[58,103,42,3,118],[]),([7,0,1,2,4,5,6,11],[223,155,66,49,47,26,12,219,224,109,56,57],[0,1,2,3]),([55,0,1,2,3,19,5,6],[110,7,12,57],[0,2]),([1,2,3,4,21,6,11],[183,140,197,50,29,125,126,12,117,121,49,78],[0,1]),([56,1,10,2,3,4,6],[163,102,23],[]),([15,1,2,3,4,5,6,36],[200,136,25,118],[0]),([15,1,2,4,5,8,6],[136,31,187,25,118,23],[0]),([0,1,3,19,43,4,5,6],[9,17,94,42,62,95,225],[0]),([2,3,4,14,21,6],[102,77,23],[0]),([57,0,1,2,3,4,5,6],[22,139,208,167,227,192,150,0,73,226,130,171],[0,2]),([58,1,10,2,3,4,5],[20,23,102,103],[]),([1,2,3,4,5,6,59],[26,36,78,64,126,228,102],[3,0]),([1,10,3,46,4,5,6],[3,142,229,42,15],[0,3]),([12,1,2,3,21,6],[3,50,39,66],[0]),([0,1,10,2,3,5,6,38],[29,23,103,77,206,102,92],[0]),([0,1,2,4,9,8,6],[67,3,111,26],[2,3]),([24,0,2,3,4,5,6,36],[70,25,49,58,118,103,138],[]),([1,3,46,4,21,6],[3,42,186,230],[0,1]),([60,0,1,3,19,4,5,6],[9,13,95,94,42,150],[0]),([0,1,10,2,3,5,52,6],[155,25,23,118,77],[]),([0,1,2,9,8,6],[111,26,18,100],[0,1,2,3]),([15,1,2,3,5,6,38],[102,23,103,206,37,78],[0]),([0,1,10,46,4,5,6],[3,118,29,46,139,231],[0]),([61,1,2,3,4,21,6],[103,101,56,112,54,118,77,140],[0]),([62,0,1,2,3,5,6],[3,67,31,4],[2,3,0]),([0,1,2,3,41,5,6],[61,65,12,63,62,17,3],[1,3,0]),([1,2,3,4,14,21,6],[102,77,23,50,98,140],[0]),([63,0,1,2,3,4,5,6],[119,77,56,101,155,64,151,150,72],[0,2]),([64,0,1,2,3,5,8,6],[6,9,66,3,12,63],[]),([55,1,10,2,3,5,6],[122,3,233,232],[0,3]),([1,2,46,4,21,6],[135,126,125,102,121,29,66],[]),([65,1,10,2,3,4,5,6],[97,119,56,77,101],[]),([65,0,1,2,3,4,5,6],[118,56,103,119,101,21,92],[0]),([0,1,2,3,4,21,44,6],[183,25,120,118,138],[]),([0,10,2,3,4,5,6,11],[175,194,21,234,126,101,92],[3]),([0,1,16,4,5,8,6],[155,136,3],[]),([1,2,3,9,5,21,6],[42,103,142,3],[2,0,3,1]),([0,10,2,3,14,5,6],[23,77,102,103,114,70],[0,3]),([7,0,1,2,14,5,6],[23,67,5,17,66],[0,1,3]),([17,1,10,2,3,5,6],[42,142,78,195],[0]),([1,10,2,3,4,5,6,36],[200,118,163,101,78,232,29,103],[0,3]),([1,2,3,19,4,21,6],[3,42,50,15,139,140],[0]),([0,1,2,3,19,5,52,6],[110,95,23,66,57],[0,2]),([1,10,3,4,5,6,53],[168,163,39,97,42,236,235,214],[0,3]),([1,10,2,3,4,5,6,38],[20,102,23,103,78,206,37],[0]),([1,2,3,19,4,5,21,6],[98,42,32,12,112,139,78],[0]),([0,1,2,16,3,4,5,6,11],[70,46,146,138,193,112,44,180,237,150,238],[0]),([66,0,1,3,4,5,6],[136,56,62,119,77],[0]),([1,2,3,14,21,6],[120,3,50,121,23,239],[2,0,1]),([10,2,67,3,4,5,6],[39,42,118,29],[0]),([0,1,2,19,4,8,6],[18,26,187,63,9,3,100,72],[0,1,3]),([1,10,2,3,4,5,8,6],[200,3,240,187],[0]),([68,1,10,2,3,4,6],[42,3,241,232],[0,3]),([1,2,3,4,69,6],[242,78,26,126,102,117,243],[0]),([0,1,2,3,4,5,6,11,35],[62,22,193,201,127,64,44,119],[0]),([0,1,10,2,4,5,8,6],[155,118,3,103,42],[]),([1,2,3,4,5,21,6,11],[31,49,98,57,29,227,50,107,125,142,140,121,12,117,78,138,180,26],[2,0,3,1]),([7,1,10,2,4,5,6],[42,3,224,232],[0]),([70,0,1,2,3,5,6,11],[70,5,71,44,244,0],[0,1]),([1,10,2,3,4,5,38],[20,23,102,103],[]),([18,1,2,3,4,5,6,11],[245,176,202,61,101,78,216,19,53,246,150,26],[0,1]),([71,1,3,4,21,6],[3,125,98,107],[0,1]),([0,1,2,3,5,6,72],[90,78,80,247,248,3,66],[0,2,1,3]),([1,10,2,4,9,5,6],[163,102,103],[]),([1,10,2,3,5,6,38],[168,29,206,214,3,102,79,97],[0]),([0,1,2,3,5,51,6],[61,31,65,63,12],[0,1,2,3]),([7,12,0,1,2,5,6],[24,3,5,17,66,4,63],[0]),([1,46,4,21,6],[42,118,3,186,230],[0,1]),([1,2,3,4,5,6,35],[56,101,77,249,214],[0]),([73,1,10,2,3,4,5],[118,42,102,91,184],[]),([1,10,2,4,5,8,6],[240,155,187,103,3],[0,3]),([0,1,2,3,5,72],[78,80,247,3,66],[0,2]),([74,0,1,2,3,5,6],[23,95,250,133],[0,1,2,3]),([1,10,2,3,5,52,6],[240,252,251,155,25,3],[0,3]),([75,0,1,2,3,5,6],[7,97,4,65],[0,2,3])]
def P_247_8_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_247 R_247 slices_247 ps_247 [0,1,2,3,4,5,6,7,9,11,12,13,15,17,18,19,20,21,22,23,24,25,26,28,29,31,32,36,37,38,39,41,42,44,46,47,49,50,53,54,56,57,58,59,60,61,62,63,64,65,66,67,69,70,71,72,73,74,76,77,78,79,80,81,82,84,86,90,91,92,93,94,95,96,97,98,100,101,102,103,105,107,109,110,111,112,113,114,115,116,117,118,119,120,121,122,124,125,126,127,128,129,130,133,135,136,138,139,140,142,146,149,150,151,152,154,155,161,162,163,166,167,168,170,171,175,176,179,180,183,184,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_247_8_0 : checkNodesBT W_247 G_247 fmask_247 P_247_8_0 autos_247 bk_247_7 8 nd_247_8_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_247_8_0 : ∀ ns ∈ nd_247_8_0, Impossible G_247 8 (nodeValsBT W_247 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_247 W_247_ok (buildPoolsSubBT_sound slices_247_ok) autos_247_ok bk_247_7_ok chk_247_8_0
def nd_247_8_1 : List NodeSpec := [([1,10,2,3,4,5,52,6],[163,25,23,78,101],[0]),([76,1,10,3,4,5,6],[42,240,214,102,91,184,62],[0]),([0,1,16,3,4,5,6,11],[253,105,234,155,102,219,237,78,125],[]),([23,0,1,2,4,5,6,11],[47,53,152,254,0,73],[0]),([0,1,2,3,5,6,30],[61,63,255,114,12,65],[0,2]),([0,1,2,19,4,5,6,77],[22,26,63,18,15,10,110,92,44,46],[0,1,2,3]),([0,1,2,19,4,9,5,6],[163,3,95,227],[0]),([1,10,2,3,4,5,6,77],[200,42,3,10],[0,3]),([0,1,2,3,4,5,6,78],[22,18,82,70,15,105,110,192,150,0,73,20,112,44,151,138,72],[0,1,2]),([1,10,2,3,4,5,6,53],[39,42,118,235,70,64],[0]),([1,10,2,3,4,8,6],[3,42,187,41,154,232],[0]),([1,10,2,3,9,5,6],[42,142,3,198],[0]),([71,1,10,3,4,5,6],[3,240,256],[0]),([76,15,1,3,4,5,6],[30,136,11,148,126,101,62,64],[]),([0,1,2,3,4,8,6,11],[111,3,19,175,204,26,63,105,125,22,187,109,183],[0,1,2,3]),([34,0,1,2,3,14,5,6],[120,63,12,114,156],[]),([1,2,3,4,21,52,6],[24,103,23,31,77,125],[0]),([63,1,10,2,3,4,5,6],[36,119,56,77,101,155,10,151],[0]),([0,10,2,3,5,6,38],[102,77,23,103,115],[]),([65,1,2,3,4,5,6],[240,15,257,103,32,56],[0]),([0,10,2,3,4,5,44,6],[155,136,166,118,232,138],[]),([1,2,3,14,5,21,6],[67,98,50,103,120,23],[0,2,3,1]),([0,1,2,3,4,5,6,11,30],[20,64,11,86,190,70,44,84],[]),([13,2,3,4,21,6],[102,23,77],[0]),([63,1,2,3,4,5,6],[90,258,122,82,36,214,150,165,42],[0]),([1,10,2,3,4,52,6],[163,102,23],[]),([15,1,2,3,5,52,6],[25,23,251,118],[0]),([0,1,2,3,4,5,26,6],[207,58,18,259,208,168,20,73,0,92,151,138,192,150,112,46,130,129,17],[0,2,1,3]),([0,1,10,2,3,4,5,6,36],[58,118,70,138,119,155,25,103],[0]),([0,10,2,3,4,5,6,36],[166,136,70,58,118],[]),([29,1,2,3,4,5,6],[61,101,26,12,78,83,260],[2,0,3,1]),([23,1,10,2,4,5,6],[163,42,103],[]),([1,2,3,4,5,79,6],[101,77,56,261,232],[0]),([1,2,3,4,5,69,6],[136,242,26,118,78,243],[0]),([1,10,2,46,4,5,6],[118,29,102,101,91,3,184],[0]),([0,1,2,3,8,51,6],[41,95,9,23],[2]),([80,0,1,2,3,4,8,6],[19,42,176,67,3,63],[]),([0,2,3,19,14,5,6],[23,95,113,32,17,114,10],[0,1,2,3]),([18,1,2,3,14,5,6],[23,67,79,13,184,62],[0,1]),([0,1,81,4,5,6],[79,125,26,158,262],[0,1]),([0,10,2,4,5,8,6],[58,118,3,42,103],[]),([10,2,3,19,4,5,6],[42,97,3,10,15],[0]),([61,1,2,3,4,5,6],[136,185,50,25,118],[0,1]),([0,10,2,3,5,52,6],[25,58,23,118],[]),([64,0,1,2,3,8,6],[41,3,9,24],[2]),([0,1,2,3,14,8,6],[23,95,187,41,154,12],[1,3,0]),([10,2,3,4,5,6,11],[29,109,227,214,91,126,181,154,10],[0]),([47,1,10,2,4,5,6],[118,3,29,5,101,17],[0])]
def P_247_8_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_247 R_247 slices_247 ps_247 [0,3,5,9,10,11,12,13,15,17,18,19,20,22,23,24,25,26,29,30,31,32,36,39,41,42,44,46,47,50,53,56,58,61,62,63,64,65,67,70,72,73,77,78,79,82,83,84,86,90,91,92,95,97,98,101,102,103,105,109,110,111,112,113,114,115,118,119,120,122,125,126,129,130,136,138,142,148,150,151,152,154,155,156,158,163,165,166,168,175,176,181,183,184,185,187,190,192,198,200,204,207,208,214,219,227,232,234,235,237,240,242,243,251,253,254,255,256,257,258,259,260,261,262]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_247_8_1 : checkNodesBT W_247 G_247 fmask_247 P_247_8_1 autos_247 bk_247_7 8 nd_247_8_1 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_247_8_1 : ∀ ns ∈ nd_247_8_1, Impossible G_247 8 (nodeValsBT W_247 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_247 W_247_ok (buildPoolsSubBT_sound slices_247_ok) autos_247_ok bk_247_7_ok chk_247_8_1
def nodes_247_8 : List NodeSpec := nd_247_8_0 ++ nd_247_8_1
def bk_247_8 : BT (List (List Nat)) := buildBucketsBT W_247 nodes_247_8
set_option maxRecDepth 500000 in
lemma bk_247_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_247 8 xs.toFinset) bk_247_8 := buildBucketsBT_of_mem (forall_append (mem_247_8_0) mem_247_8_1)
def nodes_247_9 : List NodeSpec := [([7,0,1,2,4,5,6],[26,125,12,66,224,63,263],[0,1,2,3]),([0,1,2,3,4,5,8,6],[26,125,12,3,187,188,66,63,73],[0,1,2,3]),([0,1,2,3,4,9,5,6],[3,12,80,0,78,198,264],[0,2,3,1]),([0,1,10,2,3,4,5,6],[101,78,26,10,138,117,214],[2,0,3]),([0,1,2,3,4,5,6,11],[49,10,265,92,267,268,138,150,0,22,266,151,192,73],[0,2,1,3]),([0,1,2,3,9,5,6],[26,67,198,264,3,0,78],[0,2,1,3]),([12,0,1,2,3,5,6],[78,80,10,3,66,248],[0,2,1,3]),([13,0,2,3,4,5,6],[12,80,78,63],[0,1,2,3]),([0,1,2,3,4,14,5,6],[12,80,78,63,10,114],[0,1,2,3]),([15,1,2,3,4,5,6],[78,26,10,126,102,117,269,150],[0,3]),([0,1,2,16,3,4,5,6],[102,138,26,125,150,78,237,270],[0]),([0,1,2,4,9,5,6],[12,78,80,198,0,264],[0,1,2,3]),([0,1,16,3,4,5,6],[78,138,26,125,237,270],[0,1]),([0,2,3,4,14,5,6],[12,80,78,63],[0,1,2,3]),([17,0,1,2,3,5,6],[78,80,74,66,195,271],[0,1,2,3]),([0,1,2,3,14,5,6],[102,10,23,103,114,95,67,78],[0,2,1,3]),([18,1,2,3,4,5,6],[78,125,26,150,216,272],[0,1]),([0,1,2,3,19,4,5,6],[26,95,10,22,273,3,150,92,192,73],[0,2,1,3]),([20,1,2,3,4,5,6],[78,125,26,211,274],[0,1,2,3]),([0,1,2,3,4,5,21,6],[118,78,26,138,50,103,125,140],[0,1]),([1,10,2,3,4,5,6],[3,10,240,214,42,150,122,26],[0,3]),([22,0,1,2,3,4,6],[78,125,26,138,210,275],[0,2,3,1]),([1,2,3,4,5,21,6],[125,12,78,26,50,140,117,138],[2,0,3,1]),([0,1,2,3,4,8,6],[26,63,3,125,187,188],[0,2,1,3]),([23,0,1,2,4,5,6],[12,78,80,254,276],[0,1,2,3]),([0,1,2,3,4,21,6],[101,78,26,50,140],[2,0,3,1]),([0,10,2,3,4,5,6],[101,78,26,117,138,214],[0]),([1,2,3,4,21,6],[42,122,50,140,3],[2,0,3,1]),([24,0,2,3,4,5,6],[101,78,26,117,277],[3,0])]
def P_247_9 : BT (Option BoundPool) := buildPoolsSubBT 9 W_247 R_247 slices_247 ps_247 [0,3,10,12,22,23,26,42,49,50,63,66,67,73,74,78,80,92,95,101,102,103,114,117,118,122,125,126,138,140,150,151,187,188,192,195,198,210,211,214,216,224,237,240,248,254,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_247_9 : checkNodesBT W_247 G_247 fmask_247 P_247_9 autos_247 bk_247_8 9 nodes_247_9 = true := by decide +kernel
def bk_247_9 : BT (List (List Nat)) := buildBucketsBT W_247 nodes_247_9
set_option maxRecDepth 500000 in
lemma bk_247_9_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_247 9 xs.toFinset) bk_247_9 :=
  buildBucketsBT_sound (by decide) gp_247 W_247_ok (buildPoolsSubBT_sound slices_247_ok) autos_247_ok bk_247_8_ok chk_247_9
def nodes_247_10 : List NodeSpec := [([0,1,2,3,4,5,6],[26,80,125,10,92,78],[0,2,1,3])]
def P_247_10 : BT (Option BoundPool) := buildPoolsSubBT 9 W_247 R_247 slices_247 ps_247 [10,26,78,80,92,125]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_247_10 : checkNodesBT W_247 G_247 fmask_247 P_247_10 autos_247 bk_247_9 10 nodes_247_10 = true := by decide +kernel
def bk_247_10 : BT (List (List Nat)) := buildBucketsBT W_247 nodes_247_10
set_option maxRecDepth 500000 in
lemma bk_247_10_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_247 10 xs.toFinset) bk_247_10 :=
  buildBucketsBT_sound (by decide) gp_247 W_247_ok (buildPoolsSubBT_sound slices_247_ok) autos_247_ok bk_247_9_ok chk_247_10
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_247_ok : forestRootCheck R_247 G_247 [(VAR 0,17,16),(VAR 1,18,16),(VAR 2,36,32),(VAR 4,17,1),(VAR 5,33,1),(VAR 6,66,2),(VAR 7,130,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_247_in : bucketContainsBT bk_247_10 R_247 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_247 : Lower R_247 G_247 11 := lower_of_forestBT root_247_ok bk_247_10_ok root_247_in
def G_255 : Nat := 0xfffffffffffffffffffffffeffffffccfffefffefffefffcfefefafaeeee0000
def R_255 : List Nat := varsOf 255
lemma low_255_ok : liftCheck 8 0 R_255 G_255 R_247 G_247 [(VAR 3,72,64)] = true := by decide +kernel
lemma low_255 : Lower R_255 G_255 12 := lift_of low_255_ok low_247
def wit : List PEqualNP.CircuitLowerBounds.Gate := [
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 7]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 4]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 5]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 14]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 7]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 6]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 15]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 17]⟩
]
def wo : Nat := 20
def edgeFn (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
lemma wit_mono : ∀ g ∈ wit, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by intro g hg; simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma edge_eq : ∀ r : Row, edgeFn (evalInput r) = G_255.testBit r.val := by decide +kernel
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput r)) = G_255.testBit r.val := by decide +kernel
end PEqualNP.Outside.L_meta_14312
theorem PEqualNP.Outside.L_meta_14312 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _h1not spec
  exact PEqualNP.Outside.L_meta_14312.replace_of_lower PEqualNP.Outside.L_meta_14312.G_255 (by decide) (by decide) (by decide) 12 PEqualNP.Outside.L_meta_14312.low_255 PEqualNP.Outside.L_meta_14312.wit PEqualNP.Outside.L_meta_14312.wo (by decide) PEqualNP.Outside.L_meta_14312.wit_mono PEqualNP.Outside.L_meta_14312.edgeFn PEqualNP.Outside.L_meta_14312.edge_eq PEqualNP.Outside.L_meta_14312.wit_eval gates o legal spec
