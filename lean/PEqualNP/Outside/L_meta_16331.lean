import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_16331
open PEqualNP.CircuitLowerBounds
abbrev Row := Fin 128
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
lemma bin_lt (d a b : Nat) (ha : a < 2^128) (hb : b < 2^128) : bin d a b < 2^128 := by
  have h1 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x &&& y) < 2^128 := fun x y hx _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left hx
  have h2 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x ||| y) < 2^128 := fun x y hx hy =>
    Nat.or_lt_two_pow hx hy
  have h3 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x ^^^ y) < 2^128 := fun x y hx hy =>
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
lemma swGate_lt (w : List SWire) (hw : ∀ u ∈ w, u.2 < 2^128 ∧ u.2.testBit 0 = false) (g : Gate) :
    (swGate w g).2 < 2^128 ∧ (swGate w g).2.testBit 0 = false := by
  have hz : (0 : Nat) < 2^128 ∧ (0 : Nat).testBit 0 = false := ⟨by decide, by decide⟩
  have hg (i : Nat) : (w.getD i swZero).2 < 2^128 ∧ (w.getD i swZero).2.testBit 0 = false := by
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
    (hw : ∀ u ∈ w, u.2 < 2^128 ∧ u.2.testBit 0 = false) :
    ∀ u ∈ swExec gs w, u.2 < 2^128 ∧ u.2.testBit 0 = false := by
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
lemma normPack_lt (f : Wire) : normPack f < 2^128 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).isLt
lemma testBit_normPack (f : Wire) (r : Nat) :
    (normPack f).testBit r = if h : r < 128 then (f ⟨r, h⟩ != f 0) else false := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).getLsbD r = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : r < 128 <;> simp [h]
lemma normPack_eq_of_obs {a : Nat} (ha : a < 2^128) (h0 : a.testBit 0 = false) :
    normPack (obs a) = a := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 128
  · simp [hr, obs, h0]
  · simp only [hr, dite_false]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma normPack_inv (f : Wire) : normPack (invW f) = normPack f := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_normPack]
  by_cases hr : r < 128
  · simp only [hr, dite_true, invW]
    cases f ⟨r, hr⟩ <;> cases f 0 <;> rfl
  · simp [hr]
lemma normPack_const {f : Wire} (h : Constant f) : normPack f = 0 := by
  obtain ⟨b, rfl⟩ := h
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 128 <;> simp [hr]
lemma normPack_comb2 (op : Bool) (a b : Wire) :
    ∃ d < 4, normPack (comb2 op a b) = bin d (normPack a) (normPack b) := by
  refine ⟨opIdx (if op then !(a 0) else a 0) (if op then !(b 0) else b 0), opIdx_lt _ _, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_bin, testBit_normPack, testBit_normPack]
  by_cases hr : r < 128
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
      exact made_priced w d (false, normPack a) (false, normPack b) hd
        (by simpa [simple, hreps] using avail_normPack ha)
        (by simpa [simple, hreps] using avail_normPack hb)
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
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
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
lemma obs_not_const {T : Nat} (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false) :
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
  ⟨((r.val &&& (127 ^^^ z)) ||| o) % 128, Nat.mod_lt _ (by decide)⟩
def renameW (f : Row → Row) (a : Nat) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).toNat
lemma testBit_renameW (f : Row → Row) (a : Nat) (r : Row) :
    (renameW f a).testBit r.val = a.testBit (f r).val := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).getLsbD r.val = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, r.isLt, dite_true, Option.getD_some]
lemma renameW_lt (f : Row → Row) (a : Nat) : renameW f a < 2^128 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).isLt
lemma obs_renameW (f : Row → Row) (a : Nat) : obs (renameW f a) = restrictW f (obs a) := by
  funext r; exact testBit_renameW f a r
lemma renameW_bin (f : Row → Row) (d a b : Nat) :
    renameW f (bin d a b) = bin d (renameW f a) (renameW f b) := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 128
  · rw [testBit_renameW f _ ⟨r, hr⟩, testBit_bin, testBit_bin, testBit_renameW f _ ⟨r, hr⟩, testBit_renameW f _ ⟨r, hr⟩]
  · have hlt (x : Nat) : (renameW f x).testBit r = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f x) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hlt, testBit_bin, hlt, hlt]
    rcases d with _ | _ | _ | d <;> rfl
lemma renameW_zero (f : Row → Row) : renameW f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · simpa using testBit_renameW f 0 ⟨r, hr⟩
  · rw [Nat.zero_testBit]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f 0) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 128 ≤ r)))
lemma renameW_inj (f : Row → Row) (onto : Function.Surjective f) {a b : Nat}
    (ha : a < 2^128) (hb : b < 2^128) (eq : renameW f a = renameW f b) : a = b := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · obtain ⟨q, hq⟩ := onto ⟨r, hr⟩
    have h := congrArg (fun x => x.testBit q.val) eq
    rw [testBit_renameW, testBit_renameW, hq] at h
    exact h
  · have hge : 128 ≤ r := by omega
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide : 0 < 2) hge)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 0 < 2) hge))]
lemma live_renameW {T k S} (h : Live T k S) (hS : ∀ a ∈ S, a < 2^128) (f : Row → Row)
    (onto : Function.Surjective f) : Live (renameW f T) k (S.image (renameW f)) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hT⟩ := h
    have hTlt : T < 2^128 := hS T (by simp)
    refine ⟨by simp, fun hz => hT (renameW_inj f onto hTlt (by decide) (hz.trans (renameW_zero f).symm))⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := h
    have halt : a < 2^128 := hS a (by simp)
    have hblt : b < 2^128 := hS b (by simp)
    have hUlt : ∀ x ∈ U, x < 2^128 := fun x hx => hS x (by simp [hx])
    have hzlt : bin d a b < 2^128 := bin_lt d a b halt hblt
    have htail_lt : ∀ x ∈ insert (bin d a b) U, x < 2^128 := by
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
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^128) (hGb0 : G.testBit 0 = false)
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
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
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
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000
  | _ => 0
def ALL128 : Nat := 0xffffffffffffffffffffffffffffffff
def swapRow (i j : Nat) (r : Row) : Row :=
  let bi := r.val.testBit i
  let bj := r.val.testBit j
  if bi == bj then r
  else ⟨(r.val ^^^ (1 <<< i) ^^^ (1 <<< j)) % 128, Nat.mod_lt _ (by decide)⟩
def swapWord (i j : Nat) (w : Nat) : Nat :=
  let a := VAR i
  let b := VAR j
  let m10 := a ^^^ (a &&& b)
  let m01 := b ^^^ (a &&& b)
  let msame := ALL128 ^^^ (m10 ||| m01)
  let d := (1 <<< j) - (1 <<< i)
  (w &&& msame) ||| ((w &&& m10) <<< d) ||| ((w &&& m01) >>> d)
def permRow (swaps : List (Nat × Nat)) (r : Row) : Row :=
  swaps.foldl (fun x p => swapRow p.1 p.2 x) r
def permWord (swaps : List (Nat × Nat)) (w : Nat) : Nat :=
  swaps.foldr (fun p x => swapWord p.1 p.2 x) w
lemma swapRow_invol (i j : Nat) (hi : i < 7) (hj : j < 7) (r : Row) :
    swapRow i j (swapRow i j r) = r := by
  revert r
  interval_cases i <;> interval_cases j <;> decide +kernel
lemma swapWord_testBit (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) (hw : w < 2^128) (r : Row) :
    (swapWord i j w).testBit r.val = w.testBit (swapRow i j r).val := by
  have hi : i < 7 := by omega
  have hspec : ∀ r : Row,
      let a := VAR i; let b := VAR j
      let m10 := a ^^^ (a &&& b); let m01 := b ^^^ (a &&& b); let msame := ALL128 ^^^ (m10 ||| m01)
      let d := (1 <<< j) - (1 <<< i)
      (msame.testBit r.val = true → (swapRow i j r).val = r.val ∧ (d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = false) ∧
      (msame.testBit r.val = false →
        (d ≤ r.val ∧ m10.testBit (r.val - d) = true ∧ (swapRow i j r).val = r.val - d ∧ m01.testBit (r.val + d) = false) ∨
        ((d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = true ∧ (swapRow i j r).val = r.val + d)) := by
    revert r; interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have hr := hspec r
  simp only [swapWord, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.add_comm]
  cases hms : (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))).testBit r.val with
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
lemma swapWord_lt (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) : swapWord i j w < 2^128 := by
  have hi : i < 7 := by omega
  have h1 : (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h2 : ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h3 : ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  unfold swapWord
  have e1 : (w &&& (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j))))) < 2^128 :=
    Nat.lt_of_le_of_lt Nat.and_le_right h1
  have e2 : ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i))) < 2^128 := by
    have hle : (w &&& (VAR i ^^^ (VAR i &&& VAR j))) ≤ (VAR i ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR i ^^^ (VAR i &&& VAR j))) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftLeft_eq _ _
      _ ≤ (VAR i ^^^ (VAR i &&& VAR j)) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.mul_le_mul_right _ hle
      _ = ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) := (Nat.shiftLeft_eq _ _).symm
      _ < 2^128 := h2
  have e3 : ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i))) < 2^128 := by
    have hle : (w &&& (VAR j ^^^ (VAR i &&& VAR j))) ≤ (VAR j ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR j ^^^ (VAR i &&& VAR j))) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftRight_eq_div_pow _ _
      _ ≤ (VAR j ^^^ (VAR i &&& VAR j)) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.div_le_div_right hle
      _ = ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) := (Nat.shiftRight_eq_div_pow _ _).symm
      _ < 2^128 := h3
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow e1 e2) e3
lemma swapWord_eq_renameW (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) (hw : w < 2^128) :
    swapWord i j w = renameW (swapRow i j) w := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · rw [swapWord_testBit i j hij hj w hw ⟨r, hr⟩, ← testBit_renameW (swapRow i j) w ⟨r, hr⟩]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (swapWord_lt i j hij hj w) (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
def swapsValid (swaps : List (Nat × Nat)) : Bool :=
  swaps.all fun p => decide (p.1 < p.2) && decide (p.2 < 7)
lemma permWord_eq_renameW (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (w : Nat) (hw : w < 2^128) : permWord swaps w = renameW (permRow swaps) w := by
  induction swaps generalizing w with
  | nil =>
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · exact (testBit_renameW (permRow []) w ⟨r, hr⟩).symm
    · rw [show permWord [] w = w from rfl,
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have ihw := ih hv.2 w hw
    have hlt : permWord ps w < 2^128 := ihw ▸ renameW_lt _ w
    change swapWord p.1 p.2 (permWord ps w) = renameW (permRow (p :: ps)) w
    rw [swapWord_eq_renameW p.1 p.2 hv.1.1 hv.1.2 _ hlt, ihw]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
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
    (hT : T < 2^128) (hfix : permWord swaps T = T)
    (hw : ∀ a ∈ ws, a < 2^128) :
    Impossible T n (ws.map (permWord swaps)).toFinset := by
  intro k hk run
  have hr : ∀ a ∈ (ws.map (permWord swaps)).toFinset, a < 2^128 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    rw [permWord_eq_renameW swaps hv x (hw x hx)]
    exact renameW_lt _ x
  have hvr : swapsValid swaps.reverse = true := by
    simp only [swapsValid, List.all_reverse]; exact hv
  have hinv_row2 : ∀ r : Row, permRow swaps (permRow swaps.reverse r) = r := by
    intro r; simpa using permRow_rev_cancel swaps.reverse hvr r
  have hinv_word : ∀ x : Nat, x < 2^128 → renameW (permRow swaps.reverse) (permWord swaps x) = x := by
    intro x hx
    rw [permWord_eq_renameW swaps hv x hx]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hrr : r < 128
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
  (List.range 7).filterMap fun i => if m.testBit i then some (VAR i) else none
def subcube (z o : Nat) : Nat :=
  (List.range 128).foldr (fun r acc =>
    if (r &&& z == 0) && (r &&& o == o) then acc ||| (1 <<< r) else acc) 0
def fixWord (z o w : Nat) : Nat :=
  (List.range 128).foldr (fun r acc =>
    let fr := ((r &&& (127 ^^^ z)) ||| o) % 128
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
  by_cases hr : r < 128
  · rw [testBit_renameW (fixRow z o) w ⟨r, hr⟩]
    simp [hr, fixRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma subcube_fixRow (z o : Nat) (hz : z < 128) (ho : o < 128) (hzo : (z &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow z o r).val = true := by
  unfold subcube
  rw [testBit_foldr_bits]
  have hmem : (fixRow z o r).val ∈ List.range 128 := List.mem_range.mpr (fixRow z o r).isLt
  simp only [hmem, decide_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have h127 : ((r.val &&& (127 ^^^ z)) ||| o) < 128 := by
    have hr := r.isLt
    have hlt1 : (r.val &&& (127 ^^^ z)) < 128 := Nat.lt_of_le_of_lt Nat.and_le_left hr
    exact Nat.or_lt_two_pow (n := 7) hlt1 ho
  have hval : (fixRow z o r).val = ((r.val &&& (127 ^^^ z)) ||| o) := Nat.mod_eq_of_lt h127
  rw [hval]
  constructor
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit]
    have hzi : (z.testBit i && o.testBit i) = false := by
      have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
    by_cases hi : i < 7
    · have h7 : (127 : Nat).testBit i = true := by interval_cases i <;> decide
      cases hzb : z.testBit i <;> cases hob : o.testBit i <;> simp_all [h7]
    · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
      simp [hzf]
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases o.testBit i <;> simp
def checkEss1 (T : Nat) (roots : List Nat) (a r s : Nat) : Bool :=
  decide (r < 128) && decide (s < 128) && (T.testBit r != T.testBit s) &&
    roots.all fun v => v == a || (v.testBit r == v.testBit s)
lemma checkEss1_sound {T roots a r s} (h : checkEss1 T roots a r s = true) : Essential T roots a := by
  simp only [checkEss1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨⟨r, h.1.1.1⟩, ⟨s, h.1.1.2⟩, h.1.2, fun v hv hne => (h.2 v hv).resolve_left hne⟩
def freeIn (other : List Nat) (w : Nat) : Bool := w == 0 || w == ALL128 || other.contains w
lemma freeIn_sound {other : List Nat} {f : Row → Row} {a : Nat} (ok : freeIn other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)) := by
  rw [← obs_renameW]
  simp only [freeIn, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (h0 | h1) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL128]; have := r.isLt; exact Nat.testBit_two_pow_sub_one 128 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkProper (w : Nat) : Bool := w != 0 && decide (w < 2^128) && !w.testBit 0
lemma checkProper_sound {w : Nat} (h : checkProper w = true) : w ≠ 0 ∧ w < 2^128 ∧ w.testBit 0 = false := by
  simp only [checkProper, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
def checkRoots (rs : List Nat) : Bool := rs.all fun a => decide (a < 2^128) && !a.testBit 0
lemma checkRoots_sound {rs : List Nat} (h : checkRoots rs = true) :
    ∀ a ∈ rs, a < 2^128 ∧ a.testBit 0 = false := by
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
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL128))
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
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL128]; have := r'.isLt; exact Nat.testBit_two_pow_sub_one 128 r'.val |> fun e => by simpa [this] using e⟩
def sliceCheck (z o zDrop : Nat) (raw : List Nat) (T : Nat) (freeRoots : List Nat) (qRoots : List Nat) (qGoal : Nat)
    (qL : Nat) (lEss : List (Nat × Nat × Nat)) (sliceL : Nat) : Bool :=
  let G := fixWord z o T
  decide (z < 128) && decide (o < 128) && ((z &&& o) == 0) &&
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
  base.all fun x => (x.2.1 == projBits pos x.1) && (x.2.2 == projBits neg x.1) && decide (x.1 < 2^128)
lemma base_of {pos neg base} (ok : baseCheck pos neg base = true) :
    ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128 := by
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
def evalInput (r : Row) : Fin 7 → Bool := fun i => r.val.testBit i.val
def packInput (x : Fin 7 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
    16 * (x 4).toNat + 32 * (x 5).toNat + 64 * (x 6).toNat, by
    have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
    have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
    have h6 := Bool.toNat_le (x 6); omega⟩
lemma evalInput_packInput (x : Fin 7 → Bool) : evalInput (packInput x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 b6 : Bool) (j : Fin 7),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat + 64 * b6.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5, b6].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) i
  fin_cases i <;> simpa [evalInput, packInput] using hi
lemma var_testBit (i : Fin 7) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by
  revert i r; decide +kernel
lemma sw_extract_full (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 127 := by
  let seeds : List SWire := (varsOf 127).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^128 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 127).all (fun a => decide (a < 2^128) && !a.testBit 0) = true := by decide +kernel
    have h1 := List.all_eq_true.mp hall v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact h1
  let final := swExec gs seeds
  let out := final.getD o swZero
  have hfinal_lt : out.2 < 2^128 ∧ out.2.testBit 0 = false := by
    simp only [out, List.getD_eq_getElem?_getD]
    cases eq : final[o]? with
    | none => exact ⟨by decide, by decide⟩
    | some a => exact swExec_lt gs seeds hseeds_lt a (List.mem_of_getElem? eq)
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi7 : i < 7 := by simpa using hi2
      have hv : (varsOf 127)[i]? = some (VAR i) := by
        interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput, swRead, Bool.false_bne]
      have hget : (varsOf 127)[i]'(by simpa [seeds] using hi1) = VAR i := by
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
    by_cases hr : r < 128
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
lemma replace_of_lower (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 127) T L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : ∀ g ∈ wit, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (edgeFn : (Fin 7 → Bool) → Bool)
    (hEdgeT : ∀ r : Row, edgeFn (evalInput r) = T.testBit r.val)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput r)) = T.testBit r.val)
    (gates : List Gate) (o : Nat)
    (legal : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (spec : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = edgeFn x) :
    ∃ (gates' : List Gate) (o' : Nat),
      (∀ g ∈ gates', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = edgeFn x := by
  have hwEval : ∀ x : Fin 7 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = edgeFn x := by
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
    have hsup : Supply ((varsOf 127).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 127).map obs)
        (show Reach ((varsOf 127).map obs) 0 ((varsOf 127).map obs) from rfl) hsup
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
  decide (z < 128) && decide (o < 128) && ((z &&& o) == 0) &&
    decide (zDead < 128) && (((z ||| zDead) &&& o) == 0) &&
    checkProper qGoal && checkRoots qRoots &&
    (fixWord (z ||| zDead) o T == qGoal) &&
    raw.all (fun a => freeIn qRoots (fixWord (z ||| zDead) o a))
lemma subcube_fixRow_sup (z o zDead : Nat) (hz : z < 128) (hd : zDead < 128) (ho : o < 128)
    (hzo : ((z ||| zDead) &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow (z ||| zDead) o r).val = true := by
  have hsub := subcube_fixRow (z ||| zDead) o (Nat.or_lt_two_pow (n := 7) hz hd) ho hzo r
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
def evalInput6 (r : Row) : Fin 6 → Bool := fun i => r.val.testBit i.val
def packInput6 (x : Fin 6 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
    16 * (x 4).toNat + 32 * (x 5).toNat, by
    have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
    have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
    omega⟩
lemma evalInput6_packInput6 (x : Fin 6 → Bool) : evalInput6 (packInput6 x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 : Bool) (j : Fin 6),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) i
  fin_cases i <;> simpa [evalInput6, packInput6] using hi
lemma sum_eq_packInput6 (x : Fin 6 → Bool) :
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) = (packInput6 x).val := by
  simp only [Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two, packInput6]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> decide
lemma testBit_rep64 (T6 : Nat) (hT6 : T6 < 2^64) (r : Row) :
    (T6 ||| (T6 <<< 64)).testBit r.val = T6.testBit (r.val % 64) := by
  have hr := r.isLt
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h64 : r.val < 64
  · have hn : ¬(64 ≤ r.val) := by omega
    rw [Nat.mod_eq_of_lt h64]
    simp [hn]
  · have hge : 64 ≤ r.val := by omega
    have hmod : r.val % 64 = r.val - 64 := by omega
    rw [hmod]
    have hhi : T6.testBit r.val = false → (T6.testBit r.val || (decide (64 ≤ r.val) && T6.testBit (r.val - 64))) = T6.testBit (r.val - 64) := by
      intro hf; simp [hf, hge]
    have hf : T6.testBit r.val = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hT6 (Nat.pow_le_pow_right (by decide : 0 < 2) hge))
    exact hhi hf
lemma sw_extract_full_6 (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 63 := by
  let seeds : List SWire := (varsOf 63).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^128 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 63).all (fun a => decide (a < 2^128) && !a.testBit 0) = true := by decide +kernel
    have h1 := List.all_eq_true.mp hall v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact h1
  let final := swExec gs seeds
  let out := final.getD o swZero
  have hfinal_lt : out.2 < 2^128 ∧ out.2.testBit 0 = false := by
    simp only [out, List.getD_eq_getElem?_getD]
    cases eq : final[o]? with
    | none => exact ⟨by decide, by decide⟩
    | some a => exact swExec_lt gs seeds hseeds_lt a (List.mem_of_getElem? eq)
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput6 r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi6 : i < 6 := by simpa using hi2
      have hv : (varsOf 63)[i]? = some (VAR i) := by interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput6, swRead, Bool.false_bne]
      have hget : (varsOf 63)[i]'(by simpa [seeds] using hi1) = VAR i := (List.getElem?_eq_some_iff.mp hv).2
      rw [hget]
      exact var_testBit ⟨i, by omega⟩ r
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
    by_cases hr : r < 128
    · have h := hev ⟨r, hr⟩; simpa [swRead, hout0] using h
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hfinal_lt.1 (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hTlt (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
  have hfound : T ∈ reps final := by
    rw [← hout2]; exact (get_simple final o).resolve_left (hout2.symm ▸ hT0)
  obtain ⟨k, S, hk, hlive, hsub⟩ := extract_live hT0 gs seeds hfound
  refine ⟨k, S, hk, hlive, ?_⟩
  simpa [reps, seeds, List.map_map, Function.comp_def] using hsub
lemma table2_of_lower (T6 : Nat) (hT6lt : T6 < 2^64)
    (hT0 : (T6 ||| (T6 <<< 64)) ≠ 0) (hTlt : (T6 ||| (T6 <<< 64)) < 2^128) (hTb0 : (T6 ||| (T6 <<< 64)).testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 63) (T6 ||| (T6 <<< 64)) L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = (T6 ||| (T6 <<< 64)).testBit r.val)
    (s : ℕ)
    (hcs : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  let T := T6 ||| (T6 <<< 64)
  obtain ⟨C, hfan, hsize, heval⟩ := hcs
  have hlegal : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have ⟨hm, hl⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    exact ⟨hm, hl⟩
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · have hlt : C.gates.countP isBin < C.gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro eq
      obtain ⟨g, hg, hop⟩ := hn
      have bad := List.countP_eq_length.mp eq g hg
      simp [isBin, hop] at bad
    have heR : ∀ r : Row, Circuit.eval ⟨C.gates, C.output⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val := by
      intro r
      have h1 := heval (evalInput6 r)
      have hsum : (∑ i : Fin 6, if evalInput6 r i then 2 ^ (i : ℕ) else 0) = r.val % 64 := by
        rw [sum_eq_packInput6]
        have h : ∀ j : Row, (packInput6 (evalInput6 j)).val = j.val % 64 := by decide +kernel
        exact h r
      dsimp only at h1
      rw [hsum] at h1
      exact h1.trans (testBit_rep64 T6 hT6lt r).symm
    obtain ⟨k, S, hk, hlive, hsub⟩ := sw_extract_full_6 T hT0 hTlt hTb0 C.gates C.output hlegal heR
    have hrun := live_to_run hlive S.toList (Finset.nodup_toList S) (by simp)
    have hsup : Supply ((varsOf 63).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 63).map obs)
        (show Reach ((varsOf 63).map obs) 0 ((varsOf 63).map obs) from rfl) hsup
    have hlo := hLow q next hq hav
    have hwEval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
      intro x
      rw [← evalInput6_packInput6 x, hwEvalR (packInput6 x), testBit_rep64 T6 hT6lt (packInput6 x)]
      rw [evalInput6_packInput6 x, sum_eq_packInput6 x]
      have hlt64 : (packInput6 x).val < 64 := by
        have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
        have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
        simp only [packInput6]; omega
      rw [Nat.mod_eq_of_lt hlt64]
    have hcsz : C.size = C.gates.length := rfl
    refine ⟨⟨wit, wo⟩, hwMono, ?_, hwEval⟩
    change wit.length ≤ s
    omega
  · refine ⟨C, ?_, hsize, heval⟩
    intro g hg
    have ⟨hm, hl⟩ := hlegal g hg
    refine ⟨?_, hl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hm with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g, hg, h⟩).elim
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
inductive btAll {α : Type} (P : α → Prop) : BT α → Prop where
  | empty : btAll P .empty
  | leaf {x : α} : P x → btAll P (.leaf x)
  | node {l r : BT α} : btAll P l → btAll P r → btAll P (.node l r)
lemma btAll_get {α : Type} {P : α → Prop} {d : α} {t : BT α} (ht : btAll P t) (hd : P d) (i : Nat) :
    P (btGet d t i) := by
  induction ht generalizing i with
  | empty => exact hd
  | leaf hx => exact hx
  | node _ _ ihl ihr =>
    unfold btGet
    split
    · exact ihl _
    · exact ihr _
lemma btAll_set {α : Type} {P : α → Prop} {depth : Nat} {t : BT α} {i : Nat} {v : α}
    (ht : btAll P t) (hv : P v) : btAll P (btSet depth t i v) := by
  induction depth generalizing t i with
  | zero => exact .leaf hv
  | succ d ih =>
    cases ht with
    | empty =>
      unfold btSet; split
      · exact .node (ih .empty) .empty
      · exact .node .empty (ih .empty)
    | leaf hx =>
      unfold btSet; split
      · exact .node (ih (.leaf hx)) .empty
      · exact .node .empty (ih (.leaf hx))
    | node hl hr =>
      unfold btSet; split
      · exact .node (ih hl) hr
      · exact .node hl (ih hr)
lemma btAll_update {α : Type} {P : α → Prop} {d0 : α} {depth : Nat} {t : BT α} {i : Nat} {f : α → α}
    (ht : btAll P t) (hd0 : P d0) (hf : ∀ x, P x → P (f x)) : btAll P (btUpdate d0 depth t i f) := by
  induction depth generalizing t i with
  | zero =>
    cases ht with
    | leaf hx => exact .leaf (hf _ hx)
    | empty => exact .leaf (hf d0 hd0)
    | node _ _ => exact .leaf (hf d0 hd0)
  | succ d ih =>
    cases ht with
    | empty =>
      unfold btUpdate; split
      · exact .node (ih .empty) .empty
      · exact .node .empty (ih .empty)
    | leaf hx =>
      unfold btUpdate; split
      · exact .node (ih (.leaf hx)) .empty
      · exact .node .empty (ih (.leaf hx))
    | node hl hr =>
      unfold btUpdate; split
      · exact .node (ih hl) hr
      · exact .node hl (ih hr)
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
  exact hgo l (0, BT.empty) h .empty
def fastBitMask (z o i : Nat) : Nat :=
  if z.testBit i then ALL128 ^^^ VAR i else if o.testBit i then VAR i else ALL128
def subcubeFast (z o : Nat) : Nat :=
  fastBitMask z o 0 &&& fastBitMask z o 1 &&& fastBitMask z o 2 &&&
  fastBitMask z o 3 &&& fastBitMask z o 4 &&& fastBitMask z o 5 &&& fastBitMask z o 6
lemma fastBitMask_testBit (z o i : Nat) (hi : i < 7) (r : Row) :
    (fastBitMask z o i).testBit r.val =
      (if z.testBit i then !(r.val.testBit i) else if o.testBit i then r.val.testBit i else true) := by
  have hall : ALL128.testBit r.val = true := by
    simp only [ALL128]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 128 r.val
  have hvar : (VAR i).testBit r.val = r.val.testBit i := var_testBit ⟨i, hi⟩ r
  unfold fastBitMask
  split
  · simp [Nat.testBit_xor, hall, hvar]
  · split
    · exact hvar
    · exact hall
lemma subcubeFast_eq_subcube (z o : Nat) (hz : z < 128) (ho : o < 128) (hzo : (z &&& o) = 0) :
    subcubeFast z o = subcube z o := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
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
      fastBitMask_testBit z o 6 (by decide) ⟨r, hr⟩]
    have hbit (i : Nat) (hi : i < 7) :
        ((r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i) ↔
          (if z.testBit i then !r.testBit i else if o.testBit i then r.testBit i else true) = true := by
      have hzi : (z.testBit i && o.testBit i) = false := by
        have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
      simp only [Nat.testBit_and]
      cases hz' : z.testBit i <;> cases ho' : o.testBit i <;> cases hr' : r.testBit i <;> simp_all
    have heq_iff : (((r &&& z == 0) && (r &&& o == o)) = true) ↔
        ∀ i < 7, (r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩ i _; rw [h1, h2, Nat.zero_testBit]; exact ⟨rfl, rfl⟩
      · intro h
        constructor
        · apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.zero_testBit]
          by_cases hi : i < 7
          · exact (h i hi).1
          · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
            simp [Nat.testBit_and, hzf]
        · apply Nat.eq_of_testBit_eq; intro i
          by_cases hi : i < 7
          · exact (h i hi).2
          · have hof : o.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
            simp [Nat.testBit_and, hof]
    apply Bool.eq_iff_iff.mpr
    rw [heq_iff]
    simp only [Bool.and_eq_true]
    constructor
    · intro h i hi
      have := hbit i hi
      interval_cases i <;> tauto
    · intro h
      refine ⟨⟨⟨⟨⟨⟨(hbit 0 (by decide)).mp (h 0 (by decide)), (hbit 1 (by decide)).mp (h 1 (by decide))⟩,
        (hbit 2 (by decide)).mp (h 2 (by decide))⟩, (hbit 3 (by decide)).mp (h 3 (by decide))⟩,
        (hbit 4 (by decide)).mp (h 4 (by decide))⟩, (hbit 5 (by decide)).mp (h 5 (by decide))⟩,
        (hbit 6 (by decide)).mp (h 6 (by decide))⟩
  · have hlt_f (i : Nat) : (fastBitMask z o i).testBit r = false := by
      have hle : 128 ≤ r := by omega
      have ha : ALL128 < 2^128 := by decide
      have hv : VAR i < 2^128 := by
        unfold VAR; rcases i with _ | _ | _ | _ | _ | _ | _ | _
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · change (0 : Nat) < 2^128; decide
      have hlt_m : fastBitMask z o i < 2^128 := by
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
    (hT : T < 2^128)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun b => ∀ xs ∈ b, Impossible T k xs.toFinset) prevBks)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^128)
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
    have hinv_w : ∀ x : Nat, x < 2^128 → permWord sw.reverse (permWord sw x) = x := by
      intro x hx
      have h1 := permWord_eq_renameW sw hsv x hx
      have h2 := permWord_eq_renameW sw.reverse hvr (permWord sw x) (h1 ▸ renameW_lt _ x)
      rw [h2, h1]
      apply Nat.eq_of_testBit_eq; intro r
      by_cases hrr : r < 128
      · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
    have hfixr : permWord sw.reverse T = T := by
      have := hinv_w T hT; rwa [hfix] at this
    have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^128 := by
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
    (hT : T < 2^128) (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^128)
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
  have hltc : ∀ x ∈ child, x < 2^128 := by
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
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^128) (out : T ∉ ws.map Prod.fst)
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
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128) :
    btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) (buildWiresBT depth base steps) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  unfold buildWiresBT
  have h0 : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) (btOfList depth base) := btAll_ofList hbase
  have hgo : ∀ (ss : List (Nat × Nat × Nat)) (acc : Nat × BT Decor),
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) acc.2 →
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^128)
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
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (ok : checkNodeBT W T (fullMask pos.length) poolTable autosTable prevBks k ns = true) :
    Impossible T k ((ns.1.map fun idx => (btGet (0, 0, 0) W idx).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (btGet (0, 0, 0) W idx) ∧ (btGet (0, 0, 0) W idx).1 < 2^128 :=
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
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
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
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := .empty
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
  have hinit : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (BT.empty : BT (Option BoundPool)) := .empty
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
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
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
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := .empty
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
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
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
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hP : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) P)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autos)
    (okRoot : forestRootCheck raw T essPairs = true)
    (okForest : checkForestBT W T (fullMask pos.length) P autos tiers raw = true) :
    Lower raw T tiers.length := by
  have hTlt : T < 2^128 := by
    simp only [forestRootCheck, Bool.and_eq_true] at okRoot
    exact (checkProper_sound okRoot.1.1).2.1
  unfold checkForestBT at okForest
  cases hres : checkTiersBT W T (fullMask pos.length) P autos 0 BT.empty tiers with
  | none => simp [hres] at okForest
  | some topBks =>
    simp only [hres] at okForest
    have htop := checkTiersBT_sound hTlt gp hW hP hAutos tiers 0 BT.empty topBks .empty hres
    have hlow := lower_of_forestBT okRoot (by simpa using htop) okForest
    have heq : tiers.length - 1 + 1 = tiers.length := by omega
    rwa [heq] at hlow
def G_0 : Nat := 0xfff0f000fff0f000fff0f000fff0f000
def R_0 : List Nat := varsOf 28
def pos_0 : List Nat := [12,12,20,20,24,24,12,20,24]
def neg_0 : List Nat := [8,4,16,4,16,8,16,8,4]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcf,0x10a),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x173,0xa1),(0xffff0000ffff0000ffff0000ffff0000,0x1bc,0x54)]
def steps_0 : List (Nat × Nat × Nat) := []
def W_0 : BT Decor := buildWiresBT 2 base_0 steps_0
def autosL_0 : List (List (Nat × Nat)) := []
def autos_0 : BT (List (Nat × Nat)) := btOfList 1 autosL_0
def slicesL_0 : List (Option (Nat × Nat)) := []
def slices_0 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_0
def ps_0 : BT (Option PoolSpec) := btOfList 1 []
lemma gp_0 : goodPairs G_0 pos_0 neg_0 := goodPairs_of (by decide +kernel)
lemma base_0_ok : ∀ x ∈ base_0, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_0_ok : btAll (fun x => faithful pos_0 neg_0 x ∧ x.1 < 2^128) W_0 := buildWiresBT_faithful base_0_ok
set_option maxRecDepth 500000 in
lemma autos_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_0 = G_0) autos_0 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_0_ok : btAll (fun o => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) slices_0 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
def bk_0_init : BT (List (List Nat)) := BT.empty
lemma bk_0_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 (0 - 1) xs.toFinset) bk_0_init := btAll.empty
def bk_0_0 : BT (List (List Nat)) := BT.empty
lemma bk_0_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 0 xs.toFinset) bk_0_0 := btAll.empty
def bk_0_1 : BT (List (List Nat)) := BT.empty
lemma bk_0_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 1 xs.toFinset) bk_0_1 := btAll.empty
def bk_0_2 : BT (List (List Nat)) := BT.empty
lemma bk_0_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 2 xs.toFinset) bk_0_2 := btAll.empty
def nodes_0_3 : List NodeSpec := [([0,1,2],[],[])]
def P_0_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_0 R_0 slices_0 ps_0 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_3 : checkNodesBT W_0 G_0 fmask_0 P_0_3 autos_0 bk_0_2 3 nodes_0_3 = true := by decide +kernel
def bk_0_3 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_3
set_option maxRecDepth 500000 in
lemma bk_0_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 3 xs.toFinset) bk_0_3 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok (buildPoolsSubBT_sound slices_0_ok) autos_0_ok bk_0_2_ok chk_0_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 2,12,8),(VAR 3,12,4),(VAR 4,20,4)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT bk_0_3 R_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_0 : Lower R_0 G_0 4 := lower_of_forestBT root_0_ok bk_0_3_ok root_0_in
def G_1 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def R_1 : List Nat := varsOf 7
lemma low_1_ok : carryOK [(0,1),(0,4),(1,3),(0,2)] R_1 G_1 R_0 G_0 = true := by decide +kernel
lemma low_1 : Lower R_1 G_1 4 := carry_of low_1_ok low_0
def G_2 : Nat := 0xee88ee88ee88ee88ee88ee88ee88ee88
def R_2 : List Nat := varsOf 11
lemma low_2_ok : carryOK [(1,4),(1,3),(0,2)] R_2 G_2 R_0 G_0 = true := by decide +kernel
lemma low_2 : Lower R_2 G_2 4 := carry_of low_2_ok low_0
def G_3 : Nat := 0xccc0c000ccc0c000ccc0c000ccc0c000
def R_3 : List Nat := varsOf 30
lemma low_3_ok : liftCheck 0 2 R_3 G_3 R_0 G_0 [(VAR 1,14,12)] = true := by decide +kernel
lemma low_3 : Lower R_3 G_3 5 := lift_of low_3_ok low_0
def G_4 : Nat := 0xee88ee88cc88cc88ee88ee88cc88cc88
def R_4 : List Nat := varsOf 43
lemma low_4_ok : liftCheck 0 32 R_4 G_4 R_2 G_2 [(VAR 5,41,9)] = true := by decide +kernel
lemma low_4 : Lower R_4 G_4 5 := lift_of low_4_ok low_2
def G_5 : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8
def R_5 : List Nat := varsOf 15
lemma low_5_ok : liftCheck 4 0 R_5 G_5 R_2 G_2 [(VAR 2,5,1)] = true := by decide +kernel
lemma low_5 : Lower R_5 G_5 5 := lift_of low_5_ok low_2
def G_6 : Nat := 0xeeeeaaaacccc8888eeeeaaaacccc8888
def R_6 : List Nat := varsOf 51
def pos_6 : List Nat := [3,3,18,18,19,33,33,35,49,49,50,50,3,3,3,18,18,18,33,33,33]
def neg_6 : List Nat := [2,1,16,2,17,32,1,34,48,17,48,34,17,34,48,17,34,48,17,34,48]
def fmask_6 : Nat := fullMask 21
def base_6 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1c73f3,0x49252),(0xcccccccccccccccccccccccccccccccc,0x3fc9f,0x92889),(0xffff0000ffff0000ffff0000ffff0000,0x38f1c,0x16d714),(0xffffffff00000000ffffffff00000000,0x1c0fe0,0x1b6da0)]
def steps_6 : List (Nat × Nat × Nat) := []
def W_6 : BT Decor := buildWiresBT 2 base_6 steps_6
def autosL_6 : List (List (Nat × Nat)) := []
def autos_6 : BT (List (Nat × Nat)) := btOfList 1 autosL_6
def slicesL_6 : List (Option (Nat × Nat)) := []
def slices_6 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_6
def ps_6 : BT (Option PoolSpec) := btOfList 1 []
lemma gp_6 : goodPairs G_6 pos_6 neg_6 := goodPairs_of (by decide +kernel)
lemma base_6_ok : ∀ x ∈ base_6, faithful pos_6 neg_6 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_6_ok : btAll (fun x => faithful pos_6 neg_6 x ∧ x.1 < 2^128) W_6 := buildWiresBT_faithful base_6_ok
set_option maxRecDepth 500000 in
lemma autos_6_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_6 = G_6) autos_6 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_6_ok : btAll (fun o => ∀ p, o = some p → Slice R_6 G_6 p.1 p.2) slices_6 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_6 G_6 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
def bk_6_init : BT (List (List Nat)) := BT.empty
lemma bk_6_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_6 (0 - 1) xs.toFinset) bk_6_init := btAll.empty
def bk_6_0 : BT (List (List Nat)) := BT.empty
lemma bk_6_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_6 0 xs.toFinset) bk_6_0 := btAll.empty
def bk_6_1 : BT (List (List Nat)) := BT.empty
lemma bk_6_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_6 1 xs.toFinset) bk_6_1 := btAll.empty
def bk_6_2 : BT (List (List Nat)) := BT.empty
lemma bk_6_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_6 2 xs.toFinset) bk_6_2 := btAll.empty
def nodes_6_3 : List NodeSpec := [([0,1,2,3],[],[])]
def P_6_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_6 R_6 slices_6 ps_6 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_6_3 : checkNodesBT W_6 G_6 fmask_6 P_6_3 autos_6 bk_6_2 3 nodes_6_3 = true := by decide +kernel
def bk_6_3 : BT (List (List Nat)) := buildBucketsBT W_6 nodes_6_3
set_option maxRecDepth 500000 in
lemma bk_6_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_6 3 xs.toFinset) bk_6_3 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound slices_6_ok) autos_6_ok bk_6_2_ok chk_6_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_6_ok : forestRootCheck R_6 G_6 [(VAR 0,3,2),(VAR 1,3,1),(VAR 4,18,2),(VAR 5,33,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_6_in : bucketContainsBT bk_6_3 R_6 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_6 : Lower R_6 G_6 4 := lower_of_forestBT root_6_ok bk_6_3_ok root_6_in
def G_7 : Nat := 0xfff0f0f0fff0f000fff0f0f0fff0f000
def R_7 : List Nat := varsOf 60
lemma low_7_ok : liftCheck 32 0 R_7 G_7 R_0 G_0 [(VAR 5,36,4)] = true := by decide +kernel
lemma low_7 : Lower R_7 G_7 5 := lift_of low_7_ok low_0
def G_8 : Nat := 0xfffafaaafffafaaafffafaaafffafaaa
def R_8 : List Nat := varsOf 29
lemma low_8_ok : liftCheck 1 0 R_8 G_8 R_0 G_0 [(VAR 0,1,0)] = true := by decide +kernel
lemma low_8 : Lower R_8 G_8 5 := lift_of low_8_ok low_0
def G_9 : Nat := 0xe8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8
def R_9 : List Nat := varsOf 15
lemma low_9_ok : carryOK [(2,4),(2,5),(2,3),(0,1)] R_9 G_9 R_4 G_4 = true := by decide +kernel
lemma low_9 : Lower R_9 G_9 5 := carry_of low_9_ok low_4
def G_10 : Nat := 0xe8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8
def R_10 : List Nat := varsOf 23
lemma low_10_ok : carryOK [(4,5),(2,3),(0,1)] R_10 G_10 R_4 G_4 = true := by decide +kernel
lemma low_10 : Lower R_10 G_10 5 := carry_of low_10_ok low_4
def G_11 : Nat := 0xe8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8
def R_11 : List Nat := varsOf 39
lemma low_11_ok : carryOK [(2,3),(0,1)] R_11 G_11 R_4 G_4 = true := by decide +kernel
lemma low_11 : Lower R_11 G_11 5 := carry_of low_11_ok low_4
def G_12 : Nat := 0xeae8eae8eae8eae8eae8eae8eae8eae8
def R_12 : List Nat := varsOf 15
lemma low_12_ok : carryOK [(1,5),(0,4),(1,3),(0,2)] R_12 G_12 R_7 G_7 = true := by decide +kernel
lemma low_12 : Lower R_12 G_12 5 := carry_of low_12_ok low_7
def G_13 : Nat := 0xeaeaeaeae8e8e8e8eaeaeaeae8e8e8e8
def R_13 : List Nat := varsOf 39
lemma low_13_ok : carryOK [(0,1),(0,4),(1,3),(0,2)] R_13 G_13 R_7 G_7 = true := by decide +kernel
lemma low_13 : Lower R_13 G_13 5 := carry_of low_13_ok low_7
def G_14 : Nat := 0xece8ece8ece8ece8ece8ece8ece8ece8
def R_14 : List Nat := varsOf 15
lemma low_14_ok : carryOK [(0,1),(0,5),(1,4),(1,2),(0,3)] R_14 G_14 R_7 G_7 = true := by decide +kernel
lemma low_14 : Lower R_14 G_14 5 := carry_of low_14_ok low_7
def G_15 : Nat := 0xecece8e8ecece8e8ecece8e8ecece8e8
def R_15 : List Nat := varsOf 23
lemma low_15_ok : carryOK [(1,5),(1,4),(1,2),(0,3)] R_15 G_15 R_7 G_7 = true := by decide +kernel
lemma low_15 : Lower R_15 G_15 5 := carry_of low_15_ok low_7
def G_16 : Nat := 0xee88aa88ee88aa88ee88aa88ee88aa88
def R_16 : List Nat := varsOf 27
lemma low_16_ok : carryOK [(4,5),(0,1)] R_16 G_16 R_4 G_4 = true := by decide +kernel
lemma low_16 : Lower R_16 G_16 5 := carry_of low_16_ok low_4
def G_17 : Nat := 0xccc0c0c0ccc0c000ccc0c0c0ccc0c000
def R_17 : List Nat := varsOf 62
lemma low_17_ok : liftCheck 0 2 R_17 G_17 R_7 G_7 [(VAR 1,14,12)] = true := by decide +kernel
lemma low_17 : Lower R_17 G_17 6 := lift_of low_17_ok low_7
def G_18 : Nat := 0xe8e8e8e8e8e8a8a8e8e8e8e8e8e8a8a8
def R_18 : List Nat := varsOf 55
lemma low_18_ok : liftCheck 16 0 R_18 G_18 R_11 G_11 [(VAR 4,22,6)] = true := by decide +kernel
lemma low_18 : Lower R_18 G_18 6 := lift_of low_18_ok low_11
def G_19 : Nat := 0xeae8eae8e8a8e8a8eae8eae8e8a8e8a8
def R_19 : List Nat := varsOf 47
def pos_19 : List Nat := [3,3,5,5,7,11,11,13,13,14,14,14,35,35,37,37,38,38,38,41,41,41,43,45,46,46,3,3,3,3,3,5,5,5,5,5,14,14,14,14,38,38,38,38,41,41,41]
def neg_19 : List Nat := [2,1,4,1,6,10,9,12,9,12,10,6,34,33,36,33,36,34,6,40,33,9,42,44,44,42,6,9,33,42,44,6,9,33,42,44,9,33,42,44,9,33,42,44,6,42,44]
def fmask_19 : Nat := fullMask 47
def base_19 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x700ffcf8f1ff,0x3331830a14a),(0xcccccccccccccccccccccccccccccccc,0xff07f473e73,0x3444a6461c31),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfff8387cf9c,0x5888c5854a94),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x70f003f80fe0,0x6ddd6be807e0),(0xffffffff00000000ffffffff00000000,0x7f0003fff000,0x6eee73dbf000)]
def steps_19 : List (Nat × Nat × Nat) := [(0,1,2),(2,0,1),(3,0,1),(1,1,2),(1,0,1),(2,1,2),(0,0,1),(3,1,2),(1,10,3),(3,10,0),(1,10,0),(0,0,8),(2,0,5),(1,0,5),(3,0,8),(0,9,2),(3,7,2),(2,6,2),(3,11,2),(2,9,3),(1,11,3),(3,10,3),(1,7,2),(0,11,2),(0,9,3),(1,11,2),(3,9,2),(2,9,2),(0,7,2),(3,11,3),(1,9,2),(2,11,2),(3,6,2),(1,6,2),(1,10,12),(0,1,30),(3,10,4),(1,12,0),(1,6,7),(2,9,4),(0,9,4),(1,12,11),(3,10,9),(1,11,4),(3,11,4),(1,10,4),(3,28,1),(3,39,3),(3,33,8),(1,39,3),(3,12,38),(0,9,30)]
def W_19 : BT Decor := buildWiresBT 6 base_19 steps_19
def autosL_19 : List (List (Nat × Nat)) := [[],[(3,5)],[(1,2)],[(3,5),(1,2)]]
def autos_19 : BT (List (Nat × Nat)) := btOfList 2 autosL_19
def slicesL_19 : List (Option (Nat × Nat)) := [some (subcubeFast 8 0,5),some (subcubeFast 32 8,4),some (subcubeFast 0 8,5),some (subcubeFast 0 32,5),some (subcubeFast 32 0,5),some (subcubeFast 8 32,4)]
def slices_19 : BT (Option (Nat × Nat)) := btOfList 3 slicesL_19
def ps_19 : BT (Option PoolSpec) := btOfList 3 [some (0,[]),some (1,[]),some (2,[]),some (3,[]),some (4,[]),some (5,[])]
lemma gp_19 : goodPairs G_19 pos_19 neg_19 := goodPairs_of (by decide +kernel)
lemma base_19_ok : ∀ x ∈ base_19, faithful pos_19 neg_19 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_19_ok : btAll (fun x => faithful pos_19 neg_19 x ∧ x.1 < 2^128) W_19 := buildWiresBT_faithful base_19_ok
set_option maxRecDepth 500000 in
lemma autos_19_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_19 = G_19) autos_19 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_19_0_ok : sliceDirectCheck 8 0 0 R_19 G_19 R_11 G_11 = true := by decide +kernel
lemma sl_19_0 : Slice R_19 G_19 (subcubeFast 8 0) 5 := slice_fast_direct sl_19_0_ok low_11
lemma sl_19_1_ok : sliceDirectCheck 32 8 0 R_19 G_19 R_1 G_1 = true := by decide +kernel
lemma sl_19_1 : Slice R_19 G_19 (subcubeFast 32 8) 4 := slice_fast_direct sl_19_1_ok low_1
lemma sl_19_2_ok : sliceDirectCheck 0 8 0 R_19 G_19 R_13 G_13 = true := by decide +kernel
lemma sl_19_2 : Slice R_19 G_19 (subcubeFast 0 8) 5 := slice_fast_direct sl_19_2_ok low_13
lemma sl_19_3_ok : sliceDirectCheck 0 32 0 R_19 G_19 R_12 G_12 = true := by decide +kernel
lemma sl_19_3 : Slice R_19 G_19 (subcubeFast 0 32) 5 := slice_fast_direct sl_19_3_ok low_12
lemma sl_19_4_ok : sliceDirectCheck 32 0 0 R_19 G_19 R_9 G_9 = true := by decide +kernel
lemma sl_19_4 : Slice R_19 G_19 (subcubeFast 32 0) 5 := slice_fast_direct sl_19_4_ok low_9
lemma sl_19_5_ok : sliceDirectCheck 8 32 0 R_19 G_19 R_1 G_1 = true := by decide +kernel
lemma sl_19_5 : Slice R_19 G_19 (subcubeFast 8 32) 4 := slice_fast_direct sl_19_5_ok low_1
set_option maxRecDepth 500000 in
lemma slices_19_ok : btAll (fun o => ∀ p, o = some p → Slice R_19 G_19 p.1 p.2) slices_19 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_19 G_19 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_19_0) (forall_cons (fun _ h => by cases h; exact sl_19_1) (forall_cons (fun _ h => by cases h; exact sl_19_2) (forall_cons (fun _ h => by cases h; exact sl_19_3) (forall_cons (fun _ h => by cases h; exact sl_19_4) (forall_cons (fun _ h => by cases h; exact sl_19_5) (fun _ h => (List.not_mem_nil h).elim)))))))
def bk_19_init : BT (List (List Nat)) := BT.empty
lemma bk_19_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 (0 - 1) xs.toFinset) bk_19_init := btAll.empty
def bk_19_0 : BT (List (List Nat)) := BT.empty
lemma bk_19_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 0 xs.toFinset) bk_19_0 := btAll.empty
def bk_19_1 : BT (List (List Nat)) := BT.empty
lemma bk_19_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 1 xs.toFinset) bk_19_1 := btAll.empty
def bk_19_2 : BT (List (List Nat)) := BT.empty
lemma bk_19_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 2 xs.toFinset) bk_19_2 := btAll.empty
def nodes_19_3 : List NodeSpec := [([39,0,26,4],[],[]),([39,0,13,4],[],[]),([39,0,52,4],[],[]),([39,0,3,4],[],[]),([0,53,3,4],[],[]),([39,0,54,4],[],[]),([0,55,3,4],[],[]),([0,56,3,4],[],[])]
def P_19_3 : BT (Option BoundPool) := buildPoolsSubBT 3 W_19 R_19 slices_19 ps_19 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_19_3 : checkNodesBT W_19 G_19 fmask_19 P_19_3 autos_19 bk_19_2 3 nodes_19_3 = true := by decide +kernel
def bk_19_3 : BT (List (List Nat)) := buildBucketsBT W_19 nodes_19_3
set_option maxRecDepth 500000 in
lemma bk_19_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 3 xs.toFinset) bk_19_3 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound slices_19_ok) autos_19_ok bk_19_2_ok chk_19_3
def nodes_19_4 : List NodeSpec := [([10,39,0,3,4],[],[0,1]),([10,12,0,26,4],[],[0]),([10,12,0,13,4],[],[0]),([10,12,0,3,4],[],[0]),([0,5,8,3,4],[],[0]),([0,18,8,3,4],[],[0]),([39,0,3,4],[],[0,1]),([16,0,5,3,4],[],[0]),([0,40,30,3,4],[],[]),([10,0,21,3,4],[],[0]),([33,0,8,3,4],[],[0]),([0,1,2,26,41],[],[]),([32,0,1,3,4],[],[]),([23,34,0,1,4],[],[]),([6,42,2,3,4],[],[]),([6,43,2,3,4],[],[]),([44,24,0,1,2],[],[]),([7,14,2,3,4],[],[]),([0,1,29,45,2],[],[]),([24,32,0,1,4],[],[]),([0,20,8,3,4],[],[]),([24,0,1,20,4],[],[]),([0,46,2,3,4],[],[]),([0,1,20,29,4],[],[]),([22,0,5,3,4],[],[0]),([0,47,2,3,4],[],[]),([0,5,30,3,4],[],[]),([12,0,38,3,4],[],[0]),([43,1,2,3,4],[],[]),([0,1,2,25,48],[],[]),([11,0,20,3,4],[],[0]),([32,0,1,29,4],[],[]),([0,1,30,3,4],[],[]),([34,49,0,1,2],[],[]),([0,40,2,3,4],[],[]),([0,1,2,13,50],[],[]),([51,0,2,3,4],[],[]),([39,0,1,3,4],[],[]),([23,0,1,25,4],[],[]),([39,0,8,3,4],[],[]),([34,0,1,30,4],[],[]),([6,0,20,3,4],[],[]),([0,1,30,25,4],[],[]),([0,9,30,3,4],[],[0]),([43,0,2,3,4],[],[]),([7,0,30,3,4],[],[]),([10,0,20,3,4],[],[]),([12,0,30,3,4],[],[]),([39,0,5,3,4],[],[]),([7,43,2,3,4],[],[]),([6,7,2,3,4],[],[])]
def P_19_4 : BT (Option BoundPool) := buildPoolsSubBT 3 W_19 R_19 slices_19 ps_19 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_19_4 : checkNodesBT W_19 G_19 fmask_19 P_19_4 autos_19 bk_19_3 4 nodes_19_4 = true := by decide +kernel
def bk_19_4 : BT (List (List Nat)) := buildBucketsBT W_19 nodes_19_4
set_option maxRecDepth 500000 in
lemma bk_19_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 4 xs.toFinset) bk_19_4 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound slices_19_ok) autos_19_ok bk_19_3_ok chk_19_4
def nodes_19_5 : List NodeSpec := [([10,12,0,1,3,4],[],[0]),([10,0,1,2,13,4],[0,1],[0]),([10,12,0,3,4],[],[0,2,1,3]),([0,1,2,8,3,4],[],[0]),([0,5,1,2,3,4],[],[0]),([14,0,1,2,3,4],[],[0]),([0,15,1,2,3,4],[],[2,0]),([16,0,1,2,3,4],[2,0,3,4],[2,0]),([0,5,8,3,4],[],[0]),([10,0,1,2,3,4],[2,0,3,4],[0]),([10,0,5,2,3,4],[0],[0]),([10,0,1,8,3,4],[0],[0]),([17,0,1,2,3,4],[],[]),([0,1,18,2,3,4],[0,2,4,3],[0,2]),([19,0,1,2,3,4],[],[]),([0,5,1,8,3,4],[],[0]),([0,1,20,3,4],[],[0,2]),([0,21,1,2,3,4],[2,0,3,4],[0]),([6,7,2,3,4],[],[0]),([22,0,1,2,3,4],[],[0]),([23,11,0,1,3,4],[],[0,1]),([0,1,9,2,3,4],[0,2,4,3],[2,0]),([11,0,1,2,3,4],[2,0,3,4],[0,2]),([24,0,1,9,2,4],[0,1],[0]),([7,0,2,8,3,4],[],[0]),([6,7,0,2,3,4],[],[0]),([0,1,20,2,3,4],[],[2,0]),([7,11,0,2,3,4],[0],[0]),([11,0,1,2,25,4],[0,1],[0]),([0,1,20,9,3,4],[],[0,1]),([23,0,1,3,4],[],[]),([0,9,2,8,3,4],[],[0,2]),([10,7,0,2,3,4],[],[0]),([10,0,1,2,26,4],[2,5],[0]),([7,1,9,2,3,4],[0],[0]),([0,1,2,27,3,4],[],[]),([6,7,1,2,3,4],[],[0]),([28,0,1,2,3,4],[2,0,3,4],[0,2]),([0,1,29,9,2,4],[2,5],[0]),([11,0,9,2,3,4],[],[0]),([12,11,0,2,3,4],[],[0]),([11,0,1,30,3,4],[],[0,2,1]),([10,0,9,2,3,4],[],[0]),([31,0,1,2,3,4],[2,0,3,4],[2]),([32,0,1,2,3,4],[],[]),([11,1,9,2,3,4],[],[0]),([33,0,1,2,3,4],[],[0]),([6,0,5,2,3,4],[],[0]),([34,11,0,1,2,4],[2,5],[0]),([32,0,1,9,3,4],[],[2,0,1]),([6,12,0,2,3,4],[],[2,0]),([23,0,1,2,3,4],[],[]),([0,1,2,35,3,4],[0,2,4,3],[2,0]),([6,0,9,2,3,4],[0],[0]),([36,0,1,2,3,4],[2,0,3,4],[0]),([0,1,30,3,4],[],[0]),([7,0,1,2,3,4],[],[0]),([6,11,1,2,3,4],[0],[0]),([0,1,37,2,3,4],[],[]),([0,1,2,38,3,4],[0,2,4,3],[0,2]),([32,0,1,3,4],[],[]),([6,0,1,2,3,4],[],[0]),([0,1,2,30,3,4],[],[0]),([11,0,5,2,3,4],[],[0])]
def P_19_5 : BT (Option BoundPool) := buildPoolsSubBT 3 W_19 R_19 slices_19 ps_19 [0,1,2,3,4,5]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_19_5 : checkNodesBT W_19 G_19 fmask_19 P_19_5 autos_19 bk_19_4 5 nodes_19_5 = true := by decide +kernel
def bk_19_5 : BT (List (List Nat)) := buildBucketsBT W_19 nodes_19_5
set_option maxRecDepth 500000 in
lemma bk_19_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 5 xs.toFinset) bk_19_5 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound slices_19_ok) autos_19_ok bk_19_4_ok chk_19_5
def nodes_19_6 : List NodeSpec := [([0,5,1,2,3,4],[0,2,4,3],[0,2]),([6,0,1,2,3,4],[0,2,4,3],[0,2]),([7,0,1,2,3,4],[0,2,4,3],[0,2]),([0,1,2,8,3,4],[0,2,4,3],[0,2]),([0,1,9,2,3,4],[0,2,4,3],[0,1]),([10,0,1,2,3,4],[0,2,4,3],[0,2,1]),([11,0,1,2,3,4],[0,2,4,3],[0,1])]
def P_19_6 : BT (Option BoundPool) := buildPoolsSubBT 3 W_19 R_19 slices_19 ps_19 [0,2,3,4]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_19_6 : checkNodesBT W_19 G_19 fmask_19 P_19_6 autos_19 bk_19_5 6 nodes_19_6 = true := by decide +kernel
def bk_19_6 : BT (List (List Nat)) := buildBucketsBT W_19 nodes_19_6
set_option maxRecDepth 500000 in
lemma bk_19_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 6 xs.toFinset) bk_19_6 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound slices_19_ok) autos_19_ok bk_19_5_ok chk_19_6
def nodes_19_7 : List NodeSpec := [([0,1,2,3,4],[0,2,4,3],[0,2])]
def P_19_7 : BT (Option BoundPool) := buildPoolsSubBT 3 W_19 R_19 slices_19 ps_19 [0,2,3,4]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_19_7 : checkNodesBT W_19 G_19 fmask_19 P_19_7 autos_19 bk_19_6 7 nodes_19_7 = true := by decide +kernel
def bk_19_7 : BT (List (List Nat)) := buildBucketsBT W_19 nodes_19_7
set_option maxRecDepth 500000 in
lemma bk_19_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 7 xs.toFinset) bk_19_7 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound slices_19_ok) autos_19_ok bk_19_6_ok chk_19_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_ok : forestRootCheck R_19 G_19 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 3,14,6),(VAR 5,38,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_in : bucketContainsBT bk_19_7 R_19 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_19 : Lower R_19 G_19 8 := lower_of_forestBT root_19_ok bk_19_7_ok root_19_in
def G_20 : Nat := 0xece8e8a8ece8e8a8ece8e8a8ece8e8a8
def R_20 : List Nat := varsOf 31
def pos_20 : List Nat := [3,3,5,5,7,11,11,13,13,14,14,14,19,19,21,21,22,22,22,26,26,26,27,29,29,30,3,3,3,3,3,5,5,5,5,5,14,14,14,22,22,22,26,26,26]
def neg_20 : List Nat := [2,1,4,1,6,10,9,12,9,12,10,6,18,17,20,17,20,18,6,24,18,10,25,28,25,28,6,10,18,25,28,6,10,18,25,28,18,25,28,10,25,28,6,25,28]
def fmask_20 : Nat := fullMask 45
def base_20 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffdc0f1ff,0x9242140a14a),(0xcccccccccccccccccccccccccccccccc,0x1ff07e7f3e73,0x4939c361c31),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3ff8387cf9c,0x1648c6854a94),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1c7003f80fe0,0x1bed6be807e0),(0xffff0000ffff0000ffff0000ffff0000,0x1f8003fff000,0x1b7e73dbf000)]
def steps_20 : List (Nat × Nat × Nat) := [(2,1,2),(0,1,2),(2,1,3),(1,0,3),(0,1,3),(3,0,3),(3,0,2),(1,0,2)]
def W_20 : BT Decor := buildWiresBT 4 base_20 steps_20
def autosL_20 : List (List (Nat × Nat)) := [[],[(3,4)]]
def autos_20 : BT (List (Nat × Nat)) := btOfList 1 autosL_20
def slicesL_20 : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,5),some (subcubeFast 0 2,5),some (subcubeFast 1 0,5),some (subcubeFast 1 2,4),some (subcubeFast 8 0,5),some (subcubeFast 0 8,5),some (subcubeFast 16 0,5),some (subcubeFast 16 8,4),some (subcubeFast 8 16,4)]
def slices_20 : BT (Option (Nat × Nat)) := btOfList 4 slicesL_20
def ps_20 : BT (Option PoolSpec) := btOfList 4 [some (0,[]),some (1,[]),some (2,[]),some (3,[]),some (4,[]),some (5,[]),some (6,[]),some (7,[]),some (8,[])]
lemma gp_20 : goodPairs G_20 pos_20 neg_20 := goodPairs_of (by decide +kernel)
lemma base_20_ok : ∀ x ∈ base_20, faithful pos_20 neg_20 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_20_ok : btAll (fun x => faithful pos_20 neg_20 x ∧ x.1 < 2^128) W_20 := buildWiresBT_faithful base_20_ok
set_option maxRecDepth 500000 in
lemma autos_20_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_20 = G_20) autos_20 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_20_0_ok : sliceDirectCheck 0 16 0 R_20 G_20 R_14 G_14 = true := by decide +kernel
lemma sl_20_0 : Slice R_20 G_20 (subcubeFast 0 16) 5 := slice_fast_direct sl_20_0_ok low_14
lemma sl_20_1_ok : sliceDirectCheck 0 2 0 R_20 G_20 R_8 G_8 = true := by decide +kernel
lemma sl_20_1 : Slice R_20 G_20 (subcubeFast 0 2) 5 := slice_fast_direct sl_20_1_ok low_8
lemma sl_20_2_ok : sliceDirectCheck 1 0 0 R_20 G_20 R_3 G_3 = true := by decide +kernel
lemma sl_20_2 : Slice R_20 G_20 (subcubeFast 1 0) 5 := slice_fast_direct sl_20_2_ok low_3
lemma sl_20_3_ok : sliceDirectCheck 1 2 0 R_20 G_20 R_0 G_0 = true := by decide +kernel
lemma sl_20_3 : Slice R_20 G_20 (subcubeFast 1 2) 4 := slice_fast_direct sl_20_3_ok low_0
lemma sl_20_4_ok : sliceDirectCheck 8 0 0 R_20 G_20 R_10 G_10 = true := by decide +kernel
lemma sl_20_4 : Slice R_20 G_20 (subcubeFast 8 0) 5 := slice_fast_direct sl_20_4_ok low_10
lemma sl_20_5_ok : sliceDirectCheck 0 8 0 R_20 G_20 R_15 G_15 = true := by decide +kernel
lemma sl_20_5 : Slice R_20 G_20 (subcubeFast 0 8) 5 := slice_fast_direct sl_20_5_ok low_15
lemma sl_20_6_ok : sliceDirectCheck 16 0 0 R_20 G_20 R_9 G_9 = true := by decide +kernel
lemma sl_20_6 : Slice R_20 G_20 (subcubeFast 16 0) 5 := slice_fast_direct sl_20_6_ok low_9
lemma sl_20_7_ok : sliceDirectCheck 16 8 0 R_20 G_20 R_1 G_1 = true := by decide +kernel
lemma sl_20_7 : Slice R_20 G_20 (subcubeFast 16 8) 4 := slice_fast_direct sl_20_7_ok low_1
lemma sl_20_8_ok : sliceDirectCheck 8 16 0 R_20 G_20 R_1 G_1 = true := by decide +kernel
lemma sl_20_8 : Slice R_20 G_20 (subcubeFast 8 16) 4 := slice_fast_direct sl_20_8_ok low_1
set_option maxRecDepth 500000 in
lemma slices_20_ok : btAll (fun o => ∀ p, o = some p → Slice R_20 G_20 p.1 p.2) slices_20 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_20 G_20 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_20_0) (forall_cons (fun _ h => by cases h; exact sl_20_1) (forall_cons (fun _ h => by cases h; exact sl_20_2) (forall_cons (fun _ h => by cases h; exact sl_20_3) (forall_cons (fun _ h => by cases h; exact sl_20_4) (forall_cons (fun _ h => by cases h; exact sl_20_5) (forall_cons (fun _ h => by cases h; exact sl_20_6) (forall_cons (fun _ h => by cases h; exact sl_20_7) (forall_cons (fun _ h => by cases h; exact sl_20_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def bk_20_init : BT (List (List Nat)) := BT.empty
lemma bk_20_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 (0 - 1) xs.toFinset) bk_20_init := btAll.empty
def bk_20_0 : BT (List (List Nat)) := BT.empty
lemma bk_20_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 0 xs.toFinset) bk_20_0 := btAll.empty
def bk_20_1 : BT (List (List Nat)) := BT.empty
lemma bk_20_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 1 xs.toFinset) bk_20_1 := btAll.empty
def bk_20_2 : BT (List (List Nat)) := BT.empty
lemma bk_20_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 2 xs.toFinset) bk_20_2 := btAll.empty
def bk_20_3 : BT (List (List Nat)) := BT.empty
lemma bk_20_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 3 xs.toFinset) bk_20_3 := btAll.empty
def bk_20_4 : BT (List (List Nat)) := BT.empty
lemma bk_20_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 4 xs.toFinset) bk_20_4 := btAll.empty
def nodes_20_5 : List NodeSpec := [([5,0,6,2,3,4],[1],[]),([11,1,2,12,3,4],[2],[])]
def P_20_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_20 R_20 slices_20 ps_20 [1,2]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_5 : checkNodesBT W_20 G_20 fmask_20 P_20_5 autos_20 bk_20_4 5 nodes_20_5 = true := by decide +kernel
def bk_20_5 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_5
set_option maxRecDepth 500000 in
lemma bk_20_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 5 xs.toFinset) bk_20_5 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound slices_20_ok) autos_20_ok bk_20_4_ok chk_20_5
def nodes_20_6 : List NodeSpec := [([5,0,1,2,3,4],[3,4,5,6,0],[0]),([0,6,1,2,3,4],[3,4,5,6,0],[0]),([7,0,1,2,4],[3,7],[]),([0,1,2,8,4],[3,7],[]),([0,9,1,2,4],[3,8],[]),([10,0,1,2,4],[3,8],[]),([11,0,1,2,3,4],[3,4,5,6,0],[0]),([0,1,2,12,3,4],[3,4,5,6,0],[0])]
def P_20_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_20 R_20 slices_20 ps_20 [0,3,4,5,6,7,8]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_6 : checkNodesBT W_20 G_20 fmask_20 P_20_6 autos_20 bk_20_5 6 nodes_20_6 = true := by decide +kernel
def bk_20_6 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_6
set_option maxRecDepth 500000 in
lemma bk_20_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 6 xs.toFinset) bk_20_6 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound slices_20_ok) autos_20_ok bk_20_5_ok chk_20_6
def nodes_20_7 : List NodeSpec := [([0,1,2,3,4],[3,5,4,0,6],[0,1])]
def P_20_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_20 R_20 slices_20 ps_20 [0,3,4,5,6]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_7 : checkNodesBT W_20 G_20 fmask_20 P_20_7 autos_20 bk_20_6 7 nodes_20_7 = true := by decide +kernel
def bk_20_7 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_7
set_option maxRecDepth 500000 in
lemma bk_20_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 7 xs.toFinset) bk_20_7 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound slices_20_ok) autos_20_ok bk_20_6_ok chk_20_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_ok : forestRootCheck R_20 G_20 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 3,14,6),(VAR 4,22,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_in : bucketContainsBT bk_20_7 R_20 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_20 : Lower R_20 G_20 8 := lower_of_forestBT root_20_ok bk_20_7_ok root_20_in
def G_21 : Nat := 0xee88aa88cc888888ee88aa88cc888888
def R_21 : List Nat := varsOf 59
lemma low_21_ok : liftCheck 0 16 R_21 G_21 R_4 G_4 [(VAR 4,26,10)] = true := by decide +kernel
lemma low_21 : Lower R_21 G_21 6 := lift_of low_21_ok low_4
def G_22 : Nat := 0xeee8eee8ece8ece8eee8eee8ece8ece8
def R_22 : List Nat := varsOf 47
def pos_22 : List Nat := [3,3,5,5,6,6,10,10,11,13,13,14,35,35,37,37,38,38,41,41,41,42,42,45,46,3,3,3,3,5,5,5,5,6,6,6,6,10,10,10,10,41,41]
def neg_22 : List Nat := [2,1,4,1,4,2,8,2,9,12,9,12,34,33,36,33,36,34,40,33,9,40,34,44,44,9,33,34,44,9,33,34,44,9,33,34,44,9,33,34,44,34,44]
def fmask_22 : Nat := fullMask 43
def base_22 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x601fe9cf70f,0x666618a50a),(0xcccccccccccccccccccccccccccccccc,0x1fe1f6339f3,0x288884210a1),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1fe183ce3c,0x51111814a14),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x7e001fc0fc0,0x53333b40f40),(0xffffffff00000000ffffffff00000000,0x60001fff000,0x7ddddeff000)]
def steps_22 : List (Nat × Nat × Nat) := [(2,0,1),(3,0,1),(1,0,1),(0,0,1),(2,7,2),(2,7,3),(1,8,3),(1,8,2)]
def W_22 : BT Decor := buildWiresBT 4 base_22 steps_22
def autosL_22 : List (List (Nat × Nat)) := [[]]
def autos_22 : BT (List (Nat × Nat)) := btOfList 1 autosL_22
def slicesL_22 : List (Option (Nat × Nat)) := [some (subcubeFast 32 0,5),some (subcubeFast 0 32,5),some (subcubeFast 4 0,5),some (subcubeFast 8 0,4),some (subcubeFast 8 32,4)]
def slices_22 : BT (Option (Nat × Nat)) := btOfList 3 slicesL_22
def ps_22 : BT (Option PoolSpec) := btOfList 3 [some (0,[]),some (1,[]),some (2,[]),some (3,[]),some (4,[])]
lemma gp_22 : goodPairs G_22 pos_22 neg_22 := goodPairs_of (by decide +kernel)
lemma base_22_ok : ∀ x ∈ base_22, faithful pos_22 neg_22 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_22_ok : btAll (fun x => faithful pos_22 neg_22 x ∧ x.1 < 2^128) W_22 := buildWiresBT_faithful base_22_ok
set_option maxRecDepth 500000 in
lemma autos_22_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_22 = G_22) autos_22 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_22_0_ok : sliceDirectCheck 32 0 0 R_22 G_22 R_14 G_14 = true := by decide +kernel
lemma sl_22_0 : Slice R_22 G_22 (subcubeFast 32 0) 5 := slice_fast_direct sl_22_0_ok low_14
lemma sl_22_1_ok : sliceDirectCheck 0 32 0 R_22 G_22 R_5 G_5 = true := by decide +kernel
lemma sl_22_1 : Slice R_22 G_22 (subcubeFast 0 32) 5 := slice_fast_direct sl_22_1_ok low_5
lemma sl_22_2_ok : sliceDirectCheck 4 0 0 R_22 G_22 R_4 G_4 = true := by decide +kernel
lemma sl_22_2 : Slice R_22 G_22 (subcubeFast 4 0) 5 := slice_fast_direct sl_22_2_ok low_4
lemma sl_22_3_ok : sliceDirectCheck 8 0 32 R_22 G_22 R_1 G_1 = true := by decide +kernel
lemma sl_22_3 : Slice R_22 G_22 (subcubeFast 8 0) 4 := slice_fast_direct sl_22_3_ok low_1
lemma sl_22_4_ok : sliceDirectCheck 8 32 0 R_22 G_22 R_1 G_1 = true := by decide +kernel
lemma sl_22_4 : Slice R_22 G_22 (subcubeFast 8 32) 4 := slice_fast_direct sl_22_4_ok low_1
set_option maxRecDepth 500000 in
lemma slices_22_ok : btAll (fun o => ∀ p, o = some p → Slice R_22 G_22 p.1 p.2) slices_22 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_22 G_22 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_22_0) (forall_cons (fun _ h => by cases h; exact sl_22_1) (forall_cons (fun _ h => by cases h; exact sl_22_2) (forall_cons (fun _ h => by cases h; exact sl_22_3) (forall_cons (fun _ h => by cases h; exact sl_22_4) (fun _ h => (List.not_mem_nil h).elim))))))
def bk_22_init : BT (List (List Nat)) := BT.empty
lemma bk_22_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_22 (0 - 1) xs.toFinset) bk_22_init := btAll.empty
def bk_22_0 : BT (List (List Nat)) := BT.empty
lemma bk_22_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_22 0 xs.toFinset) bk_22_0 := btAll.empty
def bk_22_1 : BT (List (List Nat)) := BT.empty
lemma bk_22_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_22 1 xs.toFinset) bk_22_1 := btAll.empty
def bk_22_2 : BT (List (List Nat)) := BT.empty
lemma bk_22_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_22 2 xs.toFinset) bk_22_2 := btAll.empty
def bk_22_3 : BT (List (List Nat)) := BT.empty
lemma bk_22_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_22 3 xs.toFinset) bk_22_3 := btAll.empty
def nodes_22_4 : List NodeSpec := [([5,6,2,3,4],[],[]),([9,0,1,3,4],[],[]),([10,0,1,2,4],[],[]),([0,1,2,11,4],[],[]),([0,1,12,3,4],[],[])]
def P_22_4 : BT (Option BoundPool) := buildPoolsSubBT 3 W_22 R_22 slices_22 ps_22 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_22_4 : checkNodesBT W_22 G_22 fmask_22 P_22_4 autos_22 bk_22_3 4 nodes_22_4 = true := by decide +kernel
def bk_22_4 : BT (List (List Nat)) := buildBucketsBT W_22 nodes_22_4
set_option maxRecDepth 500000 in
lemma bk_22_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_22 4 xs.toFinset) bk_22_4 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound slices_22_ok) autos_22_ok bk_22_3_ok chk_22_4
def nodes_22_5 : List NodeSpec := [([5,0,1,2,3,4],[0,1],[0]),([6,0,1,2,3,4],[1,0],[0]),([0,1,7,2,3,4],[2,3,0,1],[0]),([8,0,1,2,3,4],[2,3,1,0],[0])]
def P_22_5 : BT (Option BoundPool) := buildPoolsSubBT 3 W_22 R_22 slices_22 ps_22 [0,1,2,3]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_22_5 : checkNodesBT W_22 G_22 fmask_22 P_22_5 autos_22 bk_22_4 5 nodes_22_5 = true := by decide +kernel
def bk_22_5 : BT (List (List Nat)) := buildBucketsBT W_22 nodes_22_5
set_option maxRecDepth 500000 in
lemma bk_22_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_22 5 xs.toFinset) bk_22_5 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound slices_22_ok) autos_22_ok bk_22_4_ok chk_22_5
def nodes_22_6 : List NodeSpec := [([0,1,2,3,4],[4,2,0],[0])]
def P_22_6 : BT (Option BoundPool) := buildPoolsSubBT 3 W_22 R_22 slices_22 ps_22 [0,2,4]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_22_6 : checkNodesBT W_22 G_22 fmask_22 P_22_6 autos_22 bk_22_5 6 nodes_22_6 = true := by decide +kernel
def bk_22_6 : BT (List (List Nat)) := buildBucketsBT W_22 nodes_22_6
set_option maxRecDepth 500000 in
lemma bk_22_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_22 6 xs.toFinset) bk_22_6 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound slices_22_ok) autos_22_ok bk_22_5_ok chk_22_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_ok : forestRootCheck R_22 G_22 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 3,10,2),(VAR 5,41,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_in : bucketContainsBT bk_22_6 R_22 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_22 : Lower R_22 G_22 7 := lower_of_forestBT root_22_ok bk_22_6_ok root_22_in
def G_23 : Nat := 0xeeeeeaeaecece8e8eeeeeaeaecece8e8
def R_23 : List Nat := varsOf 55
lemma low_23_ok : liftCheck 16 0 R_23 G_23 R_13 G_13 [(VAR 4,18,2)] = true := by decide +kernel
lemma low_23 : Lower R_23 G_23 6 := lift_of low_23_ok low_13
def G_24 : Nat := 0xfffafafafffafaaafffafafafffafaaa
def R_24 : List Nat := varsOf 61
lemma low_24_ok : liftCheck 1 0 R_24 G_24 R_7 G_7 [(VAR 0,1,0)] = true := by decide +kernel
lemma low_24 : Lower R_24 G_24 6 := lift_of low_24_ok low_7
def G_25 : Nat := 0xeee8eae8eee8eae8eee8eae8eee8eae8
def R_25 : List Nat := varsOf 31
lemma low_25_ok : carryOK [(4,5),(0,1)] R_25 G_25 R_22 G_22 = true := by decide +kernel
lemma low_25 : Lower R_25 G_25 7 := carry_of low_25_ok low_22
def G_26 : Nat := 0xeee8eae8ece8e8a8eee8eae8ece8e8a8
def R_26 : List Nat := varsOf 63
def pos_26 : List Nat := [3,3,5,5,7,11,11,13,13,14,14,14,19,19,21,21,22,22,22,26,26,26,27,29,29,30,35,35,37,37,38,38,38,41,41,41,43,45,46,46,51,51,53,53,54,54,57,57,57,58,58,58,61,62,3,3,3,3,3,3,5,5,5,5,5,5,14,14,14,14,14,22,22,22,22,22,26,26,26,26,26,26,38,38,38,38,38,41,41,41,41,41,41]
def neg_26 : List Nat := [2,1,4,1,6,10,9,12,9,12,10,6,18,17,20,17,20,18,6,24,18,10,25,28,25,28,34,33,36,33,36,34,6,40,33,9,42,44,44,42,50,49,52,49,52,50,56,49,25,56,50,42,60,60,6,25,42,49,50,60,6,25,42,49,50,60,25,42,49,50,60,25,42,49,50,60,6,25,42,49,50,60,25,42,49,50,60,6,25,42,49,50,60]
def fmask_26 : Nat := fullMask 93
def base_26 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1f800003ffd1cf3e3dc0f1ff,0x514a294a2818a0c2940a14a),(0xcccccccccccccccccccccccccccccccc,0x7ffffc0fee33d1ce7f3e73,0xaa95529554c219184361c31),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x7c0ffff0303ce1f387cf9c,0x10c218421870146152854a94),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1f83f07c003fc0fe03f80fe0,0x134e69ce69bb40fa03e807e0),(0xffff0000ffff0000ffff0000ffff0000,0x3ff80003fff0003fff000,0x1d77aef7aeb7ff0003dbf000),(0xffffffff00000000ffffffff00000000,0x1ffc0000003ffffffc000000,0x1e7bcf7bcf3efff6fc000000)]
def steps_26 : List (Nat × Nat × Nat) := [(2,2,3),(1,2,3),(2,1,4),(1,1,3),(2,0,1),(3,1,2),(2,1,3),(0,1,3),(0,0,1),(2,1,2),(1,1,2),(3,2,3),(0,1,2),(1,0,1),(3,0,3),(2,0,3),(3,1,3),(0,0,3),(1,0,2),(1,0,3),(3,0,2),(0,2,3),(1,0,4),(2,0,2),(3,0,1),(0,0,2),(1,17,0),(1,6,0),(0,1,7),(3,0,7),(2,1,27),(1,0,27),(1,8,0),(1,12,2),(1,12,0),(1,0,13),(3,11,3),(3,15,3),(3,14,2),(1,15,3),(0,15,3),(2,15,0),(3,2,9),(1,21,2),(0,1,28),(3,20,1),(3,2,25),(1,0,18),(1,24,3),(0,1,25),(1,20,2),(3,17,1),(3,31,3),(1,23,2),(1,15,0),(2,24,3),(2,19,2),(0,24,3),(2,24,5),(1,15,5),(1,14,2),(0,1,24),(1,14,3),(1,31,3),(1,31,1),(3,14,3),(1,22,2),(3,24,3),(1,11,3),(3,26,1),(3,6,1),(2,19,3),(3,31,1),(0,19,3),(0,19,2),(2,15,3),(1,10,2),(1,13,2),(1,0,57),(3,35,1),(1,36,0),(3,8,7),(2,38,5),(1,0,76),(2,35,4),(1,38,3),(3,13,9),(3,0,83),(2,41,2),(2,38,3),(3,18,16),(0,7,28),(1,50,5),(2,40,2),(2,50,3),(2,50,2),(0,62,3),(1,20,18),(1,51,2),(3,14,7),(1,15,20),(3,15,25),(0,1,37),(1,26,13),(1,13,24),(1,0,34),(3,13,24),(0,1,54),(3,6,19),(0,1,56),(0,30,7),(1,47,5),(3,23,25),(1,50,2),(3,10,7),(3,62,3),(1,55,2),(1,12,24),(2,82,5),(2,62,3),(3,12,24),(2,19,27),(2,38,2),(2,66,3),(0,19,7),(1,6,10),(1,10,27),(0,33,1),(2,30,27),(1,14,27),(2,40,5),(1,38,2),(0,15,25),(3,15,19),(1,55,5),(3,6,30),(0,32,1),(2,34,4),(1,62,3),(0,66,3),(1,6,14),(1,50,3),(3,66,3),(1,66,3),(2,51,2),(1,0,87),(3,38,7),(0,38,7),(1,92,2),(1,46,11),(2,1,97),(3,50,7),(3,96,3),(2,118,2),(3,63,54),(3,46,45),(0,50,7),(1,118,2),(2,92,2),(0,96,3)]
def W_26 : BT Decor := buildWiresBT 8 base_26 steps_26
def autosL_26 : List (List (Nat × Nat)) := [[]]
def autos_26 : BT (List (Nat × Nat)) := btOfList 1 autosL_26
def slicesL_26 : List (Option (Nat × Nat)) := [some (subcubeFast 4 8,4),some (subcubeFast 32 8,5),some (subcubeFast 8 32,4),some (subcubeFast 32 2,5),some (subcubeFast 4 16,5),some (subcubeFast 16 0,8),some (subcubeFast 0 2,6),some (subcubeFast 24 0,5),some (subcubeFast 8 16,4),some (subcubeFast 32 0,8),some (subcubeFast 0 32,7),some (subcubeFast 1 0,6),some (subcubeFast 0 16,7),some (subcubeFast 16 8,5),some (subcubeFast 40 16,4),some (subcubeFast 32 16,5),some (subcubeFast 0 48,5),some (subcubeFast 33 2,4),some (subcubeFast 4 48,4),some (subcubeFast 1 2,5),some (subcubeFast 24 32,4),some (subcubeFast 4 0,6),some (subcubeFast 4 32,5),some (subcubeFast 0 8,6),some (subcubeFast 33 0,5),some (subcubeFast 16 32,5),some (subcubeFast 40 0,5),some (subcubeFast 8 0,6),some (subcubeFast 48 0,5)]
def slices_26 : BT (Option (Nat × Nat)) := btOfList 5 slicesL_26
def ps_26 : BT (Option PoolSpec) := btOfList 6 [some (0,[]),some (1,[]),some (2,[]),some (3,[]),some (4,[]),some (5,[(2,1,2),(3,1,2),(1,15,11)]),some (6,[]),some (5,[(0,1,2),(1,1,2),(3,18,16)]),some (5,[]),some (7,[]),some (8,[]),some (9,[]),some (10,[]),some (11,[]),some (12,[]),some (13,[]),some (14,[]),some (15,[]),some (16,[]),some (17,[]),some (18,[]),some (19,[]),some (20,[]),some (21,[]),some (22,[]),some (23,[]),some (24,[]),some (5,[(2,1,2),(3,1,2)]),some (25,[]),some (26,[]),some (27,[]),some (5,[(2,0,1),(3,0,1)]),some (12,[(2,0,1),(3,0,1)]),some (10,[(2,0,1),(3,0,1)]),some (12,[(1,0,1),(2,19,2)]),some (5,[(1,0,1),(2,19,2)]),some (10,[(1,0,1),(2,19,2)]),some (5,[(0,0,1),(1,14,2)]),some (12,[(0,0,1),(1,14,2)]),some (10,[(0,0,1),(1,14,2)]),some (5,[(1,0,2),(0,1,24),(2,24,5)]),some (5,[(2,1,2)]),some (5,[(1,1,2)]),some (5,[(1,0,2)]),some (5,[(2,0,2)]),some (12,[(2,0,1)]),some (5,[(2,0,1)]),some (10,[(2,0,1)]),some (5,[(1,0,2),(2,24,5)]),some (12,[(0,0,1)]),some (5,[(0,0,1)]),some (10,[(0,0,1)]),some (5,[(2,1,2),(1,15,5)]),some (12,[(1,0,1)]),some (5,[(1,0,1)]),some (10,[(1,0,1)]),some (5,[(1,0,2),(0,1,24)]),some (5,[(3,0,1)]),some (12,[(3,0,1)]),some (10,[(3,0,1)]),some (9,[(2,1,2)]),some (5,[(0,1,2)]),some (9,[(1,0,2)]),some (5,[(3,0,2)])]
lemma gp_26 : goodPairs G_26 pos_26 neg_26 := goodPairs_of (by decide +kernel)
lemma base_26_ok : ∀ x ∈ base_26, faithful pos_26 neg_26 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_26_ok : btAll (fun x => faithful pos_26 neg_26 x ∧ x.1 < 2^128) W_26 := buildWiresBT_faithful base_26_ok
set_option maxRecDepth 500000 in
lemma autos_26_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_26 = G_26) autos_26 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_26_0_ok : sliceDirectCheck 4 8 0 R_26 G_26 R_6 G_6 = true := by decide +kernel
lemma sl_26_0 : Slice R_26 G_26 (subcubeFast 4 8) 4 := slice_fast_direct sl_26_0_ok low_6
lemma sl_26_1_ok : sliceDirectCheck 32 8 0 R_26 G_26 R_15 G_15 = true := by decide +kernel
lemma sl_26_1 : Slice R_26 G_26 (subcubeFast 32 8) 5 := slice_fast_direct sl_26_1_ok low_15
lemma sl_26_2_ok : sliceDirectCheck 8 32 16 R_26 G_26 R_1 G_1 = true := by decide +kernel
lemma sl_26_2 : Slice R_26 G_26 (subcubeFast 8 32) 4 := slice_fast_direct sl_26_2_ok low_1
lemma sl_26_3_ok : sliceDirectCheck 32 2 0 R_26 G_26 R_8 G_8 = true := by decide +kernel
lemma sl_26_3 : Slice R_26 G_26 (subcubeFast 32 2) 5 := slice_fast_direct sl_26_3_ok low_8
lemma sl_26_4_ok : sliceDirectCheck 4 16 0 R_26 G_26 R_4 G_4 = true := by decide +kernel
lemma sl_26_4 : Slice R_26 G_26 (subcubeFast 4 16) 5 := slice_fast_direct sl_26_4_ok low_4
lemma sl_26_5_ok : sliceDirectCheck 16 0 0 R_26 G_26 R_19 G_19 = true := by decide +kernel
lemma sl_26_5 : Slice R_26 G_26 (subcubeFast 16 0) 8 := slice_fast_direct sl_26_5_ok low_19
lemma sl_26_6_ok : sliceDirectCheck 0 2 0 R_26 G_26 R_24 G_24 = true := by decide +kernel
lemma sl_26_6 : Slice R_26 G_26 (subcubeFast 0 2) 6 := slice_fast_direct sl_26_6_ok low_24
lemma sl_26_7_ok : sliceDirectCheck 24 0 0 R_26 G_26 R_11 G_11 = true := by decide +kernel
lemma sl_26_7 : Slice R_26 G_26 (subcubeFast 24 0) 5 := slice_fast_direct sl_26_7_ok low_11
lemma sl_26_8_ok : sliceDirectCheck 8 16 32 R_26 G_26 R_1 G_1 = true := by decide +kernel
lemma sl_26_8 : Slice R_26 G_26 (subcubeFast 8 16) 4 := slice_fast_direct sl_26_8_ok low_1
lemma sl_26_9_ok : sliceDirectCheck 32 0 0 R_26 G_26 R_20 G_20 = true := by decide +kernel
lemma sl_26_9 : Slice R_26 G_26 (subcubeFast 32 0) 8 := slice_fast_direct sl_26_9_ok low_20
lemma sl_26_10_ok : sliceDirectCheck 0 32 0 R_26 G_26 R_25 G_25 = true := by decide +kernel
lemma sl_26_10 : Slice R_26 G_26 (subcubeFast 0 32) 7 := slice_fast_direct sl_26_10_ok low_25
lemma sl_26_11_ok : sliceDirectCheck 1 0 0 R_26 G_26 R_17 G_17 = true := by decide +kernel
lemma sl_26_11 : Slice R_26 G_26 (subcubeFast 1 0) 6 := slice_fast_direct sl_26_11_ok low_17
lemma sl_26_12_ok : sliceDirectCheck 0 16 0 R_26 G_26 R_22 G_22 = true := by decide +kernel
lemma sl_26_12 : Slice R_26 G_26 (subcubeFast 0 16) 7 := slice_fast_direct sl_26_12_ok low_22
lemma sl_26_13_ok : sliceDirectCheck 16 8 0 R_26 G_26 R_13 G_13 = true := by decide +kernel
lemma sl_26_13 : Slice R_26 G_26 (subcubeFast 16 8) 5 := slice_fast_direct sl_26_13_ok low_13
lemma sl_26_14_ok : sliceDirectCheck 40 16 0 R_26 G_26 R_1 G_1 = true := by decide +kernel
lemma sl_26_14 : Slice R_26 G_26 (subcubeFast 40 16) 4 := slice_fast_direct sl_26_14_ok low_1
lemma sl_26_15_ok : sliceDirectCheck 32 16 0 R_26 G_26 R_14 G_14 = true := by decide +kernel
lemma sl_26_15 : Slice R_26 G_26 (subcubeFast 32 16) 5 := slice_fast_direct sl_26_15_ok low_14
lemma sl_26_16_ok : sliceDirectCheck 0 48 0 R_26 G_26 R_5 G_5 = true := by decide +kernel
lemma sl_26_16 : Slice R_26 G_26 (subcubeFast 0 48) 5 := slice_fast_direct sl_26_16_ok low_5
lemma sl_26_17_ok : sliceDirectCheck 33 2 0 R_26 G_26 R_0 G_0 = true := by decide +kernel
lemma sl_26_17 : Slice R_26 G_26 (subcubeFast 33 2) 4 := slice_fast_direct sl_26_17_ok low_0
lemma sl_26_18_ok : sliceDirectCheck 4 48 0 R_26 G_26 R_2 G_2 = true := by decide +kernel
lemma sl_26_18 : Slice R_26 G_26 (subcubeFast 4 48) 4 := slice_fast_direct sl_26_18_ok low_2
lemma sl_26_19_ok : sliceDirectCheck 1 2 0 R_26 G_26 R_7 G_7 = true := by decide +kernel
lemma sl_26_19 : Slice R_26 G_26 (subcubeFast 1 2) 5 := slice_fast_direct sl_26_19_ok low_7
lemma sl_26_20_ok : sliceDirectCheck 24 32 0 R_26 G_26 R_1 G_1 = true := by decide +kernel
lemma sl_26_20 : Slice R_26 G_26 (subcubeFast 24 32) 4 := slice_fast_direct sl_26_20_ok low_1
lemma sl_26_21_ok : sliceDirectCheck 4 0 0 R_26 G_26 R_21 G_21 = true := by decide +kernel
lemma sl_26_21 : Slice R_26 G_26 (subcubeFast 4 0) 6 := slice_fast_direct sl_26_21_ok low_21
lemma sl_26_22_ok : sliceDirectCheck 4 32 0 R_26 G_26 R_16 G_16 = true := by decide +kernel
lemma sl_26_22 : Slice R_26 G_26 (subcubeFast 4 32) 5 := slice_fast_direct sl_26_22_ok low_16
lemma sl_26_23_ok : sliceDirectCheck 0 8 0 R_26 G_26 R_23 G_23 = true := by decide +kernel
lemma sl_26_23 : Slice R_26 G_26 (subcubeFast 0 8) 6 := slice_fast_direct sl_26_23_ok low_23
lemma sl_26_24_ok : sliceDirectCheck 33 0 0 R_26 G_26 R_3 G_3 = true := by decide +kernel
lemma sl_26_24 : Slice R_26 G_26 (subcubeFast 33 0) 5 := slice_fast_direct sl_26_24_ok low_3
lemma sl_26_25_ok : sliceDirectCheck 16 32 0 R_26 G_26 R_12 G_12 = true := by decide +kernel
lemma sl_26_25 : Slice R_26 G_26 (subcubeFast 16 32) 5 := slice_fast_direct sl_26_25_ok low_12
lemma sl_26_26_ok : sliceDirectCheck 40 0 0 R_26 G_26 R_10 G_10 = true := by decide +kernel
lemma sl_26_26 : Slice R_26 G_26 (subcubeFast 40 0) 5 := slice_fast_direct sl_26_26_ok low_10
lemma sl_26_27_ok : sliceDirectCheck 8 0 0 R_26 G_26 R_18 G_18 = true := by decide +kernel
lemma sl_26_27 : Slice R_26 G_26 (subcubeFast 8 0) 6 := slice_fast_direct sl_26_27_ok low_18
lemma sl_26_28_ok : sliceDirectCheck 48 0 0 R_26 G_26 R_9 G_9 = true := by decide +kernel
lemma sl_26_28 : Slice R_26 G_26 (subcubeFast 48 0) 5 := slice_fast_direct sl_26_28_ok low_9
set_option maxRecDepth 500000 in
lemma slices_26_ok : btAll (fun o => ∀ p, o = some p → Slice R_26 G_26 p.1 p.2) slices_26 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_26 G_26 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_26_0) (forall_cons (fun _ h => by cases h; exact sl_26_1) (forall_cons (fun _ h => by cases h; exact sl_26_2) (forall_cons (fun _ h => by cases h; exact sl_26_3) (forall_cons (fun _ h => by cases h; exact sl_26_4) (forall_cons (fun _ h => by cases h; exact sl_26_5) (forall_cons (fun _ h => by cases h; exact sl_26_6) (forall_cons (fun _ h => by cases h; exact sl_26_7) (forall_cons (fun _ h => by cases h; exact sl_26_8) (forall_cons (fun _ h => by cases h; exact sl_26_9) (forall_cons (fun _ h => by cases h; exact sl_26_10) (forall_cons (fun _ h => by cases h; exact sl_26_11) (forall_cons (fun _ h => by cases h; exact sl_26_12) (forall_cons (fun _ h => by cases h; exact sl_26_13) (forall_cons (fun _ h => by cases h; exact sl_26_14) (forall_cons (fun _ h => by cases h; exact sl_26_15) (forall_cons (fun _ h => by cases h; exact sl_26_16) (forall_cons (fun _ h => by cases h; exact sl_26_17) (forall_cons (fun _ h => by cases h; exact sl_26_18) (forall_cons (fun _ h => by cases h; exact sl_26_19) (forall_cons (fun _ h => by cases h; exact sl_26_20) (forall_cons (fun _ h => by cases h; exact sl_26_21) (forall_cons (fun _ h => by cases h; exact sl_26_22) (forall_cons (fun _ h => by cases h; exact sl_26_23) (forall_cons (fun _ h => by cases h; exact sl_26_24) (forall_cons (fun _ h => by cases h; exact sl_26_25) (forall_cons (fun _ h => by cases h; exact sl_26_26) (forall_cons (fun _ h => by cases h; exact sl_26_27) (forall_cons (fun _ h => by cases h; exact sl_26_28) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))
def bk_26_init : BT (List (List Nat)) := BT.empty
lemma bk_26_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_26 (0 - 1) xs.toFinset) bk_26_init := btAll.empty
def bk_26_0 : BT (List (List Nat)) := BT.empty
lemma bk_26_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_26 0 xs.toFinset) bk_26_0 := btAll.empty
def bk_26_1 : BT (List (List Nat)) := BT.empty
lemma bk_26_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_26 1 xs.toFinset) bk_26_1 := btAll.empty
def bk_26_2 : BT (List (List Nat)) := BT.empty
lemma bk_26_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_26 2 xs.toFinset) bk_26_2 := btAll.empty
def bk_26_3 : BT (List (List Nat)) := BT.empty
lemma bk_26_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_26 3 xs.toFinset) bk_26_3 := btAll.empty
def bk_26_4 : BT (List (List Nat)) := BT.empty
lemma bk_26_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_26 4 xs.toFinset) bk_26_4 := btAll.empty
def nodes_26_5 : List NodeSpec := [([0,1,2,3,151,5],[],[]),([152,0,1,2,3,5],[],[]),([153,0,1,2,3,5],[],[]),([92,0,2,154,4,5],[0,1,2],[]),([46,96,0,3,4,5],[3],[]),([96,0,43,3,4,5],[4,5],[]),([15,155,0,3,4,5],[0],[]),([156,0,1,2,3,5],[],[]),([102,0,1,144,4,5],[],[]),([157,0,1,2,3,5],[],[]),([96,0,158,3,4,5],[4,7],[]),([159,118,1,2,4,5],[0],[]),([64,0,113,2,3,4],[],[]),([129,148,0,1,4,5],[],[]),([160,0,1,2,4,5],[],[]),([6,17,10,30,4,5],[],[]),([0,1,2,161,4,5],[],[]),([35,1,66,3,4,5],[],[]),([0,34,50,2,3,5],[],[]),([0,162,1,2,3,5],[8],[]),([0,113,2,63,4,5],[],[]),([17,0,1,114,4,5],[],[]),([0,67,83,3,4,5],[],[]),([118,1,2,163,4,5],[9,10],[]),([164,92,0,2,4,5],[],[]),([165,96,0,3,4,5],[0],[]),([17,146,0,1,4,5],[],[]),([0,34,66,3,4,5],[],[]),([1,111,2,3,28,5],[8],[]),([0,113,66,3,4,5],[],[])]
def P_26_5 : BT (Option BoundPool) := buildPoolsSubBT 6 W_26 R_26 slices_26 ps_26 [0,1,2,3,4,5,7,8,9,10]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_26_5 : checkNodesBT W_26 G_26 fmask_26 P_26_5 autos_26 bk_26_4 5 nodes_26_5 = true := by decide +kernel
def bk_26_5 : BT (List (List Nat)) := buildBucketsBT W_26 nodes_26_5
set_option maxRecDepth 500000 in
lemma bk_26_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_26 5 xs.toFinset) bk_26_5 :=
  buildBucketsBT_sound (by decide) gp_26 W_26_ok (buildPoolsSubBT_sound slices_26_ok) autos_26_ok bk_26_4_ok chk_26_5
def nodes_26_6 : List NodeSpec := [([0,1,84,2,3,4,5],[6,11,12],[]),([85,0,1,2,3,4,5],[13,14,8,12,11],[]),([0,86,1,2,3,4,5],[6,8,14,11,12],[]),([8,35,0,1,2,3,5],[14],[0]),([0,1,2,3,87,5],[15,16],[0]),([0,38,1,2,3,7,5],[17,18],[0]),([88,0,38,1,2,3],[19,20,2],[]),([0,1,89,2,3,4,5],[6],[]),([90,35,0,1,2,3,5],[15],[]),([0,38,1,2,3,91,5],[16,18],[]),([8,0,1,2,39,3,5],[],[]),([92,0,2,4,5],[22,21,0,1],[0]),([93,0,1,2,3,4,5],[8,14],[]),([0,1,41,2,7,4,5],[21,16],[]),([94,0,1,2,3,4,5],[],[]),([17,0,40,1,2,4,5],[21,24],[]),([81,0,1,2,43,4,5],[9],[0]),([15,0,1,39,3,4,5],[25,6],[]),([46,0,1,2,45,4,5],[0],[0]),([15,0,1,83,3,4,5],[6],[]),([95,0,38,1,2,3,5],[16],[]),([47,0,1,2,3,4,65],[26],[]),([0,60,1,2,3,4,65],[19],[]),([96,0,3,4,5],[21,4,24,0],[0]),([0,1,2,3,97,5],[15,16],[0]),([0,34,1,2,3,28,5],[13,14],[0]),([35,0,1,2,3,28,5],[8,14],[]),([15,11,0,43,3,4,5],[4,27],[0]),([0,50,1,2,3,98],[19,20,2],[]),([99,0,1,2,3,4,5],[14,8],[]),([100,0,50,1,2,3,5],[16,18],[]),([101,0,50,1,2,3,5],[20,17],[]),([102,62,0,1,3,4,5],[],[0]),([0,1,103,2,3,4,5],[8,14],[]),([0,1,2,39,3,28,5],[],[]),([51,0,1,2,7,4,5],[21,29],[]),([26,0,1,56,3,4,5],[13],[]),([64,0,1,2,3,54,4],[29,19,28,18],[0]),([0,1,2,104,3,4,5],[],[]),([105,0,1,2,3,4,5],[13,8,14,11,12],[]),([106,0,1,2,3,4,5],[12,11],[]),([15,52,0,1,3,4,5],[25,6],[]),([0,1,2,107,3,4,5],[14,8],[]),([0,108,1,2,3,4,5],[13,23,14,8,12,11],[]),([52,0,1,2,3,28,5],[],[]),([26,0,1,83,3,4,5],[],[]),([0,1,109,2,3,4,5],[8,14],[]),([64,61,0,1,2,3,4],[],[]),([0,1,2,110,3,4,5],[25,6,8,14,11,12],[]),([61,73,0,1,2,4,5],[],[0]),([0,1,111,2,3,4,5],[6,25,8,14,11,12],[0]),([0,1,39,24,3,4,5],[13,25],[]),([15,0,1,56,3,4,5],[6],[]),([112,0,1,2,3,4,5],[11,12],[]),([0,113,2,24,3,4,5],[1],[0]),([1,41,2,24,3,4,5],[30],[]),([0,1,114,2,3,4,5],[6],[0]),([0,115,1,2,3,4,5],[8,14],[]),([15,0,67,2,3,4,5],[21],[]),([47,60,1,2,3,4,5],[21],[]),([60,1,2,24,3,4,5],[21],[]),([0,67,13,2,3,4,5],[25],[0]),([52,0,1,24,3,4,5],[25],[]),([6,17,30,0,1,4,5],[9,4],[0]),([35,1,2,24,3,4,5],[25],[]),([30,0,76,2,3,4,5],[13],[]),([0,1,24,83,3,4,5],[13],[0]),([116,0,1,2,3,4,5],[8,14],[]),([36,30,0,2,3,4,5],[13],[]),([0,18,1,83,3,4,5],[6],[]),([10,30,2,3,7,4,5],[31,32,26,33],[]),([47,0,1,2,3,4,117],[11],[]),([118,1,2,4,5],[21,9,26,0],[0]),([17,0,55,1,2,4,5],[21,24],[]),([47,0,67,2,3,4,5],[21],[]),([0,50,1,2,119,3,5],[20],[]),([8,52,0,1,2,3,5],[],[]),([0,1,120,2,3,4,5],[8,14],[]),([15,0,19,2,3,4,65],[24],[]),([14,0,34,2,3,4,5],[25],[0]),([62,0,1,121,3,4,5],[34,35,36,3],[]),([0,1,2,3,45,4,65],[],[]),([6,17,10,0,1,4,5],[4,9],[0]),([15,0,34,2,3,4,5],[25,6],[]),([0,1,2,122,3,4,5],[0,8,14],[]),([17,0,1,66,3,4,5],[25],[]),([0,1,2,123,3,4,5],[25,11,12],[]),([124,0,1,2,82,3,4],[11],[]),([6,17,0,1,19,4,5],[0,9,4,1,24],[0]),([125,62,0,1,3,4,5],[34,35,36,3],[]),([6,17,14,0,1,4,5],[0,9,4,24,1],[0]),([30,35,1,2,3,4,5],[6],[]),([0,76,19,2,3,4,5],[23,25],[]),([0,1,2,126,3,4,5],[14,8],[]),([127,0,1,2,3,4,5],[6,8,14,11,12],[]),([128,0,38,1,2,3,5],[20],[]),([0,50,1,2,3,7,5],[21,17,18],[0]),([129,0,1,66,3,4,5],[],[0]),([10,1,2,37,3,4,5],[],[]),([0,1,130,2,3,4,5],[6,8,14,11,12],[]),([36,0,19,2,3,4,5],[23,30],[]),([1,19,2,37,3,4,5],[23,30],[]),([62,17,0,1,3,4,5],[25],[]),([131,0,1,2,3,4,5],[11,12],[]),([8,0,34,1,2,3,5],[14,8],[]),([0,1,66,3,7,4,5],[21,26,37,38,39],[0]),([6,62,0,1,3,4,5],[30],[]),([15,96,0,3,4,5],[3,21,4,24,0],[0]),([46,15,11,0,3,4,5],[24,3,0],[0]),([62,0,1,3,7,4,5],[3,35,34,36],[]),([15,30,60,2,3,4,5],[21],[]),([0,1,2,132,3,4,5],[14,8],[]),([64,0,67,1,2,3,4],[26,40],[]),([133,0,1,2,3,4,5],[13],[]),([134,0,1,2,3,4,5],[8,14],[]),([0,1,2,135,3,4,5],[13,14,8,12,11],[]),([136,0,40,1,2,3,4],[1],[]),([6,0,1,66,3,4,5],[30],[]),([0,38,1,2,137,3,5],[20,17],[]),([138,0,1,2,3,4,5],[25,12,11],[]),([15,0,139,2,3,4,5],[6],[]),([0,55,1,2,3,4,140],[1],[]),([0,1,56,24,3,4,5],[11],[]),([35,14,1,2,3,4,5],[25],[0]),([10,0,34,2,3,4,5],[],[]),([29,35,1,2,3,4,5],[13],[]),([17,10,30,2,3,4,5],[],[0]),([81,0,1,2,3,4,65],[18,28,29],[]),([141,0,1,2,3,4,5],[12,11],[]),([142,0,1,2,3,4,5],[13,12,11],[]),([143,0,34,1,2,3,5],[15],[]),([10,30,27,2,3,4,5],[32,31,33,26],[]),([62,0,1,3,144,4,5],[],[0]),([0,1,145,66,3,4,5],[38,37,39,26],[]),([0,1,2,63,54,4,5],[9],[0]),([146,0,1,2,3,4,5],[13],[0]),([0,1,27,66,3,4,5],[38,37,39,26],[]),([64,47,0,1,2,3,4],[3],[]),([15,30,0,2,3,4,65],[19],[]),([0,50,1,2,3,147,5],[16],[]),([6,10,30,2,3,4,5],[],[0]),([148,0,1,66,3,4,5],[],[0]),([0,1,66,3,149,4,5],[21,26,37,38,39],[0]),([0,18,1,56,3,4,5],[],[]),([150,0,1,2,3,4,5],[13,14,8,12,11],[]),([0,34,2,16,3,4,5],[6],[]),([62,0,1,27,3,4,5],[34,35,36,3],[])]
def P_26_6 : BT (Option BoundPool) := buildPoolsSubBT 6 W_26 R_26 slices_26 ps_26 [0,1,2,3,4,6,8,9,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_26_6 : checkNodesBT W_26 G_26 fmask_26 P_26_6 autos_26 bk_26_5 6 nodes_26_6 = true := by decide +kernel
def bk_26_6 : BT (List (List Nat)) := buildBucketsBT W_26 nodes_26_6
set_option maxRecDepth 500000 in
lemma bk_26_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_26 6 xs.toFinset) bk_26_6 :=
  buildBucketsBT_sound (by decide) gp_26 W_26_ok (buildPoolsSubBT_sound slices_26_ok) autos_26_ok bk_26_5_ok chk_26_6
def nodes_26_7 : List NodeSpec := [([0,32,1,2,3,4,5],[0,16,9,6],[0]),([0,33,1,2,3,4,5],[4,1,24,15,6],[0]),([0,34,1,2,3,4,5],[15,6,30,13,11,12,14],[0]),([35,0,1,2,3,4,5],[15,13,30,6,11,12,14],[0]),([36,0,1,2,3,4,5],[4,9,13,11,12],[0]),([0,1,2,37,3,4,5],[4,9,6,11,12],[0]),([0,38,1,2,3,5],[19,16,4],[0]),([12,17,0,1,2,4,5],[16,1,9,21,24],[0]),([12,22,0,2,4,5],[21,1,9],[0]),([0,1,2,39,3,4,5],[0,15,6,30,13,12,11],[0]),([0,40,1,2,3,4,5],[21,1,23,8,14,12],[0]),([0,1,41,2,3,4,5],[16,21,23],[0]),([0,1,42,2,4,5],[9,24,6,4],[]),([15,17,0,1,2,3,4,5],[0,30,24,1],[]),([15,0,13,1,2,3,4,5],[2,1,3,24],[0]),([15,0,1,2,43,3,4,5],[2,29,25,4,41],[0]),([44,0,1,3,4,5],[21,4,26],[]),([15,0,1,2,3,45,4,5],[1,0,30],[0]),([46,15,0,1,2,3,4,5],[0,2,29,24,3],[0]),([8,12,0,1,2,3,5],[16,15,21,4],[0]),([47,15,0,1,2,3,4,5],[19,24],[0]),([0,1,2,16,3,7,4,5],[9,3,4,25,24,42],[0]),([17,0,1,2,16,3,4,5],[0,9,4],[]),([47,0,1,2,24,3,4,5],[19,24],[0]),([0,18,13,1,2,3,4,5],[24,3,25,30],[0]),([48,0,1,2,3,4,5],[21,25,8,14,11,12],[]),([0,1,2,49,3,4,5],[21,25,8,14,11,12],[]),([15,0,1,2,3,4,5],[21,24,3,30,25,8,14],[]),([0,50,1,2,3,5],[19,4,16],[0]),([20,0,1,2,24,3,4,5],[24,2,26,25],[0]),([51,0,1,2,3,4,5],[21,29,23,8,14],[0]),([20,0,18,1,2,3,4,5],[24,30,21,3,25],[0]),([21,20,1,2,4,5],[21,9,26],[0]),([0,13,1,2,7,4,5],[16,25,9,24,21],[0]),([52,0,1,2,3,4,5],[0,15,13,30,6,11,12],[0]),([17,0,1,2,25,4,5],[16,25,9,21,23],[0]),([0,1,53,2,3,4,5],[19,4,0,24,30],[]),([0,1,2,24,3,54,4,5],[1,21,30,43,4,26,24],[0]),([0,55,1,2,3,4,5],[21,1,0,8,14,12],[0]),([15,0,1,2,3,25,4,5],[25,22,21,26,23],[0]),([0,1,2,56,3,4,5],[16,9,13,25,6],[0]),([0,57,1,2,3,4,5],[0,16,9,13],[0]),([8,0,1,2,3,25,5],[16,15,21,4],[0]),([0,13,2,9,4,5],[1,9,21],[0]),([23,1,2,25,4,5],[21,25,9,26],[0]),([58,0,1,2,4,5],[9,26,4],[]),([0,1,2,59,3,4,5],[22,21,26],[]),([15,20,0,1,2,3,4,5],[2,24,21,25,26,3],[0]),([26,20,0,1,2,3,4,5],[24,26,25,30],[0]),([29,0,1,2,3,7,4,5],[9,26,4,25,24,44],[0]),([0,60,1,2,3,4,5],[21,30,25,8,14,11,12],[0]),([10,0,1,27,2,3,4,5],[26,4,9,45,46,47],[0]),([15,0,60,1,2,3,4,5],[19,23],[0]),([29,26,1,3,4,5],[21,4,26],[]),([0,1,2,24,3,4,5],[21,24,26,30,25,8,14],[]),([17,30,0,1,2,3,4,5],[9,0,4],[0]),([61,0,1,2,24,3,4,5],[1,30],[0]),([6,0,1,19,2,3,4,5],[4,1,6,9,24],[0]),([62,0,1,3,4,5],[21,3,35],[0]),([0,1,2,63,24,3,4,5],[29,2,25,4,43],[0]),([64,0,1,2,24,3,4],[20,19,48,2],[0]),([17,0,1,2,24,3,4,5],[0,30,24,1],[]),([14,0,1,27,2,3,4,5],[4,9,26,1,24,49,50,51],[0]),([17,10,0,1,2,3,4,5],[9,0,4],[0]),([15,0,1,2,3,4,65],[20,19,52,2],[0]),([0,1,2,66,3,4,5],[21,26,37,30,25],[0]),([0,1,2,24,3,7,4,5],[1,24,26,30,4,43],[0]),([15,0,1,2,3,7,4,5],[24,1,3,30,4,41],[0]),([62,0,1,2,3,4,5],[21,3,35,30,25],[0]),([0,1,19,27,2,3,4,5],[9,4,6,1,26,24,53,54,55],[0]),([12,0,1,2,3,28,5],[16,15,21,4],[0]),([8,0,1,2,24,3,5],[19,20,9,15],[]),([10,0,1,2,3,7,4,5],[25,6,9,26,4,46,45,47],[0]),([12,0,1,2,24,3,4,5],[1,22,23,21],[0]),([20,0,1,2,7,4,5],[16,25,9,24,21],[0]),([15,0,1,2,24,3,4,5],[21,24,26,3],[0]),([0,13,1,2,24,3,4,5],[2,21,24,1,26],[0]),([0,67,1,2,3,4,5],[21,56,30,25,11,12],[0]),([0,1,2,24,3,25,4,5],[22,25,26,23],[0]),([0,1,2,68,4,5],[21,15,26],[]),([0,1,2,69,4,5],[15,26,4],[]),([6,30,0,1,2,3,4,5],[21,4,9],[0]),([0,70,2,3,4,5],[4,26,6],[]),([0,1,2,3,7,28,5],[16,15,21,18],[0]),([71,0,1,2,4,5],[21,9,26],[]),([30,0,1,2,3,7,4,5],[25,21,9,26,4,57,58,59],[0]),([26,0,13,1,2,3,4,5],[24,30,21,25,26],[0]),([8,0,1,2,3,7,5],[16,15,21,18],[0]),([0,1,2,72,3,4,5],[22,21,29],[]),([6,14,0,1,2,3,4,5],[4,1,9,24,13],[0]),([30,0,1,27,2,3,4,5],[21,9,4,58,57,59,26],[0]),([15,11,0,3,4,5],[21,24,4,0,3],[0]),([15,30,0,2,3,4,5],[19,23],[0]),([0,1,19,2,3,7,4,5],[1,9,4,6,24,54,53,26,55],[0]),([73,0,1,2,24,3,4,5],[0,29,2,24,26],[0]),([12,15,0,1,2,3,4,5],[22,1,6,23],[0]),([6,10,0,1,2,3,4,5],[4,13,9],[0]),([8,15,0,1,2,3,5],[20,21,3,9,15],[]),([0,1,2,74,4,5],[15,24,6,4],[]),([15,0,1,2,3,28,5],[19,20,9,15],[]),([75,0,1,2,3,4,5],[19,24,30,25,8,14],[]),([0,76,1,2,3,4,5],[4,1,24,15,13],[0]),([17,0,1,19,2,3,4,5],[0,9,4,1,24],[0]),([0,18,16,3,4,5],[21,4,24],[0]),([77,0,1,2,4,5],[21,15,1],[]),([0,1,2,3,25,28,5],[16,21,15,4],[0]),([78,0,2,3,4,5],[21,4,26],[]),([0,67,1,2,24,3,4,5],[19,56],[0]),([0,1,79,2,4,5],[21,9,29],[]),([0,1,80,3,4,5],[21,4,24],[]),([17,14,0,1,2,3,4,5],[0,9,4,24,1],[0]),([47,0,1,2,3,4,5],[19,30,25,8,14,12],[0]),([14,0,1,2,3,7,4,5],[1,26,4,9,24,6,50,49,51],[0]),([81,15,0,1,2,3,4,5],[1,0,30,4,41,24,3],[0]),([6,17,0,1,4,5],[9,24,4],[0]),([29,17,0,1,2,3,4,5],[0,9,4],[]),([0,1,2,24,3,28,5],[20,21,26,9,15],[]),([10,30,2,3,4,5],[21,26,31],[0]),([0,1,2,82,3,4,5],[26,6,30,25,8,14,12],[0]),([15,0,19,2,3,4,5],[21,23,3],[0]),([0,1,2,83,3,4,5],[16,9,25,6,13],[0]),([0,1,66,3,4,5],[21,26,37],[0])]
def P_26_7 : BT (Option BoundPool) := buildPoolsSubBT 6 W_26 R_26 slices_26 ps_26 [0,1,2,3,4,6,8,9,11,12,13,14,15,16,18,19,20,21,22,23,24,25,26,29,30,31,35,37,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_26_7 : checkNodesBT W_26 G_26 fmask_26 P_26_7 autos_26 bk_26_6 7 nodes_26_7 = true := by decide +kernel
def bk_26_7 : BT (List (List Nat)) := buildBucketsBT W_26 nodes_26_7
set_option maxRecDepth 500000 in
lemma bk_26_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_26 7 xs.toFinset) bk_26_7 :=
  buildBucketsBT_sound (by decide) gp_26 W_26_ok (buildPoolsSubBT_sound slices_26_ok) autos_26_ok bk_26_6_ok chk_26_7
def nodes_26_8 : List NodeSpec := [([6,0,1,2,3,4,5],[4,15,24,13,6],[0]),([0,1,2,3,7,4,5],[15,1,23,9,8,14,11,12,13,6],[0]),([8,0,1,2,3,5],[16,21,14,4,18,8],[0]),([0,1,2,3,9,4,5],[21,15,1,8,14,11,12,23],[0]),([10,0,1,2,3,4,5],[26,6,46,14,23,25,30],[0]),([11,0,1,2,3,4,5],[21,4,24,14,8,12,11,25,30],[0]),([12,0,1,2,3,4,5],[15,1,21,0,30,23],[0]),([0,13,1,2,3,4,5],[16,21,9,25,12,11,23],[0]),([14,0,1,2,3,4,5],[21,50,26,14,12,11,23,25,30],[0]),([15,0,1,2,3,4,5],[21,41,60,24,30,25,12],[0]),([0,1,2,16,3,4,5],[21,42,3,4,14,30,25],[0]),([17,0,1,2,3,4,5],[16,23,9,25,13,6],[0]),([0,18,1,2,3,4,5],[4,21,24,0,61,25,30],[0]),([0,1,19,2,3,4,5],[21,54,3,14,11,12,23,30,25],[0]),([20,0,1,2,3,4,5],[16,21,9,25,12,11,23],[0]),([21,0,1,2,3,4,5],[21,15,26,14,8,12,11,23],[0]),([22,0,1,2,3,4,5],[21,9,29,14,8,23],[0]),([23,0,1,2,3,4,5],[21,9,26,14,8,23],[0]),([0,1,2,24,3,4,5],[21,43,62,4,30,25,12],[0]),([0,1,2,3,25,4,5],[15,1,21,0,30,23],[0]),([26,0,1,2,3,4,5],[4,21,24,0,63,25,30],[0]),([0,1,27,2,3,4,5],[9,24,4,14,8,12,11,13,6],[0]),([0,1,2,3,28,5],[16,21,14,4,18,8],[0]),([29,0,1,2,3,4,5],[21,44,26,4,14,25,30],[0]),([30,0,1,2,3,4,5],[19,57,14,23,30,25],[0]),([31,0,1,2,3,4,5],[21,4,26,14,8,12,11,25,30],[0])]
def P_26_8 : BT (Option BoundPool) := buildPoolsSubBT 6 W_26 R_26 slices_26 ps_26 [0,1,3,4,6,8,9,11,12,13,14,15,16,18,19,21,23,24,25,26,29,30,41,42,43,44,46,50,54,57,60,61,62,63]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_26_8 : checkNodesBT W_26 G_26 fmask_26 P_26_8 autos_26 bk_26_7 8 nodes_26_8 = true := by decide +kernel
def bk_26_8 : BT (List (List Nat)) := buildBucketsBT W_26 nodes_26_8
set_option maxRecDepth 500000 in
lemma bk_26_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_26 8 xs.toFinset) bk_26_8 :=
  buildBucketsBT_sound (by decide) gp_26 W_26_ok (buildPoolsSubBT_sound slices_26_ok) autos_26_ok bk_26_7_ok chk_26_8
def nodes_26_9 : List NodeSpec := [([0,1,2,3,4,5],[8,11],[0])]
def P_26_9 : BT (Option BoundPool) := buildPoolsSubBT 6 W_26 R_26 slices_26 ps_26 [8,11]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_26_9 : checkNodesBT W_26 G_26 fmask_26 P_26_9 autos_26 bk_26_8 9 nodes_26_9 = true := by decide +kernel
def bk_26_9 : BT (List (List Nat)) := buildBucketsBT W_26 nodes_26_9
set_option maxRecDepth 500000 in
lemma bk_26_9_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_26 9 xs.toFinset) bk_26_9 :=
  buildBucketsBT_sound (by decide) gp_26 W_26_ok (buildPoolsSubBT_sound slices_26_ok) autos_26_ok bk_26_8_ok chk_26_9
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_26_ok : forestRootCheck R_26 G_26 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 3,14,6),(VAR 4,22,6),(VAR 5,38,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_26_in : bucketContainsBT bk_26_9 R_26 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_26 : Lower R_26 G_26 10 := lower_of_forestBT root_26_ok bk_26_9_ok root_26_in
def wit : List PEqualNP.CircuitLowerBounds.Gate := [
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 2]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 8]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 11]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 5]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 9]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 14]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 15]⟩
]
def wo : Nat := 16
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by intro g hg; simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4008241896 * 2 ^ 32 + 3974686888) ||| ((4008241896 * 2 ^ 32 + 3974686888) <<< 64)).testBit r.val := by decide +kernel
lemma root_eq : G_26 = ((4008241896 * 2 ^ 32 + 3974686888) ||| ((4008241896 * 2 ^ 32 + 3974686888) <<< 64)) := by decide
lemma low_root : Lower (varsOf 63) ((4008241896 * 2 ^ 32 + 3974686888) ||| ((4008241896 * 2 ^ 32 + 3974686888) <<< 64)) 10 := root_eq ▸ low_26
end PEqualNP.Outside.L_meta_16331
theorem PEqualNP.Outside.L_meta_16331 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241896 * 2 ^ 32 + 3974686888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241896 * 2 ^ 32 + 3974686888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_16331.table2_of_lower (4008241896 * 2 ^ 32 + 3974686888) (by decide) (by decide) (by decide) (by decide) 10 PEqualNP.Outside.L_meta_16331.low_root PEqualNP.Outside.L_meta_16331.wit PEqualNP.Outside.L_meta_16331.wo (by decide) PEqualNP.Outside.L_meta_16331.wit_mono PEqualNP.Outside.L_meta_16331.wit_eval s hcs
