import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_12280
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
def hashWs (nb : Nat) (ws : List Nat) : Nat :=
  (ws.foldl (fun h w => h + (w % 1000003) * 31) 0) % nb
def bucketContains (buckets : Array (List (List Nat))) (ws : List Nat) : Bool :=
  let s := sortNats ws
  (buckets.getD (hashWs buckets.size s) []).contains s
def closeChild (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun c => scalarPoolCut c k rest op) ||
    autos.any (fun sw => bucketContains prevBuckets (ws.map (permWord sw)))
lemma closeChild_sound {raw T pools autos prevBuckets k rest op}
    (hT : T < 2^128)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T k xs.toFinset)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^128)
    (h : closeChild pools autos prevBuckets k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨c, hc, hcut⟩ | ⟨sw, hsw, hhit⟩
  · exact scalarPoolCut_sound (hPools c hc) nd hcut
  · unfold bucketContains at hhit
    simp only [Array.getD, List.contains_eq_mem, decide_eq_true_eq] at hhit
    split at hhit
    next hlt_b =>
      have himp := hPrev _ hlt_b _ hhit
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
        · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
              Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
      have hfix_r : permWord sw.reverse T = T := by
        conv_lhs => rw [← hfix]
        exact hinv_w T hT
      have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^128 := by
        intro a ha
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        rw [permWord_eq_renameW sw hsv x (hlt x hx)]
        exact renameW_lt _ x
      have hrot := rotate_impossible himp sw.reverse hvr hT hfix_r hmap_lt
      have hback : (((choiceVal op :: rest).map (permWord sw)).map (permWord sw.reverse)) = (choiceVal op :: rest) := by
        rw [List.map_map]
        conv_rhs => rw [← List.map_id (choiceVal op :: rest)]
        exact List.map_congr_left fun x hx => hinv_w x (hlt x hx)
      rwa [hback] at hrot
    next => simp at hhit
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
def evalMove (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild pools autos prevBuckets (cap - 1) rest (d, a.1, b.1)
def testPair (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  let z := dbin d a b
  let go := evalMove cap n fmask ws cov pools autos prevBuckets d a b z
  go false false && go true false && go false true && go true true
def testAll (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPair cap n fmask ws cov pools autos prevBuckets a b)) &&
      testAll cap n fmask ws cov pools autos prevBuckets bs
lemma evalMove_sound {raw T pos neg ws pools autos prevBuckets cap a b d ka kb}
    (hT : T < 2^128)
    (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^128)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (hcap : 0 < cap) (hd : d < 4)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (cap - 1) xs.toFinset)
    (hnz : (dbin d a b).1 ≠ 0) (hfr : (dbin d a b).1 ∉ ws.map Prod.fst)
    (test : evalMove cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets
      d a b (dbin d a b) ka kb = true) :
    Impossible T (cap - 1) ((dbin d a b).1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset := by
  let z := dbin d a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => hfr ((sub.map _).subset hm), nd.sublist (sub.map _)⟩
  have hltc : ∀ x ∈ child, x < 2^128 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
      exact hlt w (sub.subset hw)
  have hfr_b : ws.any (fun v => v.1 == z.1) = false := by
    apply Bool.eq_false_iff.mpr; intro hh
    obtain ⟨x, hx, he⟩ := List.any_eq_true.mp hh
    exact hfr (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have hnz_b : (z.1 == 0) = false := beq_false_of_ne hnz
  have hleq : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = child.length := by
    change _ = (z.1 :: rest.map Prod.fst).length
    rw [List.length_cons, List.length_map, delTwo_len ws a b ka kb ha hb ne, Nat.add_comm 1]
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
  unfold evalMove at test
  dsimp only at test
  have hnotgt : ¬(child.length > cap) := by omega
  dsimp only [z] at hcov_b hnz_b hfr_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at test
  exact closeChild_sound (op := (d, a.1, b.1)) (rest := rest.map Prod.fst) hT hPools hAutos hPrev ndc hltc test k hk h
lemma testAll_pair {cap n fmask ws cov pools autos prevBuckets l}
    (h : testAll cap n fmask ws cov pools autos prevBuckets l = true)
    {a b : Decor} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) :
    (∀ d < 4, testPair cap n fmask ws cov pools autos prevBuckets a b d = true) ∨
    (∀ d < 4, testPair cap n fmask ws cov pools autos prevBuckets b a d = true) := by
  induction l with
  | nil => simp at ha
  | cons w l ih =>
    simp only [testAll, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · have bm := (List.mem_cons.mp hb).resolve_left ne.symm
      exact Or.inl fun d hd => h.1 b bm d (by interval_cases d <;> decide)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr fun d hd => h.1 a ha' d (by interval_cases d <;> decide)
      · exact ih h.2 ha' hb'
lemma node_sound {raw T pos neg ws pools autos prevBuckets cap}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^128) (out : T ∉ ws.map Prod.fst)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (cap - 1) xs.toFinset)
    (checks : cap = 0 ∨ testAll cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  rcases checks with rfl | hcheck
  · intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  by_cases h0 : cap = 0
  · subst h0; intro k hk h
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
      (ht : testPair cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets x y d' = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) x.1 y.1 d' k1 k2).toFinset := by
    rw [← delTwo_map_toFinset nd hx hy nxy d' k1 k2]
    have hem : evalMove cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets d' x y (dbin d' x y) k1 k2 = true := by
      simp only [testPair, Bool.and_eq_true] at ht
      cases k1 <;> cases k2 <;> first | exact ht.1.1.1 | exact ht.1.2 | exact ht.1.1.2 | exact ht.2
    exact evalMove_sound hT gp hf nd hlt hx hy (fun e => nxy (congrArg Prod.fst e)) hcap hd' hPools hAutos hPrev hnz' hfr' hem
  rcases testAll_pair hcheck haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb hnz hfr (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    have hfl := flipOp_lt hd
    exact one b a (flipOp d) hfl hbW haW ne.symm kb ka
      (bin_comm_flip d hd a.1 b.1 ▸ hnz) (bin_comm_flip d hd a.1 b.1 ▸ hfr) (hh _ hfl)
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
lemma lower_of_forest {roots T cap} {topBuckets : Array (List (List Nat))} {essPairs : List (Nat × Nat × Nat)}
    (ok : forestRootCheck roots T essPairs = true)
    (hTop : ∀ i (hi : i < topBuckets.size), ∀ xs ∈ topBuckets[i], Impossible T cap xs.toFinset)
    (hRoot : bucketContains topBuckets roots = true) :
    Lower roots T (cap + 1) := by
  simp only [forestRootCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at ok
  obtain ⟨⟨hT, hR⟩, hess⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hEss' : ∀ a ∈ roots, Essential T roots a := fun a ha => by
    obtain ⟨⟨v, r, s⟩, _, rfl, he⟩ := hess a ha
    exact checkEss1_sound he
  have hImp : Impossible T cap (sortNats roots).toFinset := by
    unfold bucketContains Array.getD at hRoot
    dsimp only at hRoot
    split at hRoot
    next hi => exact hTop _ hi _ (List.contains_iff_mem.mp hRoot)
    next => simp at hRoot
  rw [sortNats_toFinset] at hImp
  exact lower_of_impossible p1 p2 p3 hR' hEss' hImp
def buildWires (base : List Decor) (steps : List (Nat × Nat × Nat)) : Array Decor :=
  steps.foldl (fun arr s =>
    let a := arr.getD s.2.1 (0, 0, 0)
    let b := arr.getD s.2.2 (0, 0, 0)
    arr.push (dbin s.1 a b)) base.toArray
lemma faithful_zero (pos neg : List Nat) : faithful pos neg (0, 0, 0) := by
  constructor
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases pos[i]? <;> simp
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases neg[i]? <;> simp
lemma buildWires_faithful {pos neg base steps}
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128) :
    ∀ x ∈ (buildWires base steps).toList, faithful pos neg x ∧ x.1 < 2^128 := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hstep : ∀ (arr : Array Decor) (s : Nat × Nat × Nat),
      (∀ x ∈ arr.toList, faithful pos neg x ∧ x.1 < 2^128) →
      ∀ x ∈ (arr.push (dbin s.1 (arr.getD s.2.1 (0, 0, 0)) (arr.getD s.2.2 (0, 0, 0)))).toList,
        faithful pos neg x ∧ x.1 < 2^128 := by
    intro arr s harr x hx
    rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact harr x hx
    · have hget (i : Nat) : faithful pos neg (arr.getD i (0, 0, 0)) ∧ (arr.getD i (0, 0, 0)).1 < 2^128 := by
        unfold Array.getD
        split
        next hi => exact harr arr[i] (Array.getElem_mem_toList hi)
        next => exact hdef
      exact ⟨faithful_bin s.1 (hget s.2.1).1 (hget s.2.2).1, bin_lt s.1 _ _ (hget s.2.1).2 (hget s.2.2).2⟩
  unfold buildWires
  have hinit : ∀ x ∈ base.toArray.toList, faithful pos neg x ∧ x.1 < 2^128 := by simpa using hbase
  clear hbase
  generalize base.toArray = acc at hinit ⊢
  induction steps generalizing acc with
  | nil => exact hinit
  | cons s ss ih => exact ih _ (hstep acc s hinit)
lemma forall_cons {α : Type} {P : α → Prop} {a : α} {l : List α} (ha : P a) (hl : ∀ x ∈ l, P x) :
    ∀ x ∈ a :: l, P x := by
  intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exact ha; exact hl x hx
lemma array_forall_of_list {α : Type} {P : α → Prop} {l : List α} (h : ∀ x ∈ l, P x) :
    ∀ i (hi : i < l.toArray.size), P l.toArray[i] :=
  fun i hi => h l.toArray[i] (Array.getElem_mem_toList hi)
abbrev PoolSpec := Nat × List (Nat × Nat × Nat)
abbrev NodeSpec := List Nat × List Nat × List Nat
def buildPools (W : Array Decor) (raw : List Nat) (slices : Array (Nat × Nat))
    (pspecs : List PoolSpec) : Array (Option BoundPool) :=
  (pspecs.map fun (slIdx, chIdxs) =>
    match slices[slIdx]? with
    | none => none
    | some (dom, lb) =>
      let cs := chIdxs.map fun (op, ia, ib) => (op, (W.getD ia (0, 0, 0)).1, (W.getD ib (0, 0, 0)).1)
      materialize raw cs dom lb).toArray
lemma buildPools_sound {W : Array Decor} {raw T} {slices : Array (Nat × Nat)} {pspecs : List PoolSpec}
    (hSlices : ∀ i (hi : i < slices.size), Slice raw T slices[i].1 slices[i].2) :
    ∀ i (hi : i < (buildPools W raw slices pspecs).size),
      ∀ c, (buildPools W raw slices pspecs)[i] = some c → ValidPool raw T c := by
  intro i hi c hc
  unfold buildPools at hi hc
  have hmem : some c ∈ pspecs.map (fun (slIdx, chIdxs) =>
      match slices[slIdx]? with
      | none => none
      | some (dom, lb) =>
        let cs := chIdxs.map fun (op, ia, ib) => (op, (W.getD ia (0, 0, 0)).1, (W.getD ib (0, 0, 0)).1)
        materialize raw cs dom lb) := by
    rw [← hc]
    exact Array.getElem_mem_toList hi
  obtain ⟨⟨slIdx, chIdxs⟩, _, hmat⟩ := List.mem_map.mp hmem
  cases hget_sl : slices[slIdx]? with
  | none => simp [hget_sl] at hmat
  | some sl =>
    simp only [hget_sl] at hmat
    have ⟨hsi, hval⟩ := Array.getElem?_eq_some_iff.mp hget_sl
    exact materialize_sound (hval ▸ hSlices slIdx hsi) hmat
def checkNode (W : Array Decor) (T fmask : Nat)
    (poolTable : Array (Option BoundPool)) (autosTable : Array (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (ns : NodeSpec) : Bool :=
  let ws := ns.1.map fun idx => W.getD idx (0, 0, 0)
  let vals := ws.map Prod.fst
  let pools := ns.2.1.filterMap fun pIdx => poolTable.getD pIdx none
  let nodeAutos := ns.2.2.filterMap fun aIdx => autosTable[aIdx]?
  decide vals.Nodup && !(vals.contains T) &&
    (k == 0 || testAll k ws.length fmask ws (coverage ws) pools nodeAutos prevBuckets ws)
def checkNodes (W : Array Decor) (T fmask : Nat)
    (poolTable : Array (Option BoundPool)) (autosTable : Array (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (nodes : List NodeSpec) : Bool :=
  nodes.all (checkNode W T fmask poolTable autosTable prevBuckets k)
lemma checkNode_sound {W : Array Decor} {raw pos neg T poolTable autosTable prevBuckets k ns}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : ∀ x ∈ W.toList, faithful pos neg x ∧ x.1 < 2^128)
    (hPoolTable : ∀ i (hi : i < poolTable.size), ∀ c, poolTable[i] = some c → ValidPool raw T c)
    (hAutos : ∀ sw ∈ autosTable.toList, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (k - 1) xs.toFinset)
    (ok : checkNode W T (fullMask pos.length) poolTable autosTable prevBuckets k ns = true) :
    Impossible T k ((ns.1.map fun idx => (W.getD idx (0, 0, 0)).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (W.getD idx (0, 0, 0)) ∧ (W.getD idx (0, 0, 0)).1 < 2^128 := by
    unfold Array.getD; split
    next hi => exact hW W[idx] (Array.getElem_mem_toList hi)
    next => exact hdef
  unfold checkNode at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => W.getD idx (0, 0, 0)
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (W.getD idx (0, 0, 0)).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply node_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    ok.1.1
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).2)
    (of_decide_eq_false ok.1.2)
    (fun c hc => by
      obtain ⟨pIdx, _, hmat⟩ := List.mem_filterMap.mp hc
      unfold Array.getD at hmat
      split at hmat
      next hi => exact hPoolTable pIdx hi c hmat
      next => simp at hmat)
    (fun sw hsw => by
      obtain ⟨aIdx, _, ha⟩ := List.mem_filterMap.mp hsw
      have ⟨hi, hval⟩ := Array.getElem?_eq_some_iff.mp ha
      exact hAutos sw (hval ▸ Array.getElem_mem_toList hi))
    hPrev ok.2
def nodeVals (W : Array Decor) (ns : NodeSpec) : List Nat :=
  sortNats (ns.1.map fun idx => (W.getD idx (0, 0, 0)).1)
def insertBucket (buckets : Array (List (List Nat))) (xs : List Nat) : Array (List (List Nat)) :=
  let idx := hashWs buckets.size xs
  if h : idx < buckets.size then
    let b := buckets[idx]
    if b.contains xs then buckets else buckets.set idx (xs :: b) h
  else buckets
def buildBuckets (nb : Nat) (W : Array Decor) (nodes : List NodeSpec) : Array (List (List Nat)) :=
  nodes.foldl (fun acc ns => insertBucket acc (nodeVals W ns)) (Array.replicate nb [])
lemma insertBucket_mem {bks : Array (List (List Nat))} {P : List Nat → Prop} {xs : List Nat}
    (hb : ∀ i (hi : i < bks.size), ∀ ys ∈ bks[i], P ys) (hxs : P xs) :
    ∀ i (hi : i < (insertBucket bks xs).size), ∀ ys ∈ (insertBucket bks xs)[i], P ys := by
  unfold insertBucket
  dsimp only
  split
  next hidx =>
    split
    · exact hb
    · intro i hi ys hys
      rw [Array.size_set] at hi
      rw [Array.getElem_set] at hys
      split at hys
      next =>
        rcases List.mem_cons.mp hys with rfl | hys'
        · exact hxs
        · exact hb _ hidx ys hys'
      next => exact hb i hi ys hys
  next => exact hb
lemma buildBuckets_sound {W : Array Decor} {raw pos neg T poolTable autosTable prevBuckets k nb}
    {nodes : List NodeSpec}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : ∀ x ∈ W.toList, faithful pos neg x ∧ x.1 < 2^128)
    (hPoolTable : ∀ i (hi : i < poolTable.size), ∀ c, poolTable[i] = some c → ValidPool raw T c)
    (hAutos : ∀ sw ∈ autosTable.toList, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (k - 1) xs.toFinset)
    (hNodes : checkNodes W T (fullMask pos.length) poolTable autosTable prevBuckets k nodes = true) :
    ∀ i (hi : i < (buildBuckets nb W nodes).size), ∀ xs ∈ (buildBuckets nb W nodes)[i], Impossible T k xs.toFinset := by
  have hmem : ∀ ns ∈ nodes, Impossible T k (nodeVals W ns).toFinset := fun ns hns => by
    unfold nodeVals
    rw [sortNats_toFinset]
    exact checkNode_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
  clear hNodes
  unfold buildBuckets
  have hinit : ∀ i (hi : i < (Array.replicate nb ([] : List (List Nat))).size),
      ∀ xs ∈ (Array.replicate nb ([] : List (List Nat)))[i], Impossible T k xs.toFinset := by
    intro i hi xs hxs; simp at hxs
  generalize Array.replicate nb ([] : List (List Nat)) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    exact ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
      (insertBucket acc (nodeVals W ns)) (insertBucket_mem hinit (hmem ns (List.mem_cons_self ..)))
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
def G_0 : Nat := 0xffffff00ff000000ffffff00ff000000
def R_0 : List Nat := varsOf 56
def pos_0 : List Nat := [24,24,40,40,48,48,24,40,48]
def neg_0 : List Nat := [16,8,32,8,32,16,32,16,8]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xff00ff00ff00ff00ff00ff00ff00ff00,0xcf,0x10a),(0xffff0000ffff0000ffff0000ffff0000,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def steps_0 : List (Nat × Nat × Nat) := []
def W_0 : Array Decor := buildWires base_0 steps_0
def autos_0 : Array (List (Nat × Nat)) := #[]
def slicesL_0 : List (Nat × Nat) := []
def slices_0 : Array (Nat × Nat) := slicesL_0.toArray
def ps_0 : List PoolSpec := []
def P_0 : Array (Option BoundPool) := buildPools W_0 R_0 slices_0 ps_0
lemma gp_0 : goodPairs G_0 pos_0 neg_0 := goodPairs_of (by decide +kernel)
lemma base_0_ok : ∀ x ∈ base_0, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_0_ok : ∀ x ∈ W_0.toList, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := buildWires_faithful base_0_ok
lemma autos_0_ok : ∀ sw ∈ autos_0.toList, swapsValid sw = true ∧ permWord sw G_0 = G_0 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma slices_0_ok : ∀ i (hi : i < slices_0.size), Slice R_0 G_0 slices_0[i].1 slices_0[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_0 G_0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma P_0_ok : ∀ i (hi : i < P_0.size), ∀ c, P_0[i] = some c → ValidPool R_0 G_0 c := buildPools_sound slices_0_ok
def bk_0_init : Array (List (List Nat)) := #[]
lemma bk_0_init_ok : ∀ i (hi : i < bk_0_init.size), ∀ xs ∈ bk_0_init[i], Impossible G_0 (0 - 1) xs.toFinset := by intro i hi; simp [bk_0_init] at hi
def nodes_0_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_0 : checkNodes W_0 G_0 fmask_0 P_0 autos_0 bk_0_init 0 nodes_0_0 = true := by decide +kernel
def bk_0_0 : Array (List (List Nat)) := buildBuckets 1 W_0 nodes_0_0
lemma bk_0_0_ok : ∀ i (hi : i < bk_0_0.size), ∀ xs ∈ bk_0_0[i], Impossible G_0 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_init_ok chk_0_0
def nodes_0_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_1 : checkNodes W_0 G_0 fmask_0 P_0 autos_0 bk_0_0 1 nodes_0_1 = true := by decide +kernel
def bk_0_1 : Array (List (List Nat)) := buildBuckets 1 W_0 nodes_0_1
lemma bk_0_1_ok : ∀ i (hi : i < bk_0_1.size), ∀ xs ∈ bk_0_1[i], Impossible G_0 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_0_ok chk_0_1
def nodes_0_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_2 : checkNodes W_0 G_0 fmask_0 P_0 autos_0 bk_0_1 2 nodes_0_2 = true := by decide +kernel
def bk_0_2 : Array (List (List Nat)) := buildBuckets 1 W_0 nodes_0_2
lemma bk_0_2_ok : ∀ i (hi : i < bk_0_2.size), ∀ xs ∈ bk_0_2[i], Impossible G_0 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_1_ok chk_0_2
def nodes_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_3 : checkNodes W_0 G_0 fmask_0 P_0 autos_0 bk_0_2 3 nodes_0_3 = true := by decide +kernel
def bk_0_3 : Array (List (List Nat)) := buildBuckets 1 W_0 nodes_0_3
lemma bk_0_3_ok : ∀ i (hi : i < bk_0_3.size), ∀ xs ∈ bk_0_3[i], Impossible G_0 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_2_ok chk_0_3
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 3,24,16),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContains bk_0_3 R_0 = true := by decide +kernel
lemma low_0 : Lower R_0 G_0 4 := lower_of_forest root_0_ok bk_0_3_ok root_0_in
def G_1 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def R_1 : List Nat := varsOf 7
lemma low_1_ok : carryOK [(2,5),(1,4),(0,3)] R_1 G_1 R_0 G_0 = true := by decide +kernel
lemma low_1 : Lower R_1 G_1 4 := carry_of low_1_ok low_0
def G_2 : Nat := 0xee88ee88ee88ee88ee88ee88ee88ee88
def R_2 : List Nat := varsOf 11
lemma low_2_ok : carryOK [(2,5),(0,2),(1,4),(0,3)] R_2 G_2 R_0 G_0 = true := by decide +kernel
lemma low_2 : Lower R_2 G_2 4 := carry_of low_2_ok low_0
def G_3 : Nat := 0xeeeeeeee88888888eeeeeeee88888888
def R_3 : List Nat := varsOf 35
lemma low_3_ok : carryOK [(1,2),(0,2),(1,4),(0,3)] R_3 G_3 R_0 G_0 = true := by decide +kernel
lemma low_3 : Lower R_3 G_3 4 := carry_of low_3_ok low_0
def G_4 : Nat := 0xfaa0faa0faa0faa0faa0faa0faa0faa0
def R_4 : List Nat := varsOf 13
lemma low_4_ok : carryOK [(1,2),(1,5),(2,4),(0,1),(0,3)] R_4 G_4 R_0 G_0 = true := by decide +kernel
lemma low_4 : Lower R_4 G_4 4 := carry_of low_4_ok low_0
def G_5 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
def R_5 : List Nat := varsOf 21
lemma low_5_ok : carryOK [(2,5),(2,4),(0,1),(0,3)] R_5 G_5 R_0 G_0 = true := by decide +kernel
lemma low_5 : Lower R_5 G_5 4 := carry_of low_5_ok low_0
def G_6 : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
def R_6 : List Nat := varsOf 37
lemma low_6_ok : carryOK [(2,4),(0,1),(0,3)] R_6 G_6 R_0 G_0 = true := by decide +kernel
lemma low_6 : Lower R_6 G_6 4 := carry_of low_6_ok low_0
def G_7 : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def R_7 : List Nat := varsOf 14
lemma low_7_ok : carryOK [(1,2),(1,5),(2,4),(1,3)] R_7 G_7 R_0 G_0 = true := by decide +kernel
lemma low_7 : Lower R_7 G_7 4 := carry_of low_7_ok low_0
def G_8 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def R_8 : List Nat := varsOf 22
lemma low_8_ok : carryOK [(2,5),(2,4),(1,3)] R_8 G_8 R_0 G_0 = true := by decide +kernel
lemma low_8 : Lower R_8 G_8 4 := carry_of low_8_ok low_0
def G_9 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def R_9 : List Nat := varsOf 38
lemma low_9_ok : carryOK [(2,4),(1,3)] R_9 G_9 R_0 G_0 = true := by decide +kernel
lemma low_9 : Lower R_9 G_9 4 := carry_of low_9_ok low_0
def G_10 : Nat := 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00
def R_10 : List Nat := varsOf 25
lemma low_10_ok : carryOK [(2,5),(2,4),(1,2),(0,1),(0,3)] R_10 G_10 R_0 G_0 = true := by decide +kernel
lemma low_10 : Lower R_10 G_10 4 := carry_of low_10_ok low_0
def G_11 : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00
def R_11 : List Nat := varsOf 41
lemma low_11_ok : carryOK [(2,4),(1,2),(0,1),(0,3)] R_11 G_11 R_0 G_0 = true := by decide +kernel
lemma low_11 : Lower R_11 G_11 4 := carry_of low_11_ok low_0
def G_12 : Nat := 0xffcccc00ffcccc00ffcccc00ffcccc00
def R_12 : List Nat := varsOf 26
lemma low_12_ok : carryOK [(2,5),(2,4),(1,2),(1,3)] R_12 G_12 R_0 G_0 = true := by decide +kernel
lemma low_12 : Lower R_12 G_12 4 := carry_of low_12_ok low_0
def G_13 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
def R_13 : List Nat := varsOf 42
lemma low_13_ok : carryOK [(2,4),(1,2),(1,3)] R_13 G_13 R_0 G_0 = true := by decide +kernel
lemma low_13 : Lower R_13 G_13 4 := carry_of low_13_ok low_0
def G_14 : Nat := 0xfff0f000fff0f000fff0f000fff0f000
def R_14 : List Nat := varsOf 28
lemma low_14_ok : carryOK [(2,5),(2,4),(2,3)] R_14 G_14 R_0 G_0 = true := by decide +kernel
lemma low_14 : Lower R_14 G_14 4 := carry_of low_14_ok low_0
def G_15 : Nat := 0xfff0fff0f000f000fff0fff0f000f000
def R_15 : List Nat := varsOf 44
lemma low_15_ok : carryOK [(2,4),(2,3)] R_15 G_15 R_0 G_0 = true := by decide +kernel
lemma low_15 : Lower R_15 G_15 4 := carry_of low_15_ok low_0
def G_16 : Nat := 0xffffaaaaaaaa0000ffffaaaaaaaa0000
def R_16 : List Nat := varsOf 49
lemma low_16_ok : carryOK [(1,2),(0,1),(0,3)] R_16 G_16 R_0 G_0 = true := by decide +kernel
lemma low_16 : Lower R_16 G_16 4 := carry_of low_16_ok low_0
def G_17 : Nat := 0xffffcccccccc0000ffffcccccccc0000
def R_17 : List Nat := varsOf 50
lemma low_17_ok : carryOK [(1,2),(1,3)] R_17 G_17 R_0 G_0 = true := by decide +kernel
lemma low_17 : Lower R_17 G_17 4 := carry_of low_17_ok low_0
def G_18 : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000
def R_18 : List Nat := varsOf 52
lemma low_18_ok : carryOK [(2,3)] R_18 G_18 R_0 G_0 = true := by decide +kernel
lemma low_18 : Lower R_18 G_18 4 := carry_of low_18_ok low_0
def G_19 : Nat := 0xe8e8e8e800000000e8e8e8e800000000
def R_19 : List Nat := varsOf 39
lemma low_19_ok : liftCheck 0 32 R_19 G_19 R_1 G_1 [(VAR 5,35,3)] = true := by decide +kernel
lemma low_19 : Lower R_19 G_19 5 := lift_of low_19_ok low_1
def G_20 : Nat := 0xfefefefee8e8e8e8fefefefee8e8e8e8
def R_20 : List Nat := varsOf 39
def pos_20 : List Nat := [3,3,5,5,6,6,33,33,34,34,36,36,3,3,5,5,6,6,33,33,34,34,36,36]
def neg_20 : List Nat := [2,1,4,1,4,2,32,1,32,2,32,4,4,32,2,32,1,32,2,4,1,4,1,2]
def fmask_20 : Nat := fullMask 24
def base_20 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf0cf,0x51008a),(0xcccccccccccccccccccccccccccccccc,0x333333,0x844221),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc3cc3c,0x281814),(0xffffffff00000000ffffffff00000000,0xfc0fc0,0x2a540)]
def steps_20 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def W_20 : Array Decor := buildWires base_20 steps_20
def autos_20 : Array (List (Nat × Nat)) := #[[],[(2,5)],[(0,1)],[(2,5),(0,1)],[(1,2)],[(1,5),(1,2)],[(0,1),(0,2)],[(1,5),(0,1),(0,2)],[(1,5),(0,2)]]
def slicesL_20 : List (Nat × Nat) := [(subcube 2 0,4),(subcube 1 0,4),(subcube 32 0,4),(subcube 4 0,4)]
def slices_20 : Array (Nat × Nat) := slicesL_20.toArray
def ps_20 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_20 : Array (Option BoundPool) := buildPools W_20 R_20 slices_20 ps_20
lemma gp_20 : goodPairs G_20 pos_20 neg_20 := goodPairs_of (by decide +kernel)
lemma base_20_ok : ∀ x ∈ base_20, faithful pos_20 neg_20 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_20_ok : ∀ x ∈ W_20.toList, faithful pos_20 neg_20 x ∧ x.1 < 2^128 := buildWires_faithful base_20_ok
lemma autos_20_ok : ∀ sw ∈ autos_20.toList, swapsValid sw = true ∧ permWord sw G_20 = G_20 := autos_of (by decide +kernel)
lemma sl_20_0_ok : sliceDirectCheck 2 0 0 R_20 G_20 R_6 G_6 = true := by decide +kernel
lemma sl_20_0 : Slice R_20 G_20 (subcube 2 0) 4 := slice_direct sl_20_0_ok low_6
lemma sl_20_1_ok : sliceDirectCheck 1 0 0 R_20 G_20 R_9 G_9 = true := by decide +kernel
lemma sl_20_1 : Slice R_20 G_20 (subcube 1 0) 4 := slice_direct sl_20_1_ok low_9
lemma sl_20_2_ok : sliceDirectCheck 32 0 0 R_20 G_20 R_1 G_1 = true := by decide +kernel
lemma sl_20_2 : Slice R_20 G_20 (subcube 32 0) 4 := slice_direct sl_20_2_ok low_1
lemma sl_20_3_ok : sliceDirectCheck 4 0 0 R_20 G_20 R_3 G_3 = true := by decide +kernel
lemma sl_20_3 : Slice R_20 G_20 (subcube 4 0) 4 := slice_direct sl_20_3_ok low_3
set_option maxRecDepth 200000 in
lemma slices_20_ok : ∀ i (hi : i < slices_20.size), Slice R_20 G_20 slices_20[i].1 slices_20[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_20 G_20 p.1 p.2) (forall_cons sl_20_0 (forall_cons sl_20_1 (forall_cons sl_20_2 (forall_cons sl_20_3 (fun _ h => (List.not_mem_nil h).elim)))))
lemma P_20_ok : ∀ i (hi : i < P_20.size), ∀ c, P_20[i] = some c → ValidPool R_20 G_20 c := buildPools_sound slices_20_ok
def bk_20_init : Array (List (List Nat)) := #[]
lemma bk_20_init_ok : ∀ i (hi : i < bk_20_init.size), ∀ xs ∈ bk_20_init[i], Impossible G_20 (0 - 1) xs.toFinset := by intro i hi; simp [bk_20_init] at hi
def nodes_20_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_0 : checkNodes W_20 G_20 fmask_20 P_20 autos_20 bk_20_init 0 nodes_20_0 = true := by decide +kernel
def bk_20_0 : Array (List (List Nat)) := buildBuckets 1 W_20 nodes_20_0
lemma bk_20_0_ok : ∀ i (hi : i < bk_20_0.size), ∀ xs ∈ bk_20_0[i], Impossible G_20 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_init_ok chk_20_0
def nodes_20_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_1 : checkNodes W_20 G_20 fmask_20 P_20 autos_20 bk_20_0 1 nodes_20_1 = true := by decide +kernel
def bk_20_1 : Array (List (List Nat)) := buildBuckets 1 W_20 nodes_20_1
lemma bk_20_1_ok : ∀ i (hi : i < bk_20_1.size), ∀ xs ∈ bk_20_1[i], Impossible G_20 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_0_ok chk_20_1
def nodes_20_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_2 : checkNodes W_20 G_20 fmask_20 P_20 autos_20 bk_20_1 2 nodes_20_2 = true := by decide +kernel
def bk_20_2 : Array (List (List Nat)) := buildBuckets 1 W_20 nodes_20_2
lemma bk_20_2_ok : ∀ i (hi : i < bk_20_2.size), ∀ xs ∈ bk_20_2[i], Impossible G_20 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_1_ok chk_20_2
def nodes_20_3 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_3 : checkNodes W_20 G_20 fmask_20 P_20 autos_20 bk_20_2 3 nodes_20_3 = true := by decide +kernel
def bk_20_3 : Array (List (List Nat)) := buildBuckets 1 W_20 nodes_20_3
lemma bk_20_3_ok : ∀ i (hi : i < bk_20_3.size), ∀ xs ∈ bk_20_3[i], Impossible G_20 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_2_ok chk_20_3
def nodes_20_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_4 : checkNodes W_20 G_20 fmask_20 P_20 autos_20 bk_20_3 4 nodes_20_4 = true := by decide +kernel
def bk_20_4 : Array (List (List Nat)) := buildBuckets 2 W_20 nodes_20_4
lemma bk_20_4_ok : ∀ i (hi : i < bk_20_4.size), ∀ xs ∈ bk_20_4[i], Impossible G_20 4 xs.toFinset :=
  buildBuckets_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_3_ok chk_20_4
def nodes_20_5 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_5 : checkNodes W_20 G_20 fmask_20 P_20 autos_20 bk_20_4 5 nodes_20_5 = true := by decide +kernel
def bk_20_5 : Array (List (List Nat)) := buildBuckets 1 W_20 nodes_20_5
lemma bk_20_5_ok : ∀ i (hi : i < bk_20_5.size), ∀ xs ∈ bk_20_5[i], Impossible G_20 5 xs.toFinset :=
  buildBuckets_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_4_ok chk_20_5
def nodes_20_6 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_6 : checkNodes W_20 G_20 fmask_20 P_20 autos_20 bk_20_5 6 nodes_20_6 = true := by decide +kernel
def bk_20_6 : Array (List (List Nat)) := buildBuckets 1 W_20 nodes_20_6
lemma bk_20_6_ok : ∀ i (hi : i < bk_20_6.size), ∀ xs ∈ bk_20_6[i], Impossible G_20 6 xs.toFinset :=
  buildBuckets_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_5_ok chk_20_6
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_20_ok : forestRootCheck R_20 G_20 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 5,33,1)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_20_in : bucketContains bk_20_6 R_20 = true := by decide +kernel
lemma low_20 : Lower R_20 G_20 7 := lower_of_forest root_20_ok bk_20_6_ok root_20_in
def G_21 : Nat := 0xfff0f000f0000000fff0f000f0000000
def R_21 : List Nat := varsOf 60
def pos_21 : List Nat := [28,28,28,44,44,44,52,52,52,56,56,56,28,28,28,44,44,44,52,52,52,56,56,56]
def neg_21 : List Nat := [24,20,12,40,36,12,48,36,20,48,40,24,36,40,48,20,24,48,12,24,40,12,20,36]
def fmask_21 : Nat := fullMask 24
def base_21 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1ff1ff,0xe491b6),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xe3fe3f,0x3d2c2d),(0xffff0000ffff0000ffff0000ffff0000,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def steps_21 : List (Nat × Nat × Nat) := [(0,0,1),(0,0,2),(3,4,2),(0,4,2),(0,1,2),(3,7,3)]
def W_21 : Array Decor := buildWires base_21 steps_21
def autos_21 : Array (List (Nat × Nat)) := #[[],[(4,5)],[(2,3)],[(4,5),(2,3)],[(3,4)],[(3,5),(3,4)],[(2,3),(2,4)],[(3,5),(2,3),(2,4)],[(3,5),(2,4)]]
def slicesL_21 : List (Nat × Nat) := [(subcube 0 16,4),(subcube 0 4,4),(subcube 0 8,4),(subcube 0 32,4)]
def slices_21 : Array (Nat × Nat) := slicesL_21.toArray
def ps_21 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_21 : Array (Option BoundPool) := buildPools W_21 R_21 slices_21 ps_21
lemma gp_21 : goodPairs G_21 pos_21 neg_21 := goodPairs_of (by decide +kernel)
lemma base_21_ok : ∀ x ∈ base_21, faithful pos_21 neg_21 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_21_ok : ∀ x ∈ W_21.toList, faithful pos_21 neg_21 x ∧ x.1 < 2^128 := buildWires_faithful base_21_ok
lemma autos_21_ok : ∀ sw ∈ autos_21.toList, swapsValid sw = true ∧ permWord sw G_21 = G_21 := autos_of (by decide +kernel)
lemma sl_21_0_ok : sliceDirectCheck 0 16 0 R_21 G_21 R_15 G_15 = true := by decide +kernel
lemma sl_21_0 : Slice R_21 G_21 (subcube 0 16) 4 := slice_direct sl_21_0_ok low_15
lemma sl_21_1_ok : sliceDirectCheck 0 4 0 R_21 G_21 R_0 G_0 = true := by decide +kernel
lemma sl_21_1 : Slice R_21 G_21 (subcube 0 4) 4 := slice_direct sl_21_1_ok low_0
lemma sl_21_2_ok : sliceDirectCheck 0 8 0 R_21 G_21 R_18 G_18 = true := by decide +kernel
lemma sl_21_2 : Slice R_21 G_21 (subcube 0 8) 4 := slice_direct sl_21_2_ok low_18
lemma sl_21_3_ok : sliceDirectCheck 0 32 0 R_21 G_21 R_14 G_14 = true := by decide +kernel
lemma sl_21_3 : Slice R_21 G_21 (subcube 0 32) 4 := slice_direct sl_21_3_ok low_14
set_option maxRecDepth 200000 in
lemma slices_21_ok : ∀ i (hi : i < slices_21.size), Slice R_21 G_21 slices_21[i].1 slices_21[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_21 G_21 p.1 p.2) (forall_cons sl_21_0 (forall_cons sl_21_1 (forall_cons sl_21_2 (forall_cons sl_21_3 (fun _ h => (List.not_mem_nil h).elim)))))
lemma P_21_ok : ∀ i (hi : i < P_21.size), ∀ c, P_21[i] = some c → ValidPool R_21 G_21 c := buildPools_sound slices_21_ok
def bk_21_init : Array (List (List Nat)) := #[]
lemma bk_21_init_ok : ∀ i (hi : i < bk_21_init.size), ∀ xs ∈ bk_21_init[i], Impossible G_21 (0 - 1) xs.toFinset := by intro i hi; simp [bk_21_init] at hi
def nodes_21_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_21_0 : checkNodes W_21 G_21 fmask_21 P_21 autos_21 bk_21_init 0 nodes_21_0 = true := by decide +kernel
def bk_21_0 : Array (List (List Nat)) := buildBuckets 1 W_21 nodes_21_0
lemma bk_21_0_ok : ∀ i (hi : i < bk_21_0.size), ∀ xs ∈ bk_21_0[i], Impossible G_21 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_21 W_21_ok P_21_ok autos_21_ok bk_21_init_ok chk_21_0
def nodes_21_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_21_1 : checkNodes W_21 G_21 fmask_21 P_21 autos_21 bk_21_0 1 nodes_21_1 = true := by decide +kernel
def bk_21_1 : Array (List (List Nat)) := buildBuckets 1 W_21 nodes_21_1
lemma bk_21_1_ok : ∀ i (hi : i < bk_21_1.size), ∀ xs ∈ bk_21_1[i], Impossible G_21 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_21 W_21_ok P_21_ok autos_21_ok bk_21_0_ok chk_21_1
def nodes_21_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_21_2 : checkNodes W_21 G_21 fmask_21 P_21 autos_21 bk_21_1 2 nodes_21_2 = true := by decide +kernel
def bk_21_2 : Array (List (List Nat)) := buildBuckets 1 W_21 nodes_21_2
lemma bk_21_2_ok : ∀ i (hi : i < bk_21_2.size), ∀ xs ∈ bk_21_2[i], Impossible G_21 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_21 W_21_ok P_21_ok autos_21_ok bk_21_1_ok chk_21_2
def nodes_21_3 : List NodeSpec := [([4,5,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_21_3 : checkNodes W_21 G_21 fmask_21 P_21 autos_21 bk_21_2 3 nodes_21_3 = true := by decide +kernel
def bk_21_3 : Array (List (List Nat)) := buildBuckets 1 W_21 nodes_21_3
lemma bk_21_3_ok : ∀ i (hi : i < bk_21_3.size), ∀ xs ∈ bk_21_3[i], Impossible G_21 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_21 W_21_ok P_21_ok autos_21_ok bk_21_2_ok chk_21_3
def nodes_21_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([6,0,1,2,3],[],[]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_21_4 : checkNodes W_21 G_21 fmask_21 P_21 autos_21 bk_21_3 4 nodes_21_4 = true := by decide +kernel
def bk_21_4 : Array (List (List Nat)) := buildBuckets 2 W_21 nodes_21_4
lemma bk_21_4_ok : ∀ i (hi : i < bk_21_4.size), ∀ xs ∈ bk_21_4[i], Impossible G_21 4 xs.toFinset :=
  buildBuckets_sound (by decide) gp_21 W_21_ok P_21_ok autos_21_ok bk_21_3_ok chk_21_4
def nodes_21_5 : List NodeSpec := [([4,0,1,2,3],[2,1,0,3],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_21_5 : checkNodes W_21 G_21 fmask_21 P_21 autos_21 bk_21_4 5 nodes_21_5 = true := by decide +kernel
def bk_21_5 : Array (List (List Nat)) := buildBuckets 1 W_21 nodes_21_5
lemma bk_21_5_ok : ∀ i (hi : i < bk_21_5.size), ∀ xs ∈ bk_21_5[i], Impossible G_21 5 xs.toFinset :=
  buildBuckets_sound (by decide) gp_21 W_21_ok P_21_ok autos_21_ok bk_21_4_ok chk_21_5
def nodes_21_6 : List NodeSpec := [([0,1,2,3],[1,2,0,3],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_21_6 : checkNodes W_21 G_21 fmask_21 P_21 autos_21 bk_21_5 6 nodes_21_6 = true := by decide +kernel
def bk_21_6 : Array (List (List Nat)) := buildBuckets 1 W_21 nodes_21_6
lemma bk_21_6_ok : ∀ i (hi : i < bk_21_6.size), ∀ xs ∈ bk_21_6[i], Impossible G_21 6 xs.toFinset :=
  buildBuckets_sound (by decide) gp_21 W_21_ok P_21_ok autos_21_ok bk_21_5_ok chk_21_6
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_21_ok : forestRootCheck R_21 G_21 [(VAR 2,28,24),(VAR 3,28,20),(VAR 4,28,12),(VAR 5,44,12)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_21_in : bucketContains bk_21_6 R_21 = true := by decide +kernel
lemma low_21 : Lower R_21 G_21 7 := lower_of_forest root_21_ok bk_21_6_ok root_21_in
def G_22 : Nat := 0xfffffcfcfcfc0000fffffcfcfcfc0000
def R_22 : List Nat := varsOf 54
lemma low_22_ok : liftCheck 2 0 R_22 G_22 R_18 G_18 [(VAR 1,18,16)] = true := by decide +kernel
lemma low_22 : Lower R_22 G_22 5 := lift_of low_22_ok low_18
def G_23 : Nat := 0xe800e800e800e800e800e800e800e800
def R_23 : List Nat := varsOf 15
lemma low_23_ok : carryOK [(3,4),(3,5)] R_23 G_23 R_19 G_19 = true := by decide +kernel
lemma low_23 : Lower R_23 G_23 5 := carry_of low_23_ok low_19
def G_24 : Nat := 0xe8e80000e8e80000e8e80000e8e80000
def R_24 : List Nat := varsOf 23
lemma low_24_ok : carryOK [(4,5)] R_24 G_24 R_19 G_19 = true := by decide +kernel
lemma low_24 : Lower R_24 G_24 5 := carry_of low_24_ok low_19
def G_25 : Nat := 0xee888800ee888800ee888800ee888800
def R_25 : List Nat := varsOf 27
lemma low_25_ok : carryOK [(1,5),(1,4),(1,3),(0,2)] R_25 G_25 R_21 G_21 = true := by decide +kernel
lemma low_25 : Lower R_25 G_25 7 := carry_of low_25_ok low_21
def G_26 : Nat := 0xee88ee8888008800ee88ee8888008800
def R_26 : List Nat := varsOf 43
lemma low_26_ok : carryOK [(1,4),(1,3),(0,2)] R_26 G_26 R_21 G_21 = true := by decide +kernel
lemma low_26 : Lower R_26 G_26 7 := carry_of low_26_ok low_21
def G_27 : Nat := 0xeeee888888880000eeee888888880000
def R_27 : List Nat := varsOf 51
lemma low_27_ok : carryOK [(1,3),(0,2)] R_27 G_27 R_21 G_21 = true := by decide +kernel
lemma low_27 : Lower R_27 G_27 7 := carry_of low_27_ok low_21
def G_28 : Nat := 0xfaa0a000faa0a000faa0a000faa0a000
def R_28 : List Nat := varsOf 29
lemma low_28_ok : carryOK [(1,5),(1,4),(1,3),(0,1),(0,2)] R_28 G_28 R_21 G_21 = true := by decide +kernel
lemma low_28 : Lower R_28 G_28 7 := carry_of low_28_ok low_21
def G_29 : Nat := 0xfaa0faa0a000a000faa0faa0a000a000
def R_29 : List Nat := varsOf 45
lemma low_29_ok : carryOK [(1,4),(1,3),(0,1),(0,2)] R_29 G_29 R_21 G_21 = true := by decide +kernel
lemma low_29 : Lower R_29 G_29 7 := carry_of low_29_ok low_21
def G_30 : Nat := 0xfafaa0a0a0a00000fafaa0a0a0a00000
def R_30 : List Nat := varsOf 53
lemma low_30_ok : carryOK [(1,3),(0,1),(0,2)] R_30 G_30 R_21 G_21 = true := by decide +kernel
lemma low_30 : Lower R_30 G_30 7 := carry_of low_30_ok low_21
def G_31 : Nat := 0xfcc0c000fcc0c000fcc0c000fcc0c000
def R_31 : List Nat := varsOf 30
lemma low_31_ok : carryOK [(1,5),(1,4),(1,3),(1,2)] R_31 G_31 R_21 G_21 = true := by decide +kernel
lemma low_31 : Lower R_31 G_31 7 := carry_of low_31_ok low_21
def G_32 : Nat := 0xfcc0fcc0c000c000fcc0fcc0c000c000
def R_32 : List Nat := varsOf 46
lemma low_32_ok : carryOK [(1,4),(1,3),(1,2)] R_32 G_32 R_21 G_21 = true := by decide +kernel
lemma low_32 : Lower R_32 G_32 7 := carry_of low_32_ok low_21
def G_33 : Nat := 0xfcfcc0c0c0c00000fcfcc0c0c0c00000
def R_33 : List Nat := varsOf 54
lemma low_33_ok : carryOK [(1,3),(1,2)] R_33 G_33 R_21 G_21 = true := by decide +kernel
lemma low_33 : Lower R_33 G_33 7 := carry_of low_33_ok low_21
def G_34 : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8
def R_34 : List Nat := varsOf 15
lemma low_34_ok : carryOK [(3,4),(3,5)] R_34 G_34 R_20 G_20 = true := by decide +kernel
lemma low_34 : Lower R_34 G_34 7 := carry_of low_34_ok low_20
def G_35 : Nat := 0xfefee8e8fefee8e8fefee8e8fefee8e8
def R_35 : List Nat := varsOf 23
lemma low_35_ok : carryOK [(4,5)] R_35 G_35 R_20 G_20 = true := by decide +kernel
lemma low_35 : Lower R_35 G_35 7 := carry_of low_35_ok low_20
def G_36 : Nat := 0xffaaaa00aa000000ffaaaa00aa000000
def R_36 : List Nat := varsOf 57
lemma low_36_ok : carryOK [(0,1),(0,2)] R_36 G_36 R_21 G_21 = true := by decide +kernel
lemma low_36 : Lower R_36 G_36 7 := carry_of low_36_ok low_21
def G_37 : Nat := 0xffcccc00cc000000ffcccc00cc000000
def R_37 : List Nat := varsOf 58
lemma low_37_ok : carryOK [(1,2)] R_37 G_37 R_21 G_21 = true := by decide +kernel
lemma low_37 : Lower R_37 G_37 7 := carry_of low_37_ok low_21
def G_38 : Nat := 0xffeeee00ffeeee00ffeeee00ffeeee00
def R_38 : List Nat := varsOf 27
lemma low_38_ok : carryOK [(3,5),(3,4),(0,2),(0,1)] R_38 G_38 R_22 G_22 = true := by decide +kernel
lemma low_38 : Lower R_38 G_38 5 := carry_of low_38_ok low_22
def G_39 : Nat := 0xffeeffeeee00ee00ffeeffeeee00ee00
def R_39 : List Nat := varsOf 43
lemma low_39_ok : carryOK [(3,4),(0,2),(0,1)] R_39 G_39 R_22 G_22 = true := by decide +kernel
lemma low_39 : Lower R_39 G_39 5 := carry_of low_39_ok low_22
def G_40 : Nat := 0xfffafa00fffafa00fffafa00fffafa00
def R_40 : List Nat := varsOf 29
lemma low_40_ok : carryOK [(3,5),(3,4),(0,1)] R_40 G_40 R_22 G_22 = true := by decide +kernel
lemma low_40 : Lower R_40 G_40 5 := carry_of low_40_ok low_22
def G_41 : Nat := 0xfffafffafa00fa00fffafffafa00fa00
def R_41 : List Nat := varsOf 45
lemma low_41_ok : carryOK [(3,4),(0,1)] R_41 G_41 R_22 G_22 = true := by decide +kernel
lemma low_41 : Lower R_41 G_41 5 := carry_of low_41_ok low_22
def G_42 : Nat := 0xfffcfc00fffcfc00fffcfc00fffcfc00
def R_42 : List Nat := varsOf 30
lemma low_42_ok : carryOK [(3,5),(3,4)] R_42 G_42 R_22 G_22 = true := by decide +kernel
lemma low_42 : Lower R_42 G_42 5 := carry_of low_42_ok low_22
def G_43 : Nat := 0xfffcfffcfc00fc00fffcfffcfc00fc00
def R_43 : List Nat := varsOf 46
lemma low_43_ok : carryOK [(3,4)] R_43 G_43 R_22 G_22 = true := by decide +kernel
lemma low_43 : Lower R_43 G_43 5 := carry_of low_43_ok low_22
def G_44 : Nat := 0xffffeeeeeeee0000ffffeeeeeeee0000
def R_44 : List Nat := varsOf 51
lemma low_44_ok : carryOK [(0,2),(0,1)] R_44 G_44 R_22 G_22 = true := by decide +kernel
lemma low_44 : Lower R_44 G_44 5 := carry_of low_44_ok low_22
def G_45 : Nat := 0xfffffafafafa0000fffffafafafa0000
def R_45 : List Nat := varsOf 53
lemma low_45_ok : carryOK [(0,1)] R_45 G_45 R_22 G_22 = true := by decide +kernel
lemma low_45 : Lower R_45 G_45 5 := carry_of low_45_ok low_22
def G_46 : Nat := 0xe8e8000000000000e8e8000000000000
def R_46 : List Nat := varsOf 55
lemma low_46_ok : liftCheck 0 16 R_46 G_46 R_19 G_19 [(VAR 4,51,35)] = true := by decide +kernel
lemma low_46 : Lower R_46 G_46 6 := lift_of low_46_ok low_19
def G_47 : Nat := 0xfcc0c000c0000000fcc0c000c0000000
def R_47 : List Nat := varsOf 62
def pos_47 : List Nat := [30,30,30,30,46,46,46,46,54,54,54,54,58,58,58,58,60,60,60,60,30,30,30,30,30,30,46,46,46,46,46,46,54,54,54,54,54,54,58,58,58,58,58,58,60,60,60,60,60,60]
def neg_47 : List Nat := [28,26,22,14,44,42,38,14,52,50,38,22,56,50,42,26,56,52,44,28,38,42,44,50,52,56,22,26,28,50,52,56,14,26,28,42,44,56,14,22,28,38,44,52,14,22,26,38,42,50]
def fmask_47 : Nat := fullMask 50
def base_47 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xffffff0ffff,0x3f2cb2cb0eeee),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3f03fffff0fff,0xbfd5555e0ddd),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3ffc0fffff0ff,0x1557f9a6dd0bb),(0xffff0000ffff0000ffff0000ffff0000,0x3ffff03ffff0f,0x269a6ff8bbb07),(0xffffffff00000000ffffffff00000000,0x3fffffc0ffff0,0x38e38e3f77770)]
def steps_47 : List (Nat × Nat × Nat) := [(0,0,1),(0,2,3),(0,0,2),(3,5,2),(0,5,2),(0,1,3),(0,3,4),(3,8,3),(2,5,6),(0,9,3),(0,1,2),(0,0,3),(3,9,3),(0,5,3),(3,13,0),(0,1,4),(0,2,4),(3,12,4),(3,16,4),(3,14,4),(0,0,4),(3,14,0),(0,12,4),(1,14,4),(2,2,11),(0,17,4),(0,14,4),(0,16,4),(3,17,4),(3,14,1),(3,31,0)]
def W_47 : Array Decor := buildWires base_47 steps_47
def autos_47 : Array (List (Nat × Nat)) := #[[],[(1,2)],[(1,3),(1,2)],[(1,2),(2,4),(1,5)],[(4,5)],[(1,5),(1,4),(1,3),(1,2)],[(3,5),(3,4)],[(3,5),(2,3),(2,4)],[(3,5),(1,2),(1,4)],[(2,3),(1,3),(2,5),(1,4)],[(2,3),(3,5),(2,4)],[(3,4),(3,5)],[(3,4)],[(3,4),(2,3),(2,5)],[(2,3),(2,4)],[(3,4),(2,3),(1,2),(1,5)],[(2,3),(1,2),(1,4)],[(3,5),(2,3),(1,2),(1,4)],[(3,5),(2,4)],[(2,5),(2,4),(2,3)],[(2,4)],[(2,3),(3,5),(1,2),(1,4)],[(2,3)],[(1,4),(1,3),(1,2)],[(2,4),(2,3)],[(4,5),(1,2),(1,3)],[(2,5),(1,4)],[(4,5),(1,2)],[(4,5),(2,3)],[(1,2),(1,4)],[(3,4),(1,2)],[(4,5),(1,3),(1,2)],[(2,5),(2,4)],[(3,5),(3,4),(1,2)],[(1,3),(1,4),(1,2)],[(3,5),(1,3),(1,4),(1,2)],[(2,4),(1,3)],[(1,2),(2,3),(1,4)],[(1,2),(1,3)],[(2,4),(1,2),(1,3)],[(2,3),(2,5),(1,4)],[(2,5),(2,4),(1,2),(1,3)],[(2,5),(2,4),(1,3)],[(1,2),(1,5),(2,4),(1,3)]]
def slicesL_47 : List (Nat × Nat) := [(subcube 0 12,4),(subcube 0 6,4),(subcube 0 32,7),(subcube 0 48,4),(subcube 0 2,7),(subcube 0 24,4),(subcube 0 20,4),(subcube 0 10,4),(subcube 0 8,7),(subcube 0 16,7),(subcube 0 4,7),(subcube 0 34,4),(subcube 0 18,4)]
def slices_47 : Array (Nat × Nat) := slicesL_47.toArray
def ps_47 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(2,[(0,0,1),(0,0,2),(0,1,2)]),(8,[(0,0,1),(0,0,3),(0,1,3)]),(9,[]),(4,[(0,5,2),(0,9,3),(3,14,4)]),(2,[(0,0,1),(0,5,2),(3,9,3)]),(4,[(0,5,2),(0,5,3),(0,2,3)]),(10,[]),(9,[(0,0,1),(0,0,2)]),(8,[(0,0,1),(0,1,3)]),(2,[(0,0,1),(3,5,2)]),(8,[(0,0,1),(3,8,3)]),(9,[(0,0,1),(3,5,2)]),(4,[(0,2,3),(2,5,6)]),(8,[]),(9,[(0,0,1),(0,5,2)]),(4,[(0,5,2),(0,2,3)]),(2,[(0,0,1),(0,5,2)]),(4,[(0,1,2)]),(9,[(0,0,1),(0,0,2),(0,1,2)]),(10,[(0,5,2),(0,0,3)]),(8,[(0,0,1),(0,0,3)]),(11,[]),(4,[(0,5,2),(0,9,3)]),(4,[(0,5,2),(3,9,3)]),(10,[(0,5,2),(3,9,3)]),(8,[(0,0,1),(3,9,3)]),(2,[(0,0,1),(0,0,2)]),(10,[(0,5,2),(0,9,3)]),(8,[(0,0,1),(0,9,3)]),(4,[(0,5,2),(0,5,3)]),(12,[]),(8,[(0,0,1)]),(9,[(0,0,1)]),(4,[(0,2,3)]),(10,[(0,2,3)]),(10,[(0,0,2)]),(4,[(0,5,2)]),(10,[(0,5,2)]),(2,[(0,0,1)])]
def P_47 : Array (Option BoundPool) := buildPools W_47 R_47 slices_47 ps_47
lemma gp_47 : goodPairs G_47 pos_47 neg_47 := goodPairs_of (by decide +kernel)
lemma base_47_ok : ∀ x ∈ base_47, faithful pos_47 neg_47 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_47_ok : ∀ x ∈ W_47.toList, faithful pos_47 neg_47 x ∧ x.1 < 2^128 := buildWires_faithful base_47_ok
lemma autos_47_ok : ∀ sw ∈ autos_47.toList, swapsValid sw = true ∧ permWord sw G_47 = G_47 := autos_of (by decide +kernel)
lemma sl_47_0_ok : sliceDirectCheck 0 12 0 R_47 G_47 R_17 G_17 = true := by decide +kernel
lemma sl_47_0 : Slice R_47 G_47 (subcube 0 12) 4 := slice_direct sl_47_0_ok low_17
lemma sl_47_1_ok : sliceDirectCheck 0 6 0 R_47 G_47 R_0 G_0 = true := by decide +kernel
lemma sl_47_1 : Slice R_47 G_47 (subcube 0 6) 4 := slice_direct sl_47_1_ok low_0
lemma sl_47_2_ok : sliceDirectCheck 0 32 0 R_47 G_47 R_31 G_31 = true := by decide +kernel
lemma sl_47_2 : Slice R_47 G_47 (subcube 0 32) 7 := slice_direct sl_47_2_ok low_31
lemma sl_47_3_ok : sliceDirectCheck 0 48 0 R_47 G_47 R_7 G_7 = true := by decide +kernel
lemma sl_47_3 : Slice R_47 G_47 (subcube 0 48) 4 := slice_direct sl_47_3_ok low_7
lemma sl_47_4_ok : sliceDirectCheck 0 2 0 R_47 G_47 R_21 G_21 = true := by decide +kernel
lemma sl_47_4 : Slice R_47 G_47 (subcube 0 2) 7 := slice_direct sl_47_4_ok low_21
lemma sl_47_5_ok : sliceDirectCheck 0 24 0 R_47 G_47 R_9 G_9 = true := by decide +kernel
lemma sl_47_5 : Slice R_47 G_47 (subcube 0 24) 4 := slice_direct sl_47_5_ok low_9
lemma sl_47_6_ok : sliceDirectCheck 0 20 0 R_47 G_47 R_13 G_13 = true := by decide +kernel
lemma sl_47_6 : Slice R_47 G_47 (subcube 0 20) 4 := slice_direct sl_47_6_ok low_13
lemma sl_47_7_ok : sliceDirectCheck 0 10 0 R_47 G_47 R_18 G_18 = true := by decide +kernel
lemma sl_47_7 : Slice R_47 G_47 (subcube 0 10) 4 := slice_direct sl_47_7_ok low_18
lemma sl_47_8_ok : sliceDirectCheck 0 8 0 R_47 G_47 R_33 G_33 = true := by decide +kernel
lemma sl_47_8 : Slice R_47 G_47 (subcube 0 8) 7 := slice_direct sl_47_8_ok low_33
lemma sl_47_9_ok : sliceDirectCheck 0 16 0 R_47 G_47 R_32 G_32 = true := by decide +kernel
lemma sl_47_9 : Slice R_47 G_47 (subcube 0 16) 7 := slice_direct sl_47_9_ok low_32
lemma sl_47_10_ok : sliceDirectCheck 0 4 0 R_47 G_47 R_37 G_37 = true := by decide +kernel
lemma sl_47_10 : Slice R_47 G_47 (subcube 0 4) 7 := slice_direct sl_47_10_ok low_37
lemma sl_47_11_ok : sliceDirectCheck 0 34 0 R_47 G_47 R_14 G_14 = true := by decide +kernel
lemma sl_47_11 : Slice R_47 G_47 (subcube 0 34) 4 := slice_direct sl_47_11_ok low_14
lemma sl_47_12_ok : sliceDirectCheck 0 18 0 R_47 G_47 R_15 G_15 = true := by decide +kernel
lemma sl_47_12 : Slice R_47 G_47 (subcube 0 18) 4 := slice_direct sl_47_12_ok low_15
set_option maxRecDepth 200000 in
lemma slices_47_ok : ∀ i (hi : i < slices_47.size), Slice R_47 G_47 slices_47[i].1 slices_47[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_47 G_47 p.1 p.2) (forall_cons sl_47_0 (forall_cons sl_47_1 (forall_cons sl_47_2 (forall_cons sl_47_3 (forall_cons sl_47_4 (forall_cons sl_47_5 (forall_cons sl_47_6 (forall_cons sl_47_7 (forall_cons sl_47_8 (forall_cons sl_47_9 (forall_cons sl_47_10 (forall_cons sl_47_11 (forall_cons sl_47_12 (fun _ h => (List.not_mem_nil h).elim))))))))))))))
lemma P_47_ok : ∀ i (hi : i < P_47.size), ∀ c, P_47[i] = some c → ValidPool R_47 G_47 c := buildPools_sound slices_47_ok
def bk_47_init : Array (List (List Nat)) := #[]
lemma bk_47_init_ok : ∀ i (hi : i < bk_47_init.size), ∀ xs ∈ bk_47_init[i], Impossible G_47 (0 - 1) xs.toFinset := by intro i hi; simp [bk_47_init] at hi
def nodes_47_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_47_0 : checkNodes W_47 G_47 fmask_47 P_47 autos_47 bk_47_init 0 nodes_47_0 = true := by decide +kernel
def bk_47_0 : Array (List (List Nat)) := buildBuckets 1 W_47 nodes_47_0
lemma bk_47_0_ok : ∀ i (hi : i < bk_47_0.size), ∀ xs ∈ bk_47_0[i], Impossible G_47 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_47 W_47_ok P_47_ok autos_47_ok bk_47_init_ok chk_47_0
def nodes_47_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_47_1 : checkNodes W_47 G_47 fmask_47 P_47 autos_47 bk_47_0 1 nodes_47_1 = true := by decide +kernel
def bk_47_1 : Array (List (List Nat)) := buildBuckets 1 W_47 nodes_47_1
lemma bk_47_1_ok : ∀ i (hi : i < bk_47_1.size), ∀ xs ∈ bk_47_1[i], Impossible G_47 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_47 W_47_ok P_47_ok autos_47_ok bk_47_0_ok chk_47_1
def nodes_47_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_47_2 : checkNodes W_47 G_47 fmask_47 P_47 autos_47 bk_47_1 2 nodes_47_2 = true := by decide +kernel
def bk_47_2 : Array (List (List Nat)) := buildBuckets 1 W_47 nodes_47_2
lemma bk_47_2_ok : ∀ i (hi : i < bk_47_2.size), ∀ xs ∈ bk_47_2[i], Impossible G_47 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_47 W_47_ok P_47_ok autos_47_ok bk_47_1_ok chk_47_2
def nodes_47_3 : List NodeSpec := [([29,8,16,20],[],[]),([29,12,25,1],[],[]),([9,32,10,21],[0],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_47_3 : checkNodes W_47 G_47 fmask_47 P_47 autos_47 bk_47_2 3 nodes_47_3 = true := by decide +kernel
def bk_47_3 : Array (List (List Nat)) := buildBuckets 2 W_47 nodes_47_3
lemma bk_47_3_ok : ∀ i (hi : i < bk_47_3.size), ∀ xs ∈ bk_47_3[i], Impossible G_47 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_47 W_47_ok P_47_ok autos_47_ok bk_47_2_ok chk_47_3
def nodes_47_4 : List NodeSpec := [([8,16,20,2,11],[1],[0]),([23,8,10,2,4],[],[]),([29,12,0,1,4],[],[0,1]),([12,25,1,2,11],[2],[0]),([12,25,20,2,3],[],[]),([26,34,2,3,4],[],[]),([26,1,2,3,28],[],[]),([9,16,20,2,11],[3],[2]),([23,9,10,2,4],[],[]),([17,25,20,2,3],[],[]),([35,1,2,3,4],[],[]),([9,32,10,2,4],[0],[0]),([9,16,10,21,4],[],[0,1]),([5,7,10,21,11],[],[]),([29,8,16,1,4],[],[3,4,0]),([14,25,20,2,3],[2],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_47_4 : checkNodes W_47 G_47 fmask_47 P_47 autos_47 bk_47_3 4 nodes_47_4 = true := by decide +kernel
def bk_47_4 : Array (List (List Nat)) := buildBuckets 6 W_47 nodes_47_4
lemma bk_47_4_ok : ∀ i (hi : i < bk_47_4.size), ∀ xs ∈ bk_47_4[i], Impossible G_47 4 xs.toFinset :=
  buildBuckets_sound (by decide) gp_47 W_47_ok P_47_ok autos_47_ok bk_47_3_ok chk_47_4
def nodes_47_5 : List NodeSpec := [([5,19,1,2,3,4],[4],[]),([14,0,1,2,3,4],[2],[5]),([5,7,10,6,4],[5,1,6,7],[6,7,8,9]),([8,16,1,2,11,4],[1],[4,8,0]),([8,16,20,2,3,4],[],[10,8,0]),([5,7,15,11,3,4],[5,1,6,7,0,8],[11,12,6,13,14,7,15,16,17]),([8,16,10,2,4],[5,1,9],[4,18,8]),([5,7,10,21,3,4],[],[19,20,15,21,9,0]),([12,0,1,2,11,4],[2],[0,1]),([22,0,1,2,3,4],[],[]),([23,8,1,2,3,4],[],[0]),([9,16,10,2,4],[10,0,7,1,9],[4,0,1]),([9,5,16,10,2,4],[0,6,7,1],[]),([24,5,0,1,2,3],[11],[]),([9,5,16,1,6,4],[0,7,6,1],[]),([17,25,1,2,3,4],[2,12],[0,22]),([17,5,16,1,2,4],[10,7],[]),([26,5,1,2,3,4],[4],[]),([12,25,1,2,3,4],[2],[0]),([27,0,1,2,3,4],[],[2]),([24,0,1,2,3,4],[],[]),([14,0,1,2,3,28],[],[0,1,2,23,5]),([9,16,1,2,11,4],[3],[19,1,0,2,22]),([26,9,1,2,3,4],[4],[24]),([14,25,1,2,3,4],[2],[0,22,24]),([9,16,20,2,3,4],[],[4,1,22,25,0]),([26,14,1,2,3,4],[4],[0,22,24]),([29,8,0,1,3,4],[],[2,26,3,0,4,27]),([30,0,1,2,3,4],[12],[]),([17,9,16,1,2,4],[10,7,1],[]),([24,14,0,1,2,3],[2],[]),([9,18,0,1,6,4],[0,6,13],[]),([24,9,0,1,2,3],[],[]),([23,9,1,2,3,4],[],[0,22]),([24,0,1,2,3],[],[]),([31,0,1,2,3,4],[],[0,1,2,23,5]),([9,32,1,2,3,4],[0],[0,4,22,28]),([33,0,1,2,3,4],[12],[23])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_47_5 : checkNodes W_47 G_47 fmask_47 P_47 autos_47 bk_47_4 5 nodes_47_5 = true := by decide +kernel
def bk_47_5 : Array (List (List Nat)) := buildBuckets 13 W_47 nodes_47_5
lemma bk_47_5_ok : ∀ i (hi : i < bk_47_5.size), ∀ xs ∈ bk_47_5[i], Impossible G_47 5 xs.toFinset :=
  buildBuckets_sound (by decide) gp_47 W_47_ok P_47_ok autos_47_ok bk_47_4_ok chk_47_5
def nodes_47_6 : List NodeSpec := [([5,7,10,2,3,4],[14,4,1,6,7,15,16],[6,20,14,7,16,29,8,0,30]),([8,0,1,2,11,3,4],[1,3,0,17],[0,4,18,8,1,27]),([12,0,1,2,3,4],[6,4,1,18,2,19],[0,1]),([13,5,0,1,2,3,4],[20],[0,1]),([9,5,0,1,6,3,4],[21,0,7,6,1,22,23],[0,1]),([14,9,0,1,2,3,4],[10,24,22],[0,1,2,23]),([9,0,1,2,11,3,4],[3,1,0,24],[0,23,5,4,1,27,2,31]),([5,7,15,3,4],[25,14,21,1,0,26,8,7],[12,6,14,7,16,17,0]),([9,16,1,2,3,4],[10,0,7,1,22,27,28],[0,4,22]),([17,9,0,1,2,3,4],[10,0,1,7,22],[23,0,1,2]),([14,5,0,1,2,3,4],[5,29,30],[0,1]),([17,5,0,1,2,3,4],[21,10,6,0,7,22,31],[23,0,1]),([8,16,1,2,3,4],[5,4,1,28,19],[4,18,0]),([17,0,1,2,3,4],[0,4,7,1,22,2,31,32,33,12],[23,0,1,2]),([5,7,1,2,11,3,4],[5,1,6,7,34],[11,24,19,13,20,32,0,8,30,33,9,34,35]),([14,0,1,2,3,4],[30,35,36,22,2],[0,1,2,23]),([9,5,16,1,2,3,4],[0,7,6,1],[0]),([9,18,0,1,2,3,4],[22,21,0,37],[23,2,0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_47_6 : checkNodes W_47 G_47 fmask_47 P_47 autos_47 bk_47_5 6 nodes_47_6 = true := by decide +kernel
def bk_47_6 : Array (List (List Nat)) := buildBuckets 7 W_47 nodes_47_6
lemma bk_47_6_ok : ∀ i (hi : i < bk_47_6.size), ∀ xs ∈ bk_47_6[i], Impossible G_47 6 xs.toFinset :=
  buildBuckets_sound (by decide) gp_47 W_47_ok P_47_ok autos_47_ok bk_47_5_ok chk_47_6
def nodes_47_7 : List NodeSpec := [([5,0,1,6,2,3,4],[0,38,5,1,39,40,3,41,42,29],[0,36,2,23,12,6,14,22,24,16,37,38,39,33,9,40]),([5,7,1,2,3,4],[43,21,0,4,1,15,34,7,39],[12,6,14,7,0,4,22,28]),([8,0,1,2,3,4],[14,0,4,1,39,10,2,17,19],[0,4,1,27]),([9,5,0,1,2,3,4],[21,0,7,1,6,29,22,24,44,45,39],[0,4,1,27]),([9,0,1,2,3,4],[0,7,1,10,22,2,24,44,45,39],[0,4,1,27,2,31])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_47_7 : checkNodes W_47 G_47 fmask_47 P_47 autos_47 bk_47_6 7 nodes_47_7 = true := by decide +kernel
def bk_47_7 : Array (List (List Nat)) := buildBuckets 2 W_47 nodes_47_7
lemma bk_47_7_ok : ∀ i (hi : i < bk_47_7.size), ∀ xs ∈ bk_47_7[i], Impossible G_47 7 xs.toFinset :=
  buildBuckets_sound (by decide) gp_47 W_47_ok P_47_ok autos_47_ok bk_47_6_ok chk_47_7
def nodes_47_8 : List NodeSpec := [([5,0,1,2,3,4],[14,4,21,1,39,10,40,2,46],[0,12,6,1,30,33,11])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_47_8 : checkNodes W_47 G_47 fmask_47 P_47 autos_47 bk_47_7 8 nodes_47_8 = true := by decide +kernel
def bk_47_8 : Array (List (List Nat)) := buildBuckets 1 W_47 nodes_47_8
lemma bk_47_8_ok : ∀ i (hi : i < bk_47_8.size), ∀ xs ∈ bk_47_8[i], Impossible G_47 8 xs.toFinset :=
  buildBuckets_sound (by decide) gp_47 W_47_ok P_47_ok autos_47_ok bk_47_7_ok chk_47_8
def nodes_47_9 : List NodeSpec := [([0,1,2,3,4],[4,14,21,10,2],[0,22,24,19,38,39,41,36,42,43])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_47_9 : checkNodes W_47 G_47 fmask_47 P_47 autos_47 bk_47_8 9 nodes_47_9 = true := by decide +kernel
def bk_47_9 : Array (List (List Nat)) := buildBuckets 1 W_47 nodes_47_9
lemma bk_47_9_ok : ∀ i (hi : i < bk_47_9.size), ∀ xs ∈ bk_47_9[i], Impossible G_47 9 xs.toFinset :=
  buildBuckets_sound (by decide) gp_47 W_47_ok P_47_ok autos_47_ok bk_47_8_ok chk_47_9
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_47_ok : forestRootCheck R_47 G_47 [(VAR 1,30,28),(VAR 2,30,26),(VAR 3,30,22),(VAR 4,30,14),(VAR 5,46,14)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_47_in : bucketContains bk_47_9 R_47 = true := by decide +kernel
lemma low_47 : Lower R_47 G_47 10 := lower_of_forest root_47_ok bk_47_9_ok root_47_in
def G_48 : Nat := 0xfefee8e8e8e80000fefee8e8e8e80000
def R_48 : List Nat := varsOf 55
def pos_48 : List Nat := [19,19,19,21,21,21,22,22,22,23,35,35,35,37,37,37,38,38,38,39,49,49,49,50,50,50,52,52,52,19,19,19,19,19,19,21,21,21,21,21,21,22,22,22,22,22,22,35,35,35,35,35,35,37,37,37,37,37,37,38,38,38,38,38,38,49,49,49,49,49,50,50,50,50,50,52,52,52,52,52]
def neg_48 : List Nat := [18,17,3,20,17,5,20,18,6,7,34,33,3,36,33,5,36,34,6,7,48,33,17,48,34,18,48,36,20,7,20,33,34,36,48,7,18,33,34,36,48,7,17,33,34,36,48,7,17,18,20,36,48,7,17,18,20,34,48,7,17,18,20,33,48,7,18,20,34,36,7,17,20,33,36,7,17,18,33,34]
def fmask_48 : Nat := fullMask 80
def base_48 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3e07ff81ffe078fe3f,0x5ac298618e28a068da36),(0xcccccccccccccccccccccccccccccccc,0x7c1f81ffe07e38f1fc7,0xa8562aa29259230e1785),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf801ffe07ff81c0fe3f8,0xd6a492ca28a780da368),(0xffff0000ffff0000ffff0000ffff0000,0xfffe00007ffffff003ff,0x318d75d7451456d000db),(0xffffffff00000000ffffffff00000000,0xffffffff80001ffffc00,0xc631861879e78db36c00)]
def steps_48 : List (Nat × Nat × Nat) := [(0,3,4),(3,0,3),(1,0,1),(1,0,5),(3,1,4),(3,0,4),(3,6,4),(1,6,1),(0,6,4),(3,7,3),(0,7,3),(3,2,3),(1,0,2),(2,7,2),(1,7,2),(3,1,8),(1,1,5),(2,7,5),(1,7,5),(0,19,3),(0,7,4),(0,15,4),(3,16,4),(3,15,4),(1,1,2),(3,2,23),(2,19,5)]
def W_48 : Array Decor := buildWires base_48 steps_48
def autos_48 : Array (List (Nat × Nat)) := #[[],[(1,2)],[(0,1),(0,2)],[(0,1)],[(4,5)],[(0,2),(0,1)],[(4,5),(0,1)],[(4,5),(0,2),(0,1)]]
def slicesL_48 : List (Nat × Nat) := [(subcube 32 0,5),(subcube 0 16,7),(subcube 1 32,4),(subcube 2 0,7),(subcube 0 1,5),(subcube 0 2,5),(subcube 0 32,7),(subcube 4 0,7),(subcube 4 16,4),(subcube 4 2,4),(subcube 4 1,4),(subcube 2 1,4),(subcube 2 16,4),(subcube 1 0,7),(subcube 0 4,5),(subcube 16 0,5),(subcube 1 4,4),(subcube 16 32,4),(subcube 1 16,4),(subcube 32 16,4),(subcube 2 4,4)]
def slices_48 : Array (Nat × Nat) := slicesL_48.toArray
def ps_48 : List PoolSpec := [(0,[]),(1,[(1,0,1),(1,0,5),(1,1,5)]),(2,[]),(1,[(1,0,1),(1,7,5),(3,2,23)]),(3,[(0,7,3),(0,7,4),(0,3,4)]),(4,[]),(5,[]),(1,[]),(6,[]),(1,[(1,0,1),(1,7,2),(2,19,5)]),(7,[]),(8,[]),(9,[]),(10,[]),(1,[(1,0,1),(1,0,2),(1,1,2)]),(11,[]),(1,[(1,0,5),(3,1,8)]),(12,[]),(1,[(1,0,5),(1,1,5)]),(13,[]),(3,[]),(14,[]),(13,[(0,3,4),(2,7,5)]),(3,[(0,3,4),(2,7,5)]),(1,[(1,0,1),(1,7,5)]),(15,[]),(1,[(1,0,1),(1,0,5)]),(3,[(0,7,3),(0,7,4)]),(3,[(0,7,3),(0,15,4)]),(16,[]),(17,[]),(1,[(1,0,1),(2,7,2)]),(1,[(1,0,1),(1,7,2)]),(3,[(0,7,3),(0,3,4)]),(1,[(1,0,1),(1,0,2)]),(1,[(1,0,1),(2,7,5)]),(3,[(0,7,3),(3,15,4)]),(6,[(1,0,1),(1,0,2),(1,1,2)]),(13,[(0,3,4)]),(1,[(1,0,5)]),(18,[]),(19,[]),(20,[]),(3,[(0,3,4)]),(1,[(1,0,1)]),(6,[(1,0,1)]),(3,[(0,7,3)]),(6,[(1,0,1),(1,0,2)]),(6,[(1,0,1),(2,7,2)]),(6,[(1,0,1),(1,7,2)]),(7,[(0,3,4)])]
def P_48 : Array (Option BoundPool) := buildPools W_48 R_48 slices_48 ps_48
lemma gp_48 : goodPairs G_48 pos_48 neg_48 := goodPairs_of (by decide +kernel)
lemma base_48_ok : ∀ x ∈ base_48, faithful pos_48 neg_48 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_48_ok : ∀ x ∈ W_48.toList, faithful pos_48 neg_48 x ∧ x.1 < 2^128 := buildWires_faithful base_48_ok
lemma autos_48_ok : ∀ sw ∈ autos_48.toList, swapsValid sw = true ∧ permWord sw G_48 = G_48 := autos_of (by decide +kernel)
lemma sl_48_0_ok : sliceDirectCheck 32 0 0 R_48 G_48 R_24 G_24 = true := by decide +kernel
lemma sl_48_0 : Slice R_48 G_48 (subcube 32 0) 5 := slice_direct sl_48_0_ok low_24
lemma sl_48_1_ok : sliceDirectCheck 0 16 0 R_48 G_48 R_20 G_20 = true := by decide +kernel
lemma sl_48_1 : Slice R_48 G_48 (subcube 0 16) 7 := slice_direct sl_48_1_ok low_20
lemma sl_48_2_ok : sliceDirectCheck 1 32 0 R_48 G_48 R_8 G_8 = true := by decide +kernel
lemma sl_48_2 : Slice R_48 G_48 (subcube 1 32) 4 := slice_direct sl_48_2_ok low_8
lemma sl_48_3_ok : sliceDirectCheck 2 0 0 R_48 G_48 R_30 G_30 = true := by decide +kernel
lemma sl_48_3 : Slice R_48 G_48 (subcube 2 0) 7 := slice_direct sl_48_3_ok low_30
lemma sl_48_4_ok : sliceDirectCheck 0 1 0 R_48 G_48 R_22 G_22 = true := by decide +kernel
lemma sl_48_4 : Slice R_48 G_48 (subcube 0 1) 5 := slice_direct sl_48_4_ok low_22
lemma sl_48_5_ok : sliceDirectCheck 0 2 0 R_48 G_48 R_45 G_45 = true := by decide +kernel
lemma sl_48_5 : Slice R_48 G_48 (subcube 0 2) 5 := slice_direct sl_48_5_ok low_45
lemma sl_48_6_ok : sliceDirectCheck 0 32 0 R_48 G_48 R_35 G_35 = true := by decide +kernel
lemma sl_48_6 : Slice R_48 G_48 (subcube 0 32) 7 := slice_direct sl_48_6_ok low_35
lemma sl_48_7_ok : sliceDirectCheck 4 0 0 R_48 G_48 R_27 G_27 = true := by decide +kernel
lemma sl_48_7 : Slice R_48 G_48 (subcube 4 0) 7 := slice_direct sl_48_7_ok low_27
lemma sl_48_8_ok : sliceDirectCheck 4 16 0 R_48 G_48 R_3 G_3 = true := by decide +kernel
lemma sl_48_8 : Slice R_48 G_48 (subcube 4 16) 4 := slice_direct sl_48_8_ok low_3
lemma sl_48_9_ok : sliceDirectCheck 4 2 0 R_48 G_48 R_16 G_16 = true := by decide +kernel
lemma sl_48_9 : Slice R_48 G_48 (subcube 4 2) 4 := slice_direct sl_48_9_ok low_16
lemma sl_48_10_ok : sliceDirectCheck 4 1 0 R_48 G_48 R_17 G_17 = true := by decide +kernel
lemma sl_48_10 : Slice R_48 G_48 (subcube 4 1) 4 := slice_direct sl_48_10_ok low_17
lemma sl_48_11_ok : sliceDirectCheck 2 1 0 R_48 G_48 R_18 G_18 = true := by decide +kernel
lemma sl_48_11 : Slice R_48 G_48 (subcube 2 1) 4 := slice_direct sl_48_11_ok low_18
lemma sl_48_12_ok : sliceDirectCheck 2 16 0 R_48 G_48 R_6 G_6 = true := by decide +kernel
lemma sl_48_12 : Slice R_48 G_48 (subcube 2 16) 4 := slice_direct sl_48_12_ok low_6
lemma sl_48_13_ok : sliceDirectCheck 1 0 0 R_48 G_48 R_33 G_33 = true := by decide +kernel
lemma sl_48_13 : Slice R_48 G_48 (subcube 1 0) 7 := slice_direct sl_48_13_ok low_33
lemma sl_48_14_ok : sliceDirectCheck 0 4 0 R_48 G_48 R_44 G_44 = true := by decide +kernel
lemma sl_48_14 : Slice R_48 G_48 (subcube 0 4) 5 := slice_direct sl_48_14_ok low_44
lemma sl_48_15_ok : sliceDirectCheck 16 0 0 R_48 G_48 R_19 G_19 = true := by decide +kernel
lemma sl_48_15 : Slice R_48 G_48 (subcube 16 0) 5 := slice_direct sl_48_15_ok low_19
lemma sl_48_16_ok : sliceDirectCheck 1 4 0 R_48 G_48 R_17 G_17 = true := by decide +kernel
lemma sl_48_16 : Slice R_48 G_48 (subcube 1 4) 4 := slice_direct sl_48_16_ok low_17
lemma sl_48_17_ok : sliceDirectCheck 16 32 0 R_48 G_48 R_1 G_1 = true := by decide +kernel
lemma sl_48_17 : Slice R_48 G_48 (subcube 16 32) 4 := slice_direct sl_48_17_ok low_1
lemma sl_48_18_ok : sliceDirectCheck 1 16 0 R_48 G_48 R_9 G_9 = true := by decide +kernel
lemma sl_48_18 : Slice R_48 G_48 (subcube 1 16) 4 := slice_direct sl_48_18_ok low_9
lemma sl_48_19_ok : sliceDirectCheck 32 16 0 R_48 G_48 R_1 G_1 = true := by decide +kernel
lemma sl_48_19 : Slice R_48 G_48 (subcube 32 16) 4 := slice_direct sl_48_19_ok low_1
lemma sl_48_20_ok : sliceDirectCheck 2 4 0 R_48 G_48 R_16 G_16 = true := by decide +kernel
lemma sl_48_20 : Slice R_48 G_48 (subcube 2 4) 4 := slice_direct sl_48_20_ok low_16
set_option maxRecDepth 200000 in
lemma slices_48_ok : ∀ i (hi : i < slices_48.size), Slice R_48 G_48 slices_48[i].1 slices_48[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_48 G_48 p.1 p.2) (forall_cons sl_48_0 (forall_cons sl_48_1 (forall_cons sl_48_2 (forall_cons sl_48_3 (forall_cons sl_48_4 (forall_cons sl_48_5 (forall_cons sl_48_6 (forall_cons sl_48_7 (forall_cons sl_48_8 (forall_cons sl_48_9 (forall_cons sl_48_10 (forall_cons sl_48_11 (forall_cons sl_48_12 (forall_cons sl_48_13 (forall_cons sl_48_14 (forall_cons sl_48_15 (forall_cons sl_48_16 (forall_cons sl_48_17 (forall_cons sl_48_18 (forall_cons sl_48_19 (forall_cons sl_48_20 (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))
lemma P_48_ok : ∀ i (hi : i < P_48.size), ∀ c, P_48[i] = some c → ValidPool R_48 G_48 c := buildPools_sound slices_48_ok
def bk_48_init : Array (List (List Nat)) := #[]
lemma bk_48_init_ok : ∀ i (hi : i < bk_48_init.size), ∀ xs ∈ bk_48_init[i], Impossible G_48 (0 - 1) xs.toFinset := by intro i hi; simp [bk_48_init] at hi
def nodes_48_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_48_0 : checkNodes W_48 G_48 fmask_48 P_48 autos_48 bk_48_init 0 nodes_48_0 = true := by decide +kernel
def bk_48_0 : Array (List (List Nat)) := buildBuckets 1 W_48 nodes_48_0
lemma bk_48_0_ok : ∀ i (hi : i < bk_48_0.size), ∀ xs ∈ bk_48_0[i], Impossible G_48 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_48 W_48_ok P_48_ok autos_48_ok bk_48_init_ok chk_48_0
def nodes_48_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_48_1 : checkNodes W_48 G_48 fmask_48 P_48 autos_48 bk_48_0 1 nodes_48_1 = true := by decide +kernel
def bk_48_1 : Array (List (List Nat)) := buildBuckets 1 W_48 nodes_48_1
lemma bk_48_1_ok : ∀ i (hi : i < bk_48_1.size), ∀ xs ∈ bk_48_1[i], Impossible G_48 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_48 W_48_ok P_48_ok autos_48_ok bk_48_0_ok chk_48_1
def nodes_48_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_48_2 : checkNodes W_48 G_48 fmask_48 P_48 autos_48 bk_48_1 2 nodes_48_2 = true := by decide +kernel
def bk_48_2 : Array (List (List Nat)) := buildBuckets 1 W_48 nodes_48_2
lemma bk_48_2_ok : ∀ i (hi : i < bk_48_2.size), ∀ xs ∈ bk_48_2[i], Impossible G_48 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_48 W_48_ok P_48_ok autos_48_ok bk_48_1_ok chk_48_2
def nodes_48_3 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_48_3 : checkNodes W_48 G_48 fmask_48 P_48 autos_48 bk_48_2 3 nodes_48_3 = true := by decide +kernel
def bk_48_3 : Array (List (List Nat)) := buildBuckets 1 W_48 nodes_48_3
lemma bk_48_3_ok : ∀ i (hi : i < bk_48_3.size), ∀ xs ∈ bk_48_3[i], Impossible G_48 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_48 W_48_ok P_48_ok autos_48_ok bk_48_2_ok chk_48_3
def nodes_48_4 : List NodeSpec := [([22,17,29,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_48_4 : checkNodes W_48 G_48 fmask_48 P_48 autos_48 bk_48_3 4 nodes_48_4 = true := by decide +kernel
def bk_48_4 : Array (List (List Nat)) := buildBuckets 1 W_48 nodes_48_4
lemma bk_48_4_ok : ∀ i (hi : i < bk_48_4.size), ∀ xs ∈ bk_48_4[i], Impossible G_48 4 xs.toFinset :=
  buildBuckets_sound (by decide) gp_48 W_48_ok P_48_ok autos_48_ok bk_48_3_ok chk_48_4
def nodes_48_5 : List NodeSpec := [([7,2,3,8,21,4],[0,1,2],[]),([30,0,1,5,3,4],[3],[]),([0,1,15,25,2,5],[4,5,6,2],[]),([22,0,1,2,3,4],[],[]),([31,0,1,2,3,4],[7,8,9],[]),([22,1,2,17,3,4],[10],[0]),([7,17,29,5,3,4],[11,12,2,13,14],[0,1,2])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_48_5 : checkNodes W_48 G_48 fmask_48 P_48 autos_48 bk_48_4 5 nodes_48_5 = true := by decide +kernel
def bk_48_5 : Array (List (List Nat)) := buildBuckets 3 W_48 nodes_48_5
lemma bk_48_5_ok : ∀ i (hi : i < bk_48_5.size), ∀ xs ∈ bk_48_5[i], Impossible G_48 5 xs.toFinset :=
  buildBuckets_sound (by decide) gp_48 W_48_ok P_48_ok autos_48_ok bk_48_4_ok chk_48_5
def nodes_48_6 : List NodeSpec := [([20,0,1,2,5,3,4],[0,2,6,15,16],[]),([0,1,2,3,8,21,4],[2,5,17,6,18],[0]),([22,0,1,2,3,4],[19,20,10,21,8,7,22,23],[0,3]),([0,1,2,5,3,23,4],[11,8,24],[0]),([0,1,2,24,4],[5,21,6,25],[]),([1,7,2,5,3,8,4],[15,17,0,25,19,26],[0]),([0,1,15,25,2,3,4],[27,0,2,17,25],[0]),([0,1,26,7,2,3,4],[28,19,29,12],[0]),([0,1,7,2,27,3,4],[29,11,5,30,0],[]),([18,0,1,2,5,3,4],[21,12,5,29,15,31],[]),([0,1,2,19,5,3,4],[5,29,6,15,12,0,25,7,8,32],[0]),([22,0,1,7,2,3,4],[19,20,0,23],[]),([0,1,15,7,2,5,4],[33,5,6,7,2,30],[0]),([1,7,2,17,5,3,4],[17,12,15,11,29,34],[0,1]),([22,0,1,2,5,3,4],[5,8,7,35],[]),([28,0,1,7,2,3,4],[7,8,5,17,36,0,30],[]),([7,17,29,3,4],[20,10,12,19,13,14,37],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_48_6 : checkNodes W_48 G_48 fmask_48 P_48 autos_48 bk_48_5 6 nodes_48_6 = true := by decide +kernel
def bk_48_6 : Array (List (List Nat)) := buildBuckets 6 W_48 nodes_48_6
lemma bk_48_6_ok : ∀ i (hi : i < bk_48_6.size), ∀ xs ∈ bk_48_6[i], Impossible G_48 6 xs.toFinset :=
  buildBuckets_sound (by decide) gp_48 W_48_ok P_48_ok autos_48_ok bk_48_5_ok chk_48_6
def nodes_48_7 : List NodeSpec := [([0,1,2,5,3,8,4],[38,5,0,25,15,17,13,11,39],[0,1]),([0,1,2,3,8,4],[5,15,13,25,0,7,2],[]),([9,6,0,1,2,3,4],[5,0,40,41,2,29,11,20,6,12,42,30],[]),([6,10,1,2,3,4],[5,7,19,8,13,30],[]),([0,11,1,2,3,4],[8,0,7,2,5,6,20,21,10,19,13,15,30],[2]),([0,1,12,2,3,4],[6,5,20,12,25,17,40,0,8],[]),([0,1,7,2,5,3,4],[43,2,38,5,6,11,0,25,7,44,8,45,12,29],[0,3,4]),([13,0,1,2,3,4],[5,6,20,21,10,25,0,13],[]),([14,0,1,2,3,4],[5,6,21,10,25,8,0,12],[]),([0,1,15,7,2,3,4],[46,5,12,7,17,2,30,44],[0]),([0,1,15,2,3,4],[17,5,6,7,25,12,40,21,8,0,30],[]),([16,0,1,7,2,3,4],[19,5,20,6,21,12,11,17,29,2,25,41,30],[0]),([1,7,2,17,3,4],[19,12,20,5,10,34,47],[0]),([18,0,1,2,3,4],[10,21,20,19,7,25,8,0,12,13,31,48],[0]),([0,1,2,19,3,4],[5,21,6,25,7,0,8,32,49],[0,4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_48_7 : checkNodes W_48 G_48 fmask_48 P_48 autos_48 bk_48_6 7 nodes_48_7 = true := by decide +kernel
def bk_48_7 : Array (List (List Nat)) := buildBuckets 6 W_48 nodes_48_7
lemma bk_48_7_ok : ∀ i (hi : i < bk_48_7.size), ∀ xs ∈ bk_48_7[i], Impossible G_48 7 xs.toFinset :=
  buildBuckets_sound (by decide) gp_48 W_48_ok P_48_ok autos_48_ok bk_48_6_ok chk_48_7
def nodes_48_8 : List NodeSpec := [([0,1,2,5,3,4],[43,38,50,0,7,8],[0,1,2,5]),([6,0,1,2,3,4],[7,20,5,40,10,19,8,13,15,30],[0,1,2]),([0,1,7,2,3,4],[20,19,10,12,7,44,8,45],[0,3,4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_48_8 : checkNodes W_48 G_48 fmask_48 P_48 autos_48 bk_48_7 8 nodes_48_8 = true := by decide +kernel
def bk_48_8 : Array (List (List Nat)) := buildBuckets 2 W_48 nodes_48_8
lemma bk_48_8_ok : ∀ i (hi : i < bk_48_8.size), ∀ xs ∈ bk_48_8[i], Impossible G_48 8 xs.toFinset :=
  buildBuckets_sound (by decide) gp_48 W_48_ok P_48_ok autos_48_ok bk_48_7_ok chk_48_8
def nodes_48_9 : List NodeSpec := [([0,1,2,3,4],[20,19,10,7,8],[0,1,4,2,6,5,7])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_48_9 : checkNodes W_48 G_48 fmask_48 P_48 autos_48 bk_48_8 9 nodes_48_9 = true := by decide +kernel
def bk_48_9 : Array (List (List Nat)) := buildBuckets 1 W_48 nodes_48_9
lemma bk_48_9_ok : ∀ i (hi : i < bk_48_9.size), ∀ xs ∈ bk_48_9[i], Impossible G_48 9 xs.toFinset :=
  buildBuckets_sound (by decide) gp_48 W_48_ok P_48_ok autos_48_ok bk_48_8_ok chk_48_9
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_48_ok : forestRootCheck R_48 G_48 [(VAR 0,19,18),(VAR 1,19,17),(VAR 2,21,17),(VAR 4,19,3),(VAR 5,35,3)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_48_in : bucketContains bk_48_9 R_48 = true := by decide +kernel
lemma low_48 : Lower R_48 G_48 10 := lower_of_forest root_48_ok bk_48_9_ok root_48_in
def G_49 : Nat := 0xfffcfc00fc000000fffcfc00fc000000
def R_49 : List Nat := varsOf 62
lemma low_49_ok : liftCheck 2 0 R_49 G_49 R_21 G_21 [(VAR 1,26,24)] = true := by decide +kernel
lemma low_49 : Lower R_49 G_49 8 := lift_of low_49_ok low_21
def G_50 : Nat := 0xe8000000e8000000e8000000e8000000
def R_50 : List Nat := varsOf 31
lemma low_50_ok : carryOK [(3,5),(3,4)] R_50 G_50 R_46 G_46 = true := by decide +kernel
lemma low_50 : Lower R_50 G_50 6 := carry_of low_50_ok low_46
def G_51 : Nat := 0xe800e80000000000e800e80000000000
def R_51 : List Nat := varsOf 47
lemma low_51_ok : carryOK [(3,4)] R_51 G_51 R_46 G_46 = true := by decide +kernel
lemma low_51 : Lower R_51 G_51 6 := carry_of low_51_ok low_46
def G_52 : Nat := 0xee88880088000000ee88880088000000
def R_52 : List Nat := varsOf 59
lemma low_52_ok : carryOK [(0,2),(0,1)] R_52 G_52 R_47 G_47 = true := by decide +kernel
lemma low_52 : Lower R_52 G_52 10 := carry_of low_52_ok low_47
def G_53 : Nat := 0xfaa0a000a0000000faa0a000a0000000
def R_53 : List Nat := varsOf 61
lemma low_53_ok : carryOK [(0,1)] R_53 G_53 R_47 G_47 = true := by decide +kernel
lemma low_53 : Lower R_53 G_53 10 := carry_of low_53_ok low_47
def G_54 : Nat := 0xfee8e800fee8e800fee8e800fee8e800
def R_54 : List Nat := varsOf 31
lemma low_54_ok : carryOK [(3,5),(3,4)] R_54 G_54 R_48 G_48 = true := by decide +kernel
lemma low_54 : Lower R_54 G_54 10 := carry_of low_54_ok low_48
def G_55 : Nat := 0xfee8fee8e800e800fee8fee8e800e800
def R_55 : List Nat := varsOf 47
lemma low_55_ok : carryOK [(3,4)] R_55 G_55 R_48 G_48 = true := by decide +kernel
lemma low_55 : Lower R_55 G_55 10 := carry_of low_55_ok low_48
def G_56 : Nat := 0xffeeee00ee000000ffeeee00ee000000
def R_56 : List Nat := varsOf 59
lemma low_56_ok : carryOK [(0,2),(0,1)] R_56 G_56 R_49 G_49 = true := by decide +kernel
lemma low_56 : Lower R_56 G_56 8 := carry_of low_56_ok low_49
def G_57 : Nat := 0xfffafa00fa000000fffafa00fa000000
def R_57 : List Nat := varsOf 61
lemma low_57_ok : carryOK [(0,1)] R_57 G_57 R_49 G_49 = true := by decide +kernel
lemma low_57 : Lower R_57 G_57 8 := carry_of low_57_ok low_49
def G_58 : Nat := 0xfee8e800e8000000fee8e800e8000000
def R_58 : List Nat := varsOf 63
def pos_58 : List Nat := [27,27,27,27,29,29,29,29,30,30,30,30,31,31,43,43,43,43,45,45,45,45,46,46,46,46,47,47,51,51,51,51,53,53,53,53,54,54,54,54,55,55,57,57,57,57,58,58,58,58,60,60,60,60,27,27,27,27,27,27,27,27,27,27,27,29,29,29,29,29,29,29,29,29,29,29,30,30,30,30,30,30,30,30,30,30,30,43,43,43,43,43,43,43,43,43,43,43,45,45,45,45,45,45,45,45,45,45,45,46,46,46,46,46,46,46,46,46,46,46,51,51,51,51,51,51,51,51]
def neg_58 : List Nat := [26,25,19,11,28,25,21,13,28,26,22,14,23,15,42,41,35,11,44,41,37,13,44,42,38,14,39,15,50,49,35,19,52,49,37,21,52,50,38,22,39,23,56,49,41,25,56,50,42,26,56,52,44,28,15,23,28,39,41,42,44,49,50,52,56,15,23,26,39,41,42,44,49,50,52,56,15,23,25,39,41,42,44,49,50,52,56,15,23,25,26,28,39,44,49,50,52,56,15,23,25,26,28,39,42,49,50,52,56,15,23,25,26,28,39,41,49,50,52,56,15,23,25,26,28,39,41,42]
def fmask_58 : Nat := fullMask 128
def base_58 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff001fffff800fffffc03f0ffc3ff0ff,0x671ce29c5389f13626c03b0eec3bb0ee),(0xcccccccccccccccccccccccccccccccc,0xffffe003fffff001ffc3c3f0ffc3ff0f,0xab2565ac9592b25e4ac383e0df837e0d),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffc007ffffe003c03ff0ffc3ff0,0x334668cd39a4b49693f803dd0f743dd0),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfffffffffffffffffffc000fffffff,0xdd8bb1762ec758eb1d7774000aeeebbb),(0xffff0000ffff0000ffff0000ffff0000,0xff000000007ffffffffffffff0003fff,0x1ef3de7bcf786f0de1aeeebbb0001777),(0xffffffff00000000ffffffff00000000,0xffffffffff800000003fffffffffc000,0xe0fc1f83f07f8ff1fe1ddd7775ddc000)]
def steps_58 : List (Nat × Nat × Nat) := [(3,0,3),(0,3,4),(1,0,1),(3,7,5),(0,7,5),(1,0,7),(3,1,4),(3,6,4),(3,0,7),(1,6,1),(0,3,5),(3,2,3),(0,8,3),(2,8,2),(3,8,3),(0,4,5),(3,0,4),(1,8,2),(1,0,2),(1,0,10),(3,0,10),(1,1,2),(3,1,7),(3,14,5),(3,0,21),(1,14,1),(3,13,5),(0,11,5),(3,8,7),(2,18,2),(3,18,4),(2,8,7),(0,8,7),(3,2,7),(3,1,21),(3,1,5),(3,17,4),(0,8,4),(3,6,21),(3,20,4),(0,23,3),(1,18,2),(3,0,5),(3,2,4),(1,26,1),(1,1,10),(3,44,4),(3,26,4),(3,9,8),(2,18,21),(0,38,5),(2,8,10),(3,2,10),(3,2,5),(1,8,10),(3,34,3),(3,37,5),(3,42,5),(2,8,42),(0,46,4),(0,8,21),(3,38,3),(3,38,5),(0,8,5),(3,49,3),(1,38,2),(3,36,5),(0,18,5),(3,1,25),(3,49,5),(0,47,4),(0,36,5),(3,45,5),(3,46,4),(3,39,5),(1,2,10),(0,45,5),(3,17,21),(3,2,60),(1,56,2),(3,58,8),(2,57,2),(3,77,4),(3,55,3),(2,23,10),(1,57,2),(3,55,8),(3,56,4),(3,56,3),(0,8,81),(0,91,3)]
def W_58 : Array Decor := buildWires base_58 steps_58
def autos_58 : Array (List (Nat × Nat)) := #[[],[(3,4),(3,5)],[(4,5)],[(3,4)],[(3,5),(3,4)],[(1,2)],[(0,1),(0,2)],[(0,1)],[(3,5)],[(4,5),(0,1)],[(3,4),(3,5),(0,1)],[(0,2),(0,1)],[(4,5),(0,2),(0,1)],[(3,4),(3,5),(0,2),(0,1)],[(3,5),(3,4),(0,1)],[(3,5),(3,4),(0,2),(0,1)],[(4,5),(1,2)],[(3,4),(0,1)],[(3,4),(0,2),(0,1)]]
def slicesL_58 : List (Nat × Nat) := [(subcube 0 4,8),(subcube 2 0,10),(subcube 4 48,4),(subcube 1 0,10),(subcube 0 1,8),(subcube 1 20,4),(subcube 2 36,4),(subcube 1 10,4),(subcube 1 4,7),(subcube 2 4,7),(subcube 4 1,7),(subcube 0 8,10),(subcube 1 24,4),(subcube 8 16,5),(subcube 32 8,5),(subcube 0 33,5),(subcube 0 48,7),(subcube 0 40,7),(subcube 0 32,10),(subcube 0 24,7),(subcube 2 1,7),(subcube 0 2,8),(subcube 0 5,4),(subcube 0 6,4),(subcube 8 0,6),(subcube 16 0,6),(subcube 32 16,5),(subcube 16 32,5),(subcube 4 0,10),(subcube 32 0,6),(subcube 1 2,7),(subcube 4 24,4),(subcube 4 18,4),(subcube 4 9,4),(subcube 16 40,4),(subcube 8 48,4),(subcube 32 24,4),(subcube 0 18,5),(subcube 0 9,5),(subcube 2 32,7),(subcube 1 16,7),(subcube 0 16,10),(subcube 16 8,5),(subcube 2 48,4),(subcube 2 40,4),(subcube 2 24,4),(subcube 8 32,5),(subcube 1 48,4),(subcube 0 20,5),(subcube 0 36,5),(subcube 0 12,5),(subcube 1 32,7),(subcube 1 8,7),(subcube 0 17,5),(subcube 2 8,7),(subcube 0 34,5),(subcube 4 8,7),(subcube 4 33,4),(subcube 4 17,4),(subcube 1 6,4),(subcube 4 32,7),(subcube 2 9,4),(subcube 0 7,4),(subcube 4 10,4),(subcube 4 2,7),(subcube 2 12,4),(subcube 1 18,4),(subcube 0 10,5),(subcube 4 16,7),(subcube 2 20,4),(subcube 2 17,4),(subcube 1 40,4),(subcube 2 33,4),(subcube 1 12,4),(subcube 2 16,7),(subcube 4 3,4)]
def slices_58 : Array (Nat × Nat) := slicesL_58.toArray
def ps_58 : List PoolSpec := [(0,[]),(1,[(0,8,3),(0,18,4),(0,38,5),(1,56,2),(3,56,3)]),(1,[(0,8,3),(0,18,4),(0,38,5),(3,56,8),(3,56,3)]),(1,[(0,3,4),(0,3,5),(0,4,5)]),(1,[(1,0,2),(0,3,4),(0,3,5),(0,4,5)]),(2,[]),(3,[(0,3,4),(0,3,5),(0,4,5)]),(3,[(1,1,2),(0,3,4),(0,3,5),(0,4,5)]),(4,[(1,1,2),(0,3,4),(0,3,5),(0,4,5)]),(0,[(1,0,1),(0,3,4),(0,3,5),(0,4,5)]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(1,[(0,8,3),(0,18,4),(0,38,5),(3,56,8),(1,56,2)]),(10,[]),(1,[(0,8,3),(0,18,4),(0,38,5),(3,56,3),(3,56,4)]),(11,[(1,0,1),(1,0,2),(1,1,2),(0,7,5),(2,8,10)]),(1,[(1,0,2),(0,3,4),(0,7,5),(2,8,10)]),(0,[(1,0,1),(0,3,4),(0,7,5),(2,8,10)]),(12,[]),(13,[]),(0,[(0,3,4),(0,3,5),(0,4,5)]),(14,[]),(15,[]),(16,[(1,0,1),(1,8,10),(3,2,60)]),(17,[(1,0,1),(1,8,10),(3,2,60)]),(18,[(1,0,1),(0,3,4),(1,8,10),(3,2,60)]),(19,[(1,0,1),(1,8,10),(3,2,60)]),(11,[(1,0,1),(0,7,5),(1,8,10),(3,2,60)]),(9,[(0,3,4),(0,7,5),(2,8,10)]),(8,[(0,3,4),(0,7,5),(2,8,10)]),(20,[]),(21,[]),(1,[(0,3,4),(0,7,5),(0,8,10),(1,56,2)]),(22,[]),(23,[]),(24,[]),(25,[]),(26,[]),(27,[]),(28,[]),(4,[]),(28,[(1,0,1),(0,3,4),(0,7,5),(3,58,8)]),(17,[]),(16,[]),(29,[]),(19,[]),(28,[(1,0,1),(0,3,4),(0,7,5),(2,8,10)]),(16,[(1,0,1),(1,0,10),(1,1,10)]),(30,[]),(17,[(1,0,1),(1,0,10),(1,1,10)]),(19,[(1,0,1),(1,0,10),(1,1,10)]),(1,[(0,3,4),(0,7,5),(1,0,10)]),(31,[]),(32,[]),(33,[]),(1,[(0,3,4),(3,2,7),(0,3,5),(0,4,5)]),(34,[]),(35,[]),(28,[(1,0,1),(0,3,4),(0,3,5),(0,4,5)]),(1,[(0,3,4),(3,2,7),(3,39,5),(0,7,5)]),(0,[(0,3,4),(0,7,5)]),(19,[(1,0,1)]),(4,[(0,3,4),(0,3,5),(0,4,5)]),(1,[(0,3,4),(2,8,7),(0,3,5),(0,4,5)]),(3,[(0,3,4),(2,8,7),(0,3,5),(0,4,5)]),(21,[(0,3,4),(0,3,5),(0,4,5)]),(10,[(0,3,4),(0,3,5),(0,4,5)]),(36,[]),(17,[(1,0,1),(2,8,7)]),(16,[(1,0,1),(2,8,7)]),(18,[]),(18,[(1,0,1),(0,3,4),(2,8,10)]),(1,[(0,3,4),(0,8,7),(0,3,5),(0,4,5)]),(37,[]),(38,[]),(39,[]),(1,[(0,3,4),(0,8,7),(3,38,5),(0,3,5)]),(1,[(0,8,3),(0,4,5),(3,18,21),(3,77,4)]),(40,[]),(1,[(0,8,3),(0,4,5),(2,18,21),(3,55,3)]),(11,[(1,0,1),(0,4,5),(2,18,21)]),(11,[]),(41,[(1,0,1),(0,8,3),(0,18,21),(3,56,8)]),(42,[]),(43,[]),(41,[(1,0,1),(0,8,3),(0,8,5),(0,3,5)]),(1,[(0,8,3),(3,18,4),(0,8,5),(0,3,5)]),(1,[(0,8,3),(0,3,4),(0,4,5),(0,8,21)]),(18,[(1,0,1),(0,8,3),(0,8,4),(0,3,4)]),(1,[(0,8,3),(0,8,4),(0,3,4),(3,7,5)]),(4,[(0,3,4),(3,7,5)]),(3,[(0,8,3),(0,8,4),(0,3,4),(3,7,5)]),(21,[(0,3,4),(3,7,5)]),(1,[(0,8,3),(0,8,4),(0,3,4),(0,7,5)]),(3,[(0,8,3),(0,8,4),(0,3,4),(0,7,5)]),(4,[(0,3,4),(0,7,5)]),(21,[(0,3,4),(0,7,5)]),(44,[]),(1,[(0,8,3),(0,18,4),(0,8,5),(0,4,5)]),(1,[(0,8,3),(0,18,4),(0,3,5),(0,4,5)]),(1,[(0,8,3),(0,8,4),(0,3,5),(0,4,5)]),(3,[(0,8,3),(0,8,4),(0,3,5),(0,4,5)]),(4,[(0,3,5),(0,4,5)]),(21,[(0,3,5),(0,4,5)]),(45,[]),(46,[]),(1,[(0,8,3),(0,18,4),(3,38,5),(0,3,5)]),(3,[(0,8,3),(0,18,4),(0,3,5),(0,4,5)]),(4,[(0,18,4),(0,3,5),(0,4,5)]),(21,[(0,18,4),(0,3,5),(0,4,5)]),(28,[(1,0,1),(0,8,3),(0,18,4),(0,3,5),(0,4,5)]),(10,[(0,18,4),(0,3,5),(0,4,5)]),(1,[(0,3,4),(3,2,7),(3,39,5),(0,3,5)]),(0,[(0,3,4),(0,3,5)]),(1,[(0,8,3),(0,18,4),(3,38,5),(0,8,5)]),(3,[]),(1,[(0,8,3),(0,18,4),(0,8,5),(0,3,5)]),(3,[(0,8,3),(0,18,4),(0,8,5),(0,3,5)]),(4,[(0,18,4),(0,3,5)]),(21,[(0,18,4),(0,3,5)]),(18,[(1,0,1),(0,8,3),(0,18,4)]),(1,[]),(16,[(1,0,1),(1,8,2),(2,23,10)]),(11,[(1,0,1),(1,8,2),(0,7,5),(2,23,10)]),(17,[(1,0,1),(1,8,2),(2,23,10)]),(41,[(1,0,1),(1,8,2),(0,7,5),(2,23,10)]),(19,[(1,0,1),(1,8,2),(2,23,10)]),(18,[(1,0,1),(1,8,2),(0,3,4),(2,23,10)]),(1,[(0,8,3),(0,18,4),(0,38,5),(3,56,8)]),(3,[(0,8,3),(0,18,4),(0,38,5),(3,56,8)]),(10,[(0,18,4),(0,38,5)]),(11,[(1,0,1),(0,7,5),(2,8,10)]),(41,[(1,0,1),(0,7,5),(2,8,10)]),(1,[(0,8,3),(0,3,4),(0,7,5),(2,8,10)]),(1,[(0,3,4),(0,7,5)]),(1,[(1,0,2),(0,3,4),(0,7,5)]),(3,[(0,3,4),(0,7,5)]),(3,[(1,1,2),(0,3,4),(0,7,5)]),(4,[(1,1,2),(0,3,4),(0,7,5)]),(0,[(1,0,1),(0,3,4),(0,7,5)]),(16,[(1,0,1),(1,0,2),(1,1,2)]),(17,[(1,0,1),(1,0,2),(1,1,2)]),(19,[(1,0,1),(1,0,2),(1,1,2)]),(4,[(0,18,4),(0,38,5)]),(21,[(0,18,4),(0,38,5)]),(1,[(0,8,3),(0,4,5),(2,18,21),(3,55,8)]),(1,[(0,8,3),(0,4,5),(0,18,21),(3,56,4)]),(47,[]),(1,[(2,8,2),(0,3,4),(0,3,5),(0,4,5)]),(3,[(2,8,2),(0,3,4),(0,3,5),(0,4,5)]),(48,[]),(49,[]),(50,[]),(1,[(0,8,3),(0,18,4),(0,38,5),(1,56,2)]),(51,[]),(52,[]),(53,[]),(11,[(1,0,1),(0,8,4),(0,7,5)]),(41,[(1,0,1),(0,7,5)]),(1,[(0,8,3),(0,4,5),(0,8,21),(0,3,21)]),(41,[(1,0,1),(0,8,3),(0,8,21),(0,3,21)]),(4,[(1,1,2),(0,3,4),(3,7,5)]),(0,[(1,0,1),(0,3,4),(3,7,5)]),(18,[(1,0,1),(1,0,2),(1,1,2),(0,3,4)]),(3,[(1,8,2),(0,3,4),(0,3,5),(0,4,5)]),(1,[(1,8,2),(0,3,4),(0,3,5),(0,4,5)]),(1,[(0,8,3),(0,18,4),(0,38,5),(3,56,3)]),(1,[(0,3,4),(0,7,5),(1,2,10),(0,8,81)]),(9,[(0,3,4),(0,7,5)]),(8,[(0,3,4),(0,7,5)]),(28,[(1,0,1),(0,3,4),(0,7,5),(0,8,81)]),(1,[(0,8,3),(0,18,4),(0,18,5),(0,4,5)]),(11,[(1,0,1),(0,18,4),(0,18,5),(0,4,5)]),(18,[(1,0,1),(0,3,4),(1,0,10),(1,1,10)]),(11,[(1,0,1),(0,7,5),(1,0,10),(1,1,10)]),(1,[(0,8,3),(0,4,5),(2,18,21),(3,55,18)]),(11,[(1,0,1),(0,4,5),(2,18,21),(3,55,18)]),(1,[(0,3,4),(0,8,7),(3,38,5),(0,7,5)]),(18,[(1,0,1),(0,8,3),(0,18,4),(3,56,8)]),(54,[]),(11,[(1,0,1),(1,0,2),(1,1,2),(0,7,5)]),(1,[(0,8,3),(0,8,4),(0,3,5),(0,16,4)]),(55,[]),(56,[]),(11,[(1,0,1),(1,0,2),(0,7,5),(2,8,10)]),(4,[(1,1,2),(0,3,4),(0,3,5)]),(0,[(1,0,1),(0,3,4),(0,3,5)]),(41,[(1,0,1),(1,0,2),(1,1,2),(0,3,5)]),(3,[(0,3,4),(0,7,5),(1,26,1)]),(1,[(0,3,4),(0,7,5),(3,0,10)]),(28,[(0,3,4),(0,3,5),(0,4,5)]),(1,[(0,3,4),(3,0,7),(0,3,5),(0,4,5)]),(28,[(0,3,4),(3,0,7),(0,3,5),(0,4,5)]),(1,[(0,3,4),(3,0,7),(3,14,5),(0,7,5)]),(28,[(0,3,4),(3,0,7),(3,14,5),(0,7,5)]),(16,[(1,0,10),(1,1,10)]),(17,[(1,0,10),(1,1,10)]),(19,[(1,0,10),(1,1,10)]),(57,[]),(58,[]),(10,[(0,4,5)]),(17,[(1,0,1)]),(16,[(1,0,1)]),(11,[(1,0,1),(0,4,5)]),(1,[(0,3,4),(3,7,5),(3,9,8)]),(3,[(0,3,4),(3,7,5),(3,9,8)]),(28,[(1,0,1),(0,3,4),(3,7,5),(3,9,8)]),(10,[(0,3,4),(3,7,5)]),(11,[(1,0,1),(3,7,5),(3,9,8)]),(41,[(1,0,1),(3,7,5),(3,9,8)]),(1,[(0,8,3),(0,4,5),(2,18,21)]),(1,[(0,8,3),(0,18,4),(0,38,5)]),(59,[]),(11,[(1,0,1),(0,18,4),(0,38,5)]),(1,[(0,3,4),(0,7,5),(2,8,10)]),(16,[(1,0,1),(2,8,10)]),(17,[(1,0,1),(2,8,10)]),(3,[(0,3,4),(0,7,5),(2,8,10)]),(19,[(1,0,1),(2,8,10)]),(1,[(0,3,4),(0,7,5),(3,2,10)]),(28,[(0,3,4),(0,7,5)]),(28,[(1,0,1),(0,3,4),(0,7,5)]),(10,[(0,3,4),(0,7,5)]),(60,[]),(3,[(0,3,4),(0,7,5),(1,8,10)]),(1,[(0,3,4),(0,7,5),(1,8,10)]),(16,[(1,0,1),(1,8,10)]),(17,[(1,0,1),(1,8,10)]),(19,[(1,0,1),(1,8,10)]),(61,[]),(16,[(1,0,1),(1,0,10)]),(17,[(1,0,1),(1,0,10)]),(18,[(1,0,1),(0,3,4),(1,0,10)]),(19,[(1,0,1),(1,0,10)]),(11,[(1,0,1),(0,7,5),(1,0,10)]),(62,[]),(4,[(0,3,4),(0,3,5)]),(1,[(0,3,4),(2,8,7),(0,3,5)]),(3,[(0,3,4),(2,8,7),(0,3,5)]),(21,[(0,3,4),(0,3,5)]),(10,[(0,3,4),(0,3,5)]),(18,[(1,0,1),(0,3,4),(2,8,7)]),(1,[(0,3,4),(2,8,7),(3,37,5)]),(4,[(0,3,4),(3,37,5)]),(3,[(0,3,4),(2,8,7),(3,37,5)]),(21,[(0,3,4),(3,37,5)]),(10,[(0,3,4),(3,37,5)]),(11,[(1,0,1),(2,8,7),(3,37,5)]),(41,[(1,0,1),(2,8,7),(3,37,5)]),(18,[(1,0,1),(0,3,4)]),(1,[(0,3,4),(3,2,7),(0,7,5)]),(1,[(0,3,4),(0,8,7),(0,3,5)]),(41,[]),(63,[]),(1,[(0,8,3),(0,4,5),(0,3,21)]),(4,[(0,4,5),(0,3,21)]),(41,[(1,0,1),(0,8,3),(0,3,21)]),(41,[(1,0,1),(1,8,2),(0,23,3)]),(64,[]),(1,[(0,8,3),(0,4,5),(0,8,21)]),(11,[(1,0,1),(0,4,5),(0,8,21)]),(41,[(1,0,1),(0,8,3),(0,8,21)]),(1,[(0,8,3),(0,4,5),(0,18,21)]),(8,[(0,4,5)]),(41,[(1,0,1),(0,8,3),(0,18,21)]),(1,[(0,8,3),(0,3,4),(0,4,5)]),(3,[(0,8,3),(0,3,4),(0,4,5)]),(4,[(0,3,4),(0,4,5)]),(21,[(0,3,4),(0,4,5)]),(18,[(1,0,1),(0,8,3),(0,3,4)]),(28,[(1,0,1),(0,8,3),(0,3,4),(0,4,5)]),(10,[(0,3,4),(0,4,5)]),(1,[(0,8,3),(0,8,4),(0,3,5)]),(3,[(0,8,3),(0,8,4),(0,3,5)]),(4,[(0,3,5)]),(21,[(0,3,5)]),(10,[(0,3,5)]),(18,[(1,0,1),(0,8,3),(0,8,4)]),(41,[(1,0,1),(0,8,3),(0,3,5)]),(0,[(0,3,4),(3,7,5)]),(19,[(1,0,1),(1,8,2)]),(18,[(1,0,1),(1,8,2),(0,3,4)]),(3,[(1,8,2),(0,3,4),(3,7,5)]),(1,[(1,8,2),(0,3,4),(3,7,5)]),(1,[(0,3,4),(3,2,7),(0,3,5)]),(28,[(1,0,1),(0,3,4),(0,3,5)]),(1,[(0,8,3),(0,18,4),(0,4,5)]),(11,[(1,0,1),(0,18,4),(0,4,5)]),(1,[(0,8,3),(0,18,4),(3,38,5)]),(3,[(0,8,3),(0,18,4),(3,38,5)]),(1,[(0,8,3),(0,8,4),(0,3,4)]),(3,[(0,8,3),(0,8,4),(0,3,4)]),(4,[(0,3,4)]),(21,[(0,3,4)]),(10,[(0,3,4)]),(1,[(0,8,3),(0,18,4),(0,8,5)]),(1,[(0,8,3),(0,18,4),(0,3,5)]),(3,[(0,8,3),(0,18,4),(0,3,5)]),(28,[(1,0,1),(0,8,3),(0,18,4),(0,3,5)]),(10,[(0,18,4),(0,3,5)]),(1,[(1,0,2),(0,3,4),(0,3,5)]),(18,[(1,0,1),(1,0,2),(0,3,4)]),(19,[(1,0,1),(1,0,2)]),(41,[(1,0,1),(1,0,2),(0,3,5)]),(17,[(1,0,1),(1,0,2)]),(65,[]),(16,[(1,0,1),(2,8,2)]),(17,[(1,0,1),(2,8,2)]),(18,[(1,0,1),(2,8,2),(0,3,4)]),(19,[(1,0,1),(2,8,2)]),(11,[(1,0,1),(2,8,2),(0,7,5)]),(3,[(0,8,3),(0,18,4),(0,38,5)]),(41,[(1,0,1),(0,8,3),(0,38,5)]),(3,[(0,8,3),(0,18,4),(0,8,5)]),(4,[(0,18,4)]),(21,[(0,18,4)]),(10,[(0,18,4)]),(11,[(1,0,1),(0,18,4),(0,8,5)]),(41,[(1,0,1),(0,8,3),(0,8,5)]),(1,[(0,8,3),(3,18,4),(0,8,5)]),(18,[(1,0,1),(0,8,3),(3,18,4)]),(1,[(0,8,3),(0,3,4),(3,7,5)]),(3,[(0,8,3),(0,3,4),(3,7,5)]),(28,[(1,0,1),(0,8,3),(0,3,4),(3,7,5)]),(64,[(0,3,4),(0,7,5)]),(16,[(1,0,1),(1,0,2)]),(1,[(0,8,3),(0,18,4),(0,18,5)]),(41,[(1,0,1),(0,8,3),(0,18,5)]),(11,[(1,0,1),(0,18,4),(0,18,5)]),(16,[(1,0,10),(3,1,25)]),(17,[(1,0,10),(3,1,25)]),(18,[(0,3,4),(1,0,10),(3,1,25)]),(19,[(1,0,10),(3,1,25)]),(11,[(0,7,5),(1,0,10),(3,1,25)]),(18,[(1,0,1),(0,3,4),(1,8,10)]),(11,[(1,0,1),(0,7,5),(1,8,10)]),(66,[]),(11,[(1,0,1),(0,7,5)]),(1,[(0,3,4),(0,8,7),(0,7,5)]),(11,[(1,0,1),(0,8,7),(0,7,5)]),(67,[]),(1,[(0,8,3),(3,18,4),(3,36,5)]),(41,[(1,0,1),(0,8,3),(3,36,5)]),(28,[(1,0,1),(0,3,4),(3,7,5)]),(11,[(1,0,1),(0,18,4),(3,38,5)]),(18,[(0,3,4),(1,0,10),(1,1,10)]),(11,[(0,7,5),(1,0,10),(1,1,10)]),(1,[(2,8,2),(0,3,4),(0,7,5)]),(3,[(2,8,2),(0,3,4),(0,7,5)]),(1,[(0,8,3),(0,3,4),(0,7,5)]),(3,[(0,8,3),(0,3,4),(0,7,5)]),(4,[(1,1,2),(0,3,4)]),(0,[(1,0,1),(0,3,4)]),(11,[(1,0,1),(1,0,2),(1,1,2)]),(41,[(1,0,1),(1,0,2),(1,1,2)]),(1,[(0,8,3),(0,4,5),(3,18,21)]),(41,[(1,0,1),(0,8,3),(3,18,21)]),(3,[(2,8,2),(0,3,4),(0,3,5)]),(1,[(2,8,2),(0,3,4),(0,3,5)]),(41,[(1,0,1),(2,8,2),(0,3,5)]),(1,[(0,3,4),(0,7,5),(0,8,10)]),(3,[(0,3,4),(0,7,5),(0,8,10)]),(11,[(1,0,1),(1,8,2),(0,46,4)]),(1,[(0,3,4),(0,8,7),(3,38,5)]),(18,[(1,0,1),(0,3,4),(0,8,7)]),(11,[(1,0,1),(0,8,7),(3,38,5)]),(16,[(1,0,1),(1,8,2)]),(17,[(1,0,1),(1,8,2)]),(11,[(1,0,1),(1,8,2),(0,7,5)]),(3,[(1,8,2),(0,3,4),(0,7,5)]),(1,[(1,8,2),(0,3,4),(0,7,5)]),(28,[(1,0,1),(0,8,3),(0,3,4),(0,7,5)]),(41,[(1,0,1),(0,8,3),(0,7,5)]),(1,[(0,8,3),(3,18,4),(0,3,5)]),(4,[(0,18,4),(3,38,5)]),(21,[(0,18,4),(3,38,5)]),(28,[(1,0,1),(0,8,3),(0,18,4),(3,38,5)]),(10,[(0,18,4),(3,38,5)]),(41,[(1,0,1),(0,8,3),(3,38,5)]),(68,[]),(1,[(0,3,4),(3,0,7),(3,14,5),(0,3,5)]),(28,[(0,3,4),(3,0,7),(3,14,5),(0,3,5)]),(1,[(0,3,4),(3,2,7),(3,39,5)]),(0,[(0,3,4)]),(11,[(1,0,1),(3,2,7),(3,39,5)]),(69,[]),(1,[(0,3,4),(0,7,5),(1,2,10)]),(11,[(1,0,1),(1,0,2),(0,7,5)]),(3,[(1,8,2),(0,3,4),(0,3,5)]),(1,[(1,8,2),(0,3,4),(0,3,5)]),(41,[(1,0,1),(1,8,2),(0,3,5)]),(1,[(3,2,3),(0,4,5),(3,17,21)]),(0,[(0,4,5)]),(41,[(1,0,1),(3,2,3),(3,17,21)]),(1,[(1,0,2),(0,3,4),(3,7,5)]),(16,[(1,0,10)]),(17,[(1,0,10)]),(18,[(0,3,4),(1,0,10)]),(19,[(1,0,10)]),(11,[(0,7,5),(1,0,10)]),(28,[(0,3,4),(0,7,5),(3,0,10)]),(3,[(0,3,4),(0,3,5)]),(1,[(0,3,4),(3,0,7),(0,3,5)]),(28,[(0,3,4),(3,0,7),(0,3,5)]),(18,[(1,0,1),(1,0,2),(1,1,2)]),(1,[(0,3,4),(3,0,7),(3,14,5)]),(28,[(0,3,4),(3,0,7),(3,14,5)]),(18,[(0,3,4),(3,0,7)]),(11,[(3,0,7),(3,14,5)]),(41,[(3,0,3),(3,0,21)]),(3,[(0,4,5),(0,6,21)]),(21,[(0,4,5)]),(41,[(3,0,3),(0,6,21)]),(64,[(0,3,4)]),(11,[(3,0,7),(1,14,1)]),(70,[]),(41,[(3,0,3),(3,13,5)]),(3,[(1,6,1),(0,4,5)]),(71,[]),(64,[(0,4,5)]),(11,[(1,6,1),(0,4,5)]),(41,[(3,0,3),(1,6,1)]),(8,[(0,3,4)]),(11,[(1,0,1),(3,8,7)]),(1,[(0,3,4),(0,3,5)]),(41,[(1,0,1),(0,3,5)]),(41,[(1,0,1),(0,8,3)]),(1,[(0,8,3),(3,18,4)]),(1,[(0,3,4),(3,7,5)]),(3,[(0,3,4),(3,7,5)]),(28,[(0,3,4),(0,7,5),(1,0,10)]),(20,[(0,3,4),(0,7,5)]),(1,[(0,3,4),(2,8,7)]),(3,[(0,3,4),(2,8,7)]),(1,[(0,3,4),(0,8,7)]),(3,[(0,3,4),(0,8,7)]),(11,[(1,0,1),(0,8,7)]),(11,[(1,0,1),(3,2,7)]),(56,[(0,4,5)]),(41,[(1,0,1),(3,2,3)]),(18,[(1,0,1),(3,2,3)]),(72,[]),(9,[(0,4,5)]),(41,[(3,0,3),(3,1,21)]),(73,[]),(11,[(0,4,5)]),(3,[(3,8,3),(0,4,5)]),(1,[(3,8,3),(0,4,5)]),(41,[(1,0,1),(3,8,3)]),(1,[(0,8,3),(0,3,4)]),(3,[(0,8,3),(0,3,4)]),(28,[(1,0,1),(0,8,3),(0,3,4)]),(1,[(0,8,3),(0,8,4)]),(11,[(1,0,1),(0,8,4)]),(3,[(0,4,5),(3,6,21)]),(1,[(3,0,3),(0,4,5),(3,6,21)]),(28,[(3,0,3),(0,4,5),(3,6,21)]),(41,[(3,0,3),(3,6,21)]),(11,[(0,6,4),(3,14,5)]),(41,[(3,0,3),(3,14,5)]),(3,[(2,8,2),(0,3,4)]),(1,[(2,8,2),(0,3,4)]),(28,[(1,0,1),(0,3,4)]),(11,[(1,0,1),(2,8,2)]),(41,[(1,0,1),(2,8,2)]),(11,[(1,0,1),(3,20,4)]),(1,[(0,3,4),(3,0,7),(0,7,5)]),(28,[(0,3,4),(3,0,7),(0,7,5)]),(1,[(0,8,3),(0,18,4)]),(11,[(1,0,1),(0,18,4)]),(1,[(0,8,3),(0,4,5)]),(3,[(0,8,3),(0,4,5)]),(4,[(0,4,5)]),(18,[(1,0,1),(0,8,3)]),(8,[(0,8,3)]),(28,[(1,0,1),(0,8,3),(0,18,4)]),(3,[(0,8,3),(0,18,4)]),(3,[(1,8,2),(0,3,4)]),(1,[(1,8,2),(0,3,4)]),(11,[(1,0,1),(1,8,2)]),(41,[(1,0,1),(1,8,2)]),(18,[(1,0,1),(1,8,2),(0,23,3)]),(1,[(1,0,2),(0,3,4)]),(11,[(1,0,1),(1,0,2)]),(41,[(1,0,1),(1,0,2)]),(11,[(1,0,1),(3,18,4)]),(11,[(1,0,1),(3,2,4)]),(18,[(0,3,4)]),(28,[(0,3,4),(3,7,5)]),(11,[(0,7,5)]),(41,[(0,7,5)]),(74,[]),(11,[(3,1,4)]),(41,[(3,0,3)]),(75,[]),(18,[(3,0,3),(3,6,4)]),(3,[(0,3,4)]),(1,[(0,3,4),(3,0,7)]),(28,[(0,3,4),(3,0,7)]),(11,[(3,0,7)]),(18,[(3,0,3),(1,6,1)]),(1,[(0,3,4)]),(11,[(1,0,1)]),(41,[(1,0,1)]),(28,[(0,3,4),(0,3,5)]),(41,[(0,3,5)]),(3,[(0,6,4)]),(11,[(0,6,4)]),(1,[(0,8,3)]),(18,[(1,0,1),(2,8,2)]),(18,[(1,0,1),(3,8,3)]),(52,[(0,4,5)]),(18,[(3,0,3)]),(3,[(0,4,5)]),(1,[(3,0,3),(0,4,5)]),(28,[(3,0,3),(0,4,5)]),(11,[(3,0,4)]),(18,[(1,0,1),(1,8,2)]),(18,[(1,0,1),(1,0,2)]),(28,[(0,3,4)]),(18,[(1,0,1)])]
def P_58 : Array (Option BoundPool) := buildPools W_58 R_58 slices_58 ps_58
lemma gp_58 : goodPairs G_58 pos_58 neg_58 := goodPairs_of (by decide +kernel)
lemma base_58_ok : ∀ x ∈ base_58, faithful pos_58 neg_58 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_58_ok : ∀ x ∈ W_58.toList, faithful pos_58 neg_58 x ∧ x.1 < 2^128 := buildWires_faithful base_58_ok
lemma autos_58_ok : ∀ sw ∈ autos_58.toList, swapsValid sw = true ∧ permWord sw G_58 = G_58 := autos_of (by decide +kernel)
lemma sl_58_0_ok : sliceDirectCheck 0 4 0 R_58 G_58 R_56 G_56 = true := by decide +kernel
lemma sl_58_0 : Slice R_58 G_58 (subcube 0 4) 8 := slice_direct sl_58_0_ok low_56
lemma sl_58_1_ok : sliceDirectCheck 2 0 0 R_58 G_58 R_53 G_53 = true := by decide +kernel
lemma sl_58_1 : Slice R_58 G_58 (subcube 2 0) 10 := slice_direct sl_58_1_ok low_53
lemma sl_58_2_ok : sliceDirectCheck 4 48 0 R_58 G_58 R_2 G_2 = true := by decide +kernel
lemma sl_58_2 : Slice R_58 G_58 (subcube 4 48) 4 := slice_direct sl_58_2_ok low_2
lemma sl_58_3_ok : sliceDirectCheck 1 0 0 R_58 G_58 R_47 G_47 = true := by decide +kernel
lemma sl_58_3 : Slice R_58 G_58 (subcube 1 0) 10 := slice_direct sl_58_3_ok low_47
lemma sl_58_4_ok : sliceDirectCheck 0 1 0 R_58 G_58 R_49 G_49 = true := by decide +kernel
lemma sl_58_4 : Slice R_58 G_58 (subcube 0 1) 8 := slice_direct sl_58_4_ok low_49
lemma sl_58_5_ok : sliceDirectCheck 1 20 0 R_58 G_58 R_13 G_13 = true := by decide +kernel
lemma sl_58_5 : Slice R_58 G_58 (subcube 1 20) 4 := slice_direct sl_58_5_ok low_13
lemma sl_58_6_ok : sliceDirectCheck 2 36 0 R_58 G_58 R_10 G_10 = true := by decide +kernel
lemma sl_58_6 : Slice R_58 G_58 (subcube 2 36) 4 := slice_direct sl_58_6_ok low_10
lemma sl_58_7_ok : sliceDirectCheck 1 10 0 R_58 G_58 R_18 G_18 = true := by decide +kernel
lemma sl_58_7 : Slice R_58 G_58 (subcube 1 10) 4 := slice_direct sl_58_7_ok low_18
lemma sl_58_8_ok : sliceDirectCheck 1 4 0 R_58 G_58 R_37 G_37 = true := by decide +kernel
lemma sl_58_8 : Slice R_58 G_58 (subcube 1 4) 7 := slice_direct sl_58_8_ok low_37
lemma sl_58_9_ok : sliceDirectCheck 2 4 0 R_58 G_58 R_36 G_36 = true := by decide +kernel
lemma sl_58_9 : Slice R_58 G_58 (subcube 2 4) 7 := slice_direct sl_58_9_ok low_36
lemma sl_58_10_ok : sliceDirectCheck 4 1 0 R_58 G_58 R_37 G_37 = true := by decide +kernel
lemma sl_58_10 : Slice R_58 G_58 (subcube 4 1) 7 := slice_direct sl_58_10_ok low_37
lemma sl_58_11_ok : sliceDirectCheck 0 8 0 R_58 G_58 R_48 G_48 = true := by decide +kernel
lemma sl_58_11 : Slice R_58 G_58 (subcube 0 8) 10 := slice_direct sl_58_11_ok low_48
lemma sl_58_12_ok : sliceDirectCheck 1 24 0 R_58 G_58 R_9 G_9 = true := by decide +kernel
lemma sl_58_12 : Slice R_58 G_58 (subcube 1 24) 4 := slice_direct sl_58_12_ok low_9
lemma sl_58_13_ok : sliceDirectCheck 8 16 0 R_58 G_58 R_19 G_19 = true := by decide +kernel
lemma sl_58_13 : Slice R_58 G_58 (subcube 8 16) 5 := slice_direct sl_58_13_ok low_19
lemma sl_58_14_ok : sliceDirectCheck 32 8 0 R_58 G_58 R_24 G_24 = true := by decide +kernel
lemma sl_58_14 : Slice R_58 G_58 (subcube 32 8) 5 := slice_direct sl_58_14_ok low_24
lemma sl_58_15_ok : sliceDirectCheck 0 33 0 R_58 G_58 R_42 G_42 = true := by decide +kernel
lemma sl_58_15 : Slice R_58 G_58 (subcube 0 33) 5 := slice_direct sl_58_15_ok low_42
lemma sl_58_16_ok : sliceDirectCheck 0 48 0 R_58 G_58 R_34 G_34 = true := by decide +kernel
lemma sl_58_16 : Slice R_58 G_58 (subcube 0 48) 7 := slice_direct sl_58_16_ok low_34
lemma sl_58_17_ok : sliceDirectCheck 0 40 0 R_58 G_58 R_35 G_35 = true := by decide +kernel
lemma sl_58_17 : Slice R_58 G_58 (subcube 0 40) 7 := slice_direct sl_58_17_ok low_35
lemma sl_58_18_ok : sliceDirectCheck 0 32 0 R_58 G_58 R_54 G_54 = true := by decide +kernel
lemma sl_58_18 : Slice R_58 G_58 (subcube 0 32) 10 := slice_direct sl_58_18_ok low_54
lemma sl_58_19_ok : sliceDirectCheck 0 24 0 R_58 G_58 R_20 G_20 = true := by decide +kernel
lemma sl_58_19 : Slice R_58 G_58 (subcube 0 24) 7 := slice_direct sl_58_19_ok low_20
lemma sl_58_20_ok : sliceDirectCheck 2 1 0 R_58 G_58 R_21 G_21 = true := by decide +kernel
lemma sl_58_20 : Slice R_58 G_58 (subcube 2 1) 7 := slice_direct sl_58_20_ok low_21
lemma sl_58_21_ok : sliceDirectCheck 0 2 0 R_58 G_58 R_57 G_57 = true := by decide +kernel
lemma sl_58_21 : Slice R_58 G_58 (subcube 0 2) 8 := slice_direct sl_58_21_ok low_57
lemma sl_58_22_ok : sliceDirectCheck 0 5 2 R_58 G_58 R_0 G_0 = true := by decide +kernel
lemma sl_58_22 : Slice R_58 G_58 (subcube 0 5) 4 := slice_direct sl_58_22_ok low_0
lemma sl_58_23_ok : sliceDirectCheck 0 6 1 R_58 G_58 R_0 G_0 = true := by decide +kernel
lemma sl_58_23 : Slice R_58 G_58 (subcube 0 6) 4 := slice_direct sl_58_23_ok low_0
lemma sl_58_24_ok : sliceDirectCheck 8 0 0 R_58 G_58 R_46 G_46 = true := by decide +kernel
lemma sl_58_24 : Slice R_58 G_58 (subcube 8 0) 6 := slice_direct sl_58_24_ok low_46
lemma sl_58_25_ok : sliceDirectCheck 16 0 0 R_58 G_58 R_51 G_51 = true := by decide +kernel
lemma sl_58_25 : Slice R_58 G_58 (subcube 16 0) 6 := slice_direct sl_58_25_ok low_51
lemma sl_58_26_ok : sliceDirectCheck 32 16 0 R_58 G_58 R_23 G_23 = true := by decide +kernel
lemma sl_58_26 : Slice R_58 G_58 (subcube 32 16) 5 := slice_direct sl_58_26_ok low_23
lemma sl_58_27_ok : sliceDirectCheck 16 32 0 R_58 G_58 R_23 G_23 = true := by decide +kernel
lemma sl_58_27 : Slice R_58 G_58 (subcube 16 32) 5 := slice_direct sl_58_27_ok low_23
lemma sl_58_28_ok : sliceDirectCheck 4 0 0 R_58 G_58 R_52 G_52 = true := by decide +kernel
lemma sl_58_28 : Slice R_58 G_58 (subcube 4 0) 10 := slice_direct sl_58_28_ok low_52
lemma sl_58_29_ok : sliceDirectCheck 32 0 0 R_58 G_58 R_50 G_50 = true := by decide +kernel
lemma sl_58_29 : Slice R_58 G_58 (subcube 32 0) 6 := slice_direct sl_58_29_ok low_50
lemma sl_58_30_ok : sliceDirectCheck 1 2 0 R_58 G_58 R_21 G_21 = true := by decide +kernel
lemma sl_58_30 : Slice R_58 G_58 (subcube 1 2) 7 := slice_direct sl_58_30_ok low_21
lemma sl_58_31_ok : sliceDirectCheck 4 24 0 R_58 G_58 R_3 G_3 = true := by decide +kernel
lemma sl_58_31 : Slice R_58 G_58 (subcube 4 24) 4 := slice_direct sl_58_31_ok low_3
lemma sl_58_32_ok : sliceDirectCheck 4 18 0 R_58 G_58 R_11 G_11 = true := by decide +kernel
lemma sl_58_32 : Slice R_58 G_58 (subcube 4 18) 4 := slice_direct sl_58_32_ok low_11
lemma sl_58_33_ok : sliceDirectCheck 4 9 0 R_58 G_58 R_17 G_17 = true := by decide +kernel
lemma sl_58_33 : Slice R_58 G_58 (subcube 4 9) 4 := slice_direct sl_58_33_ok low_17
lemma sl_58_34_ok : sliceDirectCheck 16 40 0 R_58 G_58 R_1 G_1 = true := by decide +kernel
lemma sl_58_34 : Slice R_58 G_58 (subcube 16 40) 4 := slice_direct sl_58_34_ok low_1
lemma sl_58_35_ok : sliceDirectCheck 8 48 0 R_58 G_58 R_1 G_1 = true := by decide +kernel
lemma sl_58_35 : Slice R_58 G_58 (subcube 8 48) 4 := slice_direct sl_58_35_ok low_1
lemma sl_58_36_ok : sliceDirectCheck 32 24 0 R_58 G_58 R_1 G_1 = true := by decide +kernel
lemma sl_58_36 : Slice R_58 G_58 (subcube 32 24) 4 := slice_direct sl_58_36_ok low_1
lemma sl_58_37_ok : sliceDirectCheck 0 18 0 R_58 G_58 R_41 G_41 = true := by decide +kernel
lemma sl_58_37 : Slice R_58 G_58 (subcube 0 18) 5 := slice_direct sl_58_37_ok low_41
lemma sl_58_38_ok : sliceDirectCheck 0 9 0 R_58 G_58 R_22 G_22 = true := by decide +kernel
lemma sl_58_38 : Slice R_58 G_58 (subcube 0 9) 5 := slice_direct sl_58_38_ok low_22
lemma sl_58_39_ok : sliceDirectCheck 2 32 0 R_58 G_58 R_28 G_28 = true := by decide +kernel
lemma sl_58_39 : Slice R_58 G_58 (subcube 2 32) 7 := slice_direct sl_58_39_ok low_28
lemma sl_58_40_ok : sliceDirectCheck 1 16 0 R_58 G_58 R_32 G_32 = true := by decide +kernel
lemma sl_58_40 : Slice R_58 G_58 (subcube 1 16) 7 := slice_direct sl_58_40_ok low_32
lemma sl_58_41_ok : sliceDirectCheck 0 16 0 R_58 G_58 R_55 G_55 = true := by decide +kernel
lemma sl_58_41 : Slice R_58 G_58 (subcube 0 16) 10 := slice_direct sl_58_41_ok low_55
lemma sl_58_42_ok : sliceDirectCheck 16 8 0 R_58 G_58 R_19 G_19 = true := by decide +kernel
lemma sl_58_42 : Slice R_58 G_58 (subcube 16 8) 5 := slice_direct sl_58_42_ok low_19
lemma sl_58_43_ok : sliceDirectCheck 2 48 0 R_58 G_58 R_4 G_4 = true := by decide +kernel
lemma sl_58_43 : Slice R_58 G_58 (subcube 2 48) 4 := slice_direct sl_58_43_ok low_4
lemma sl_58_44_ok : sliceDirectCheck 2 40 0 R_58 G_58 R_5 G_5 = true := by decide +kernel
lemma sl_58_44 : Slice R_58 G_58 (subcube 2 40) 4 := slice_direct sl_58_44_ok low_5
lemma sl_58_45_ok : sliceDirectCheck 2 24 0 R_58 G_58 R_6 G_6 = true := by decide +kernel
lemma sl_58_45 : Slice R_58 G_58 (subcube 2 24) 4 := slice_direct sl_58_45_ok low_6
lemma sl_58_46_ok : sliceDirectCheck 8 32 0 R_58 G_58 R_24 G_24 = true := by decide +kernel
lemma sl_58_46 : Slice R_58 G_58 (subcube 8 32) 5 := slice_direct sl_58_46_ok low_24
lemma sl_58_47_ok : sliceDirectCheck 1 48 0 R_58 G_58 R_7 G_7 = true := by decide +kernel
lemma sl_58_47 : Slice R_58 G_58 (subcube 1 48) 4 := slice_direct sl_58_47_ok low_7
lemma sl_58_48_ok : sliceDirectCheck 0 20 0 R_58 G_58 R_39 G_39 = true := by decide +kernel
lemma sl_58_48 : Slice R_58 G_58 (subcube 0 20) 5 := slice_direct sl_58_48_ok low_39
lemma sl_58_49_ok : sliceDirectCheck 0 36 0 R_58 G_58 R_38 G_38 = true := by decide +kernel
lemma sl_58_49 : Slice R_58 G_58 (subcube 0 36) 5 := slice_direct sl_58_49_ok low_38
lemma sl_58_50_ok : sliceDirectCheck 0 12 0 R_58 G_58 R_44 G_44 = true := by decide +kernel
lemma sl_58_50 : Slice R_58 G_58 (subcube 0 12) 5 := slice_direct sl_58_50_ok low_44
lemma sl_58_51_ok : sliceDirectCheck 1 32 0 R_58 G_58 R_31 G_31 = true := by decide +kernel
lemma sl_58_51 : Slice R_58 G_58 (subcube 1 32) 7 := slice_direct sl_58_51_ok low_31
lemma sl_58_52_ok : sliceDirectCheck 1 8 0 R_58 G_58 R_33 G_33 = true := by decide +kernel
lemma sl_58_52 : Slice R_58 G_58 (subcube 1 8) 7 := slice_direct sl_58_52_ok low_33
lemma sl_58_53_ok : sliceDirectCheck 0 17 0 R_58 G_58 R_43 G_43 = true := by decide +kernel
lemma sl_58_53 : Slice R_58 G_58 (subcube 0 17) 5 := slice_direct sl_58_53_ok low_43
lemma sl_58_54_ok : sliceDirectCheck 2 8 0 R_58 G_58 R_30 G_30 = true := by decide +kernel
lemma sl_58_54 : Slice R_58 G_58 (subcube 2 8) 7 := slice_direct sl_58_54_ok low_30
lemma sl_58_55_ok : sliceDirectCheck 0 34 0 R_58 G_58 R_40 G_40 = true := by decide +kernel
lemma sl_58_55 : Slice R_58 G_58 (subcube 0 34) 5 := slice_direct sl_58_55_ok low_40
lemma sl_58_56_ok : sliceDirectCheck 4 8 0 R_58 G_58 R_27 G_27 = true := by decide +kernel
lemma sl_58_56 : Slice R_58 G_58 (subcube 4 8) 7 := slice_direct sl_58_56_ok low_27
lemma sl_58_57_ok : sliceDirectCheck 4 33 0 R_58 G_58 R_12 G_12 = true := by decide +kernel
lemma sl_58_57 : Slice R_58 G_58 (subcube 4 33) 4 := slice_direct sl_58_57_ok low_12
lemma sl_58_58_ok : sliceDirectCheck 4 17 0 R_58 G_58 R_13 G_13 = true := by decide +kernel
lemma sl_58_58 : Slice R_58 G_58 (subcube 4 17) 4 := slice_direct sl_58_58_ok low_13
lemma sl_58_59_ok : sliceDirectCheck 1 6 0 R_58 G_58 R_0 G_0 = true := by decide +kernel
lemma sl_58_59 : Slice R_58 G_58 (subcube 1 6) 4 := slice_direct sl_58_59_ok low_0
lemma sl_58_60_ok : sliceDirectCheck 4 32 0 R_58 G_58 R_25 G_25 = true := by decide +kernel
lemma sl_58_60 : Slice R_58 G_58 (subcube 4 32) 7 := slice_direct sl_58_60_ok low_25
lemma sl_58_61_ok : sliceDirectCheck 2 9 0 R_58 G_58 R_18 G_18 = true := by decide +kernel
lemma sl_58_61 : Slice R_58 G_58 (subcube 2 9) 4 := slice_direct sl_58_61_ok low_18
lemma sl_58_62_ok : sliceDirectCheck 0 7 0 R_58 G_58 R_0 G_0 = true := by decide +kernel
lemma sl_58_62 : Slice R_58 G_58 (subcube 0 7) 4 := slice_direct sl_58_62_ok low_0
lemma sl_58_63_ok : sliceDirectCheck 4 10 0 R_58 G_58 R_16 G_16 = true := by decide +kernel
lemma sl_58_63 : Slice R_58 G_58 (subcube 4 10) 4 := slice_direct sl_58_63_ok low_16
lemma sl_58_64_ok : sliceDirectCheck 4 2 0 R_58 G_58 R_36 G_36 = true := by decide +kernel
lemma sl_58_64 : Slice R_58 G_58 (subcube 4 2) 7 := slice_direct sl_58_64_ok low_36
lemma sl_58_65_ok : sliceDirectCheck 2 12 0 R_58 G_58 R_16 G_16 = true := by decide +kernel
lemma sl_58_65 : Slice R_58 G_58 (subcube 2 12) 4 := slice_direct sl_58_65_ok low_16
lemma sl_58_66_ok : sliceDirectCheck 1 18 0 R_58 G_58 R_15 G_15 = true := by decide +kernel
lemma sl_58_66 : Slice R_58 G_58 (subcube 1 18) 4 := slice_direct sl_58_66_ok low_15
lemma sl_58_67_ok : sliceDirectCheck 0 10 0 R_58 G_58 R_45 G_45 = true := by decide +kernel
lemma sl_58_67 : Slice R_58 G_58 (subcube 0 10) 5 := slice_direct sl_58_67_ok low_45
lemma sl_58_68_ok : sliceDirectCheck 4 16 0 R_58 G_58 R_26 G_26 = true := by decide +kernel
lemma sl_58_68 : Slice R_58 G_58 (subcube 4 16) 7 := slice_direct sl_58_68_ok low_26
lemma sl_58_69_ok : sliceDirectCheck 2 20 0 R_58 G_58 R_11 G_11 = true := by decide +kernel
lemma sl_58_69 : Slice R_58 G_58 (subcube 2 20) 4 := slice_direct sl_58_69_ok low_11
lemma sl_58_70_ok : sliceDirectCheck 2 17 0 R_58 G_58 R_15 G_15 = true := by decide +kernel
lemma sl_58_70 : Slice R_58 G_58 (subcube 2 17) 4 := slice_direct sl_58_70_ok low_15
lemma sl_58_71_ok : sliceDirectCheck 1 40 0 R_58 G_58 R_8 G_8 = true := by decide +kernel
lemma sl_58_71 : Slice R_58 G_58 (subcube 1 40) 4 := slice_direct sl_58_71_ok low_8
lemma sl_58_72_ok : sliceDirectCheck 2 33 0 R_58 G_58 R_14 G_14 = true := by decide +kernel
lemma sl_58_72 : Slice R_58 G_58 (subcube 2 33) 4 := slice_direct sl_58_72_ok low_14
lemma sl_58_73_ok : sliceDirectCheck 1 12 0 R_58 G_58 R_17 G_17 = true := by decide +kernel
lemma sl_58_73 : Slice R_58 G_58 (subcube 1 12) 4 := slice_direct sl_58_73_ok low_17
lemma sl_58_74_ok : sliceDirectCheck 2 16 0 R_58 G_58 R_29 G_29 = true := by decide +kernel
lemma sl_58_74 : Slice R_58 G_58 (subcube 2 16) 7 := slice_direct sl_58_74_ok low_29
lemma sl_58_75_ok : sliceDirectCheck 4 3 0 R_58 G_58 R_0 G_0 = true := by decide +kernel
lemma sl_58_75 : Slice R_58 G_58 (subcube 4 3) 4 := slice_direct sl_58_75_ok low_0
set_option maxRecDepth 200000 in
lemma slices_58_ok : ∀ i (hi : i < slices_58.size), Slice R_58 G_58 slices_58[i].1 slices_58[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_58 G_58 p.1 p.2) (forall_cons sl_58_0 (forall_cons sl_58_1 (forall_cons sl_58_2 (forall_cons sl_58_3 (forall_cons sl_58_4 (forall_cons sl_58_5 (forall_cons sl_58_6 (forall_cons sl_58_7 (forall_cons sl_58_8 (forall_cons sl_58_9 (forall_cons sl_58_10 (forall_cons sl_58_11 (forall_cons sl_58_12 (forall_cons sl_58_13 (forall_cons sl_58_14 (forall_cons sl_58_15 (forall_cons sl_58_16 (forall_cons sl_58_17 (forall_cons sl_58_18 (forall_cons sl_58_19 (forall_cons sl_58_20 (forall_cons sl_58_21 (forall_cons sl_58_22 (forall_cons sl_58_23 (forall_cons sl_58_24 (forall_cons sl_58_25 (forall_cons sl_58_26 (forall_cons sl_58_27 (forall_cons sl_58_28 (forall_cons sl_58_29 (forall_cons sl_58_30 (forall_cons sl_58_31 (forall_cons sl_58_32 (forall_cons sl_58_33 (forall_cons sl_58_34 (forall_cons sl_58_35 (forall_cons sl_58_36 (forall_cons sl_58_37 (forall_cons sl_58_38 (forall_cons sl_58_39 (forall_cons sl_58_40 (forall_cons sl_58_41 (forall_cons sl_58_42 (forall_cons sl_58_43 (forall_cons sl_58_44 (forall_cons sl_58_45 (forall_cons sl_58_46 (forall_cons sl_58_47 (forall_cons sl_58_48 (forall_cons sl_58_49 (forall_cons sl_58_50 (forall_cons sl_58_51 (forall_cons sl_58_52 (forall_cons sl_58_53 (forall_cons sl_58_54 (forall_cons sl_58_55 (forall_cons sl_58_56 (forall_cons sl_58_57 (forall_cons sl_58_58 (forall_cons sl_58_59 (forall_cons sl_58_60 (forall_cons sl_58_61 (forall_cons sl_58_62 (forall_cons sl_58_63 (forall_cons sl_58_64 (forall_cons sl_58_65 (forall_cons sl_58_66 (forall_cons sl_58_67 (forall_cons sl_58_68 (forall_cons sl_58_69 (forall_cons sl_58_70 (forall_cons sl_58_71 (forall_cons sl_58_72 (forall_cons sl_58_73 (forall_cons sl_58_74 (forall_cons sl_58_75 (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
lemma P_58_ok : ∀ i (hi : i < P_58.size), ∀ c, P_58[i] = some c → ValidPool R_58 G_58 c := buildPools_sound slices_58_ok
def bk_58_init : Array (List (List Nat)) := #[]
lemma bk_58_init_ok : ∀ i (hi : i < bk_58_init.size), ∀ xs ∈ bk_58_init[i], Impossible G_58 (0 - 1) xs.toFinset := by intro i hi; simp [bk_58_init] at hi
def nodes_58_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_58_0 : checkNodes W_58 G_58 fmask_58 P_58 autos_58 bk_58_init 0 nodes_58_0 = true := by decide +kernel
def bk_58_0 : Array (List (List Nat)) := buildBuckets 1 W_58 nodes_58_0
lemma bk_58_0_ok : ∀ i (hi : i < bk_58_0.size), ∀ xs ∈ bk_58_0[i], Impossible G_58 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_58 W_58_ok P_58_ok autos_58_ok bk_58_init_ok chk_58_0
def nodes_58_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_58_1 : checkNodes W_58 G_58 fmask_58 P_58 autos_58 bk_58_0 1 nodes_58_1 = true := by decide +kernel
def bk_58_1 : Array (List (List Nat)) := buildBuckets 1 W_58 nodes_58_1
lemma bk_58_1_ok : ∀ i (hi : i < bk_58_1.size), ∀ xs ∈ bk_58_1[i], Impossible G_58 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_58 W_58_ok P_58_ok autos_58_ok bk_58_0_ok chk_58_1
def nodes_58_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_58_2 : checkNodes W_58 G_58 fmask_58 P_58 autos_58 bk_58_1 2 nodes_58_2 = true := by decide +kernel
def bk_58_2 : Array (List (List Nat)) := buildBuckets 1 W_58 nodes_58_2
lemma bk_58_2_ok : ∀ i (hi : i < bk_58_2.size), ∀ xs ∈ bk_58_2[i], Impossible G_58 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_58 W_58_ok P_58_ok autos_58_ok bk_58_1_ok chk_58_2
def nodes_58_3 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_58_3 : checkNodes W_58 G_58 fmask_58 P_58 autos_58 bk_58_2 3 nodes_58_3 = true := by decide +kernel
def bk_58_3 : Array (List (List Nat)) := buildBuckets 1 W_58 nodes_58_3
lemma bk_58_3_ok : ∀ i (hi : i < bk_58_3.size), ∀ xs ∈ bk_58_3[i], Impossible G_58 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_58 W_58_ok P_58_ok autos_58_ok bk_58_2_ok chk_58_3
def nodes_58_4 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_58_4 : checkNodes W_58 G_58 fmask_58 P_58 autos_58 bk_58_3 4 nodes_58_4 = true := by decide +kernel
def bk_58_4 : Array (List (List Nat)) := buildBuckets 1 W_58 nodes_58_4
lemma bk_58_4_ok : ∀ i (hi : i < bk_58_4.size), ∀ xs ∈ bk_58_4[i], Impossible G_58 4 xs.toFinset :=
  buildBuckets_sound (by decide) gp_58 W_58_ok P_58_ok autos_58_ok bk_58_3_ok chk_58_4
def nodes_58_5 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_58_5 : checkNodes W_58 G_58 fmask_58 P_58 autos_58 bk_58_4 5 nodes_58_5 = true := by decide +kernel
def bk_58_5 : Array (List (List Nat)) := buildBuckets 1 W_58 nodes_58_5
lemma bk_58_5_ok : ∀ i (hi : i < bk_58_5.size), ∀ xs ∈ bk_58_5[i], Impossible G_58 5 xs.toFinset :=
  buildBuckets_sound (by decide) gp_58 W_58_ok P_58_ok autos_58_ok bk_58_4_ok chk_58_5
def nodes_58_6 : List NodeSpec := [([57,0,1,96,2,4,5],[0],[]),([57,0,1,2,80,3,4],[0],[]),([94,0,1,8,85,4,5],[1],[]),([57,94,0,1,2,4,5],[2],[]),([8,24,27,7,16,21],[3,4,5,6,7,8,9,10,11,12],[]),([57,0,1,85,3,4,5],[13,14,15],[]),([57,24,27,10,3,4,5],[16],[]),([94,93,0,1,8,2,5],[17],[]),([57,24,27,7,3,4,5],[18],[]),([57,24,27,3,4,5],[19,20],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_58_6 : checkNodes W_58 G_58 fmask_58 P_58 autos_58 bk_58_5 6 nodes_58_6 = true := by decide +kernel
def bk_58_6 : Array (List (List Nat)) := buildBuckets 4 W_58 nodes_58_6
lemma bk_58_6_ok : ∀ i (hi : i < bk_58_6.size), ∀ xs ∈ bk_58_6[i], Impossible G_58 6 xs.toFinset :=
  buildBuckets_sound (by decide) gp_58 W_58_ok P_58_ok autos_58_ok bk_58_5_ok chk_58_6
def nd_58_7_0 : List NodeSpec := [([0,1,31,2,7,16,21],[21,22,5,23,24],[]),([84,0,1,10,7,3,4,5],[25,26,27,28,29,30],[]),([57,0,1,2,3,81,4,5],[0,5,31,32],[]),([84,0,1,10,3,4,5],[0,16,13,33,34,26,27,29],[]),([0,1,8,85,10,3,4,5],[35,36,13,37,38,24,39,40,41],[0]),([0,1,86,2,10,3,4,5],[42,43,44,38,45,39,46,47],[]),([57,58,0,1,2,3,4,5],[16,5,0],[1,2,0]),([57,0,1,2,10,3,4,5],[43,46,45,48],[]),([87,57,0,1,2,3,4,5],[42,0,49,31,32],[]),([8,2,10,3,25,51,4,5],[47,38,39,50,51,33,52,53,54],[]),([39,0,1,8,2,7,16,21],[22,55,56,57,58,23,59,60,61],[]),([0,1,8,2,80,10,3,4],[62,55,63,41,38,13],[0]),([37,0,1,8,2,16,21],[22,64,65,25,66,67,68,55,69,70,71,72],[]),([57,39,0,1,2,3,4,5],[73,16,57,0,74],[0]),([0,1,38,8,2,7,16,21],[75,48,76,77,65,64,22,59,60],[]),([68,0,1,8,2,7,16,4],[48,41,78,77,79,70,59],[]),([0,1,88,8,2,3,21,5],[80,39,48,81,47,41],[]),([0,1,18,8,2,89,4,5],[82,43,34,83],[]),([57,0,1,2,3,21,4,5],[84,43,46,45,48,85],[]),([36,0,1,69,2,16,4],[86,25,87,77,88,89,12],[]),([0,1,18,66,2,7,21,5],[90,87,24,25,76],[]),([9,0,1,18,43,2,5],[43,34,25,16,64,91,92,21,93,94,95],[]),([0,1,18,43,2,10,5],[96,97,98,99,87,100,16,64],[]),([0,1,38,18,69,2,3,21],[101,40,25,76,22,77],[]),([0,1,38,18,8,2,16,21],[102,64,25,77],[]),([0,1,18,43,2,16,21],[103,104,105,106,22,86,25,77,87,76,100],[]),([68,0,1,18,8,2,16,4],[78,107,108,109,24],[]),([0,1,38,8,2,16,21],[102,110,111,112,48,64,78,76,77,113,114,22,59,60],[]),([0,1,8,2,80,7,16,4],[115,55,116,41,38,59,78,57],[]),([68,0,1,38,69,2,3,4],[78,38,76,77,117],[]),([57,1,2,24,3,4,5],[118,42,49,31],[0]),([0,1,38,69,2,16,4],[119,120,121,122,78,123,107,76,77,86],[]),([90,0,1,2,3,4,5],[118,43,124,34,42,0,125,126,127,128,129,130],[]),([57,0,1,56,2,3,4,5],[47,124,131,132,133],[0,3,4]),([57,0,1,2,91,3,4,5],[49,0,134,135,74],[0,3,4]),([57,0,1,18,2,10,4,5],[38,45,43,100,22,107,108,136,98,99],[]),([68,0,1,18,69,2,3,4],[78,47,43,76,117,38],[]),([8,24,27,10,3,4,5],[137,138,5,139,140,141,142,143,144,145],[0,5,6]),([57,0,1,2,3,4,5],[118,124,42,0,46,84,45,48,146,132,147,131],[]),([0,1,38,2,16,21],[102,22,110,73,86],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_58_7_0 : checkNodes W_58 G_58 fmask_58 P_58 autos_58 bk_58_6 7 nd_58_7_0 = true := by decide +kernel
def nd_58_7_1 : List NodeSpec := [([0,1,38,18,69,2,16,4],[119,25,107,76,77],[]),([0,1,18,92,2,3,4,5],[148,47,84,43,38],[]),([93,0,1,8,2,3,21,5],[45,40,124,81,149,60],[]),([19,0,1,2,7,16,21],[150,3,151,23,48,22,45,24,152,61,153,154,155],[]),([0,1,38,8,85,3,4,5],[156,70,11],[4]),([1,8,2,24,7,16,21],[4,6,61,65,81,157,158],[0]),([0,1,18,43,2,10,7,5],[96,159,12,160,87,161,100,91,64],[]),([67,36,0,1,2,5],[38,39,76,159,41],[]),([0,1,18,66,2,10,4,5],[162,25,76,87,163],[]),([9,8,24,27,3,4,5],[164,165,10,12,145,166,107,55],[]),([0,1,2,23,7,16,21],[167,23,168,22,48,45,24,46,153,25,77],[]),([94,0,1,56,8,2,4,5],[124,169],[0,2]),([94,0,1,18,8,2,4,5],[124,43,169,24],[]),([90,0,1,2,10,3,4,5],[0,46,45,48,125,127,129],[]),([0,1,95,2,10,3,4,5],[170,171,36,13,150,172,37,47,42,173],[]),([0,1,38,73,8,2,3,21],[174,25,70,59,76,175,22],[]),([8,2,7,3,25,51,4,5],[38,39,176,53,177,107],[]),([0,1,56,8,85,3,4,5],[156,13,16],[0,3,4]),([0,1,56,8,2,3,4,5],[178,118,179,13,16],[]),([68,0,1,8,2,10,3,4],[48,41,124,180,38,24,40],[4]),([68,0,1,38,8,2,16,4],[78,107,41,77,109,70],[]),([94,0,1,38,8,2,4,5],[124,169,70],[2]),([57,1,2,24,10,3,4,5],[5,43,31,49],[0]),([90,0,1,2,7,3,4,5],[73,0,48,45,46,130,129,126],[]),([57,0,1,38,2,3,4,5],[38,124,48,131,181],[4]),([57,0,1,18,2,3,4,5],[158,182,46,47,38,131],[]),([8,24,27,10,7,3,4,5],[107,55,12,10,11,143,144,166,145,183],[0,5,6]),([0,1,18,43,2,10,16,5],[184,25,185,41,100,64],[]),([57,1,2,24,7,3,4,5],[186,187],[0]),([57,0,1,18,2,7,4,5],[158,182,46,43,38,100,22,136,135],[]),([8,24,27,7,16,4,5],[186,182,158,188,189,10,11,12,166,145,190,144],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_58_7_1 : checkNodes W_58 G_58 fmask_58 P_58 autos_58 bk_58_6 7 nd_58_7_1 = true := by decide +kernel
def nodes_58_7 : List NodeSpec := nd_58_7_0 ++ nd_58_7_1
lemma chk_58_7 : checkNodes W_58 G_58 fmask_58 P_58 autos_58 bk_58_6 7 nodes_58_7 = true := by
  unfold nodes_58_7 checkNodes
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨chk_58_7_0, chk_58_7_1⟩
def bk_58_7 : Array (List (List Nat)) := buildBuckets 24 W_58 nodes_58_7
lemma bk_58_7_ok : ∀ i (hi : i < bk_58_7.size), ∀ xs ∈ bk_58_7[i], Impossible G_58 7 xs.toFinset :=
  buildBuckets_sound (by decide) gp_58 W_58_ok P_58_ok autos_58_ok bk_58_6_ok chk_58_7
def nd_58_8_0 : List NodeSpec := [([0,1,50,2,10,3,4,5],[191,43,47,99,192,5,63,37,16,38,39],[]),([14,0,1,2,7,16,21],[48,22,3,193,45,81,158,24,21,6,194,195,86],[0,5,6]),([0,29,1,2,10,3,4],[47,21,43,196,197],[6]),([0,1,31,2,7,16,4,5],[21,38,186,116,24,45,41],[0]),([0,1,2,10,3,25,51,4,5],[47,139,98,137,99,198,51,33,199,200],[0]),([0,1,31,2,10,3,4,5],[21,43,38,34,33,5,63,47,37,16],[]),([52,0,1,2,3,21,5],[39,81,25,201,24],[]),([0,53,1,2,3,21,5],[39,150,25,157,202,203,24],[]),([0,1,8,2,7,16,21],[3,6,193,61,65,69,22,48,64,45,204,24,46,205,206,81],[0,7,2,1]),([0,1,54,8,2,3,4,5],[207,21,93,208,95,16,13,76,77,209,210,108,41,211,212],[0,4]),([0,1,54,2,3,4,5],[107,207,21,208,42,41,0,38,108],[]),([55,0,1,18,8,2,3,4,5],[213,83,38],[0]),([0,1,56,18,8,2,3,4,5],[214,158,87,215,16,24,216,38],[0]),([57,0,1,8,2,7,3,4,5],[158,182,38,78,43,76,74,87,100,217,98,134,135],[0,3]),([57,0,1,2,7,3,4,5],[158,182,186,153,73,74,43,98,46,218,134,45,219,135,220,217,49,221],[0,7]),([58,0,1,8,2,10,3,4,5],[98,139,99,137,47,16,222,36,13,37,223,63,38,24,39,40,41,224],[0,1,2]),([57,0,1,8,2,3,4,5],[118,217,220,47,16,13,87,134,100,135,107,74,98,99,49,225],[0]),([57,0,1,2,3,4,5],[118,217,220,42,49,0,46,134,45,135,48,74],[0,7]),([59,0,1,38,2,3,4,5],[12,159,107,0,38,226,41,57,13,14,108,47],[]),([0,1,2,10,3,60,4,5],[98,227,99,228,16,37,223,63,229,230,231,46,45,48],[0]),([1,8,2,10,7,3,25,4,5],[232,107,38,39,24,25,233,158,234,235,236,237],[0]),([1,8,2,10,3,25,4,5],[54,139,225,238,47,38,39,233,234,236],[0]),([0,1,61,2,7,4,5],[12,159,107,38,124,84,40,16,39,41],[]),([37,0,1,8,2,16,4,5],[38,64,239,25,240,241,242,55,243,70,71,244],[0]),([57,0,1,2,10,3,4,5],[47,137,217,5,63,43,98,218,45,134,219,46,135,221,74,220,49],[0,7]),([0,1,8,2,3,62,4,5],[245,21,246,247,248,55,249,250,47,244,251],[0]),([39,0,1,8,2,10,3,4,5],[38,55,13,57,252,253,37,63,39,70,41],[0]),([0,1,38,2,3,4,5],[12,124,38,159,107,0,42,73,47,39,41],[]),([0,1,38,8,2,7,16,4,5],[254,48,76,77,252,239,64,38,59],[0,4]),([63,0,1,8,2,3,4,5],[118,43,124,34,47,10,41,57,186],[]),([64,0,1,2,3,4,5],[118,22,124,0,255,73,47,10,256],[]),([0,1,18,8,2,10,21,4,5],[257,25,76,45,87,60,258,182,204,64,259],[0,3,4]),([0,1,2,65,46,4,5],[10,76,159,57,33,38,108,260],[]),([59,36,0,1,2,3,4,5],[0,39,226,22,12,159,107,41,57,261,186],[]),([0,1,18,66,2,3,21,4,5],[262,47,87,39,206,22,43,25,76,263,264],[0,2]),([0,1,56,8,2,3,21,4,5],[265,81,266,56,77,47,60,39,267],[0,2]),([0,1,18,8,2,7,21,5],[268,269,270,271,45,206,81,77,87,272,273,274,22,64,60],[2,1,0]),([67,0,1,2,7,4,5],[38,124,84,40,76,159,41],[]),([0,1,18,43,2,16,4,5],[275,276,277,278,38,86,182,25,77,41,57,279,76,100,280,281],[8,1,0]),([9,0,1,2,23,3,4,5],[13,43,33,34,16,48,282,41,153,25,77,283,284,285,286,108,47],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_58_8_0 : checkNodes W_58 G_58 fmask_58 P_58 autos_58 bk_58_7 8 nd_58_8_0 = true := by decide +kernel
def nd_58_8_1 : List NodeSpec := [([39,0,1,8,2,7,16,4,5],[38,55,56,57,252,287,116,59,70,288,11],[0]),([0,1,38,18,8,2,3,21,5],[289,81,64,76,25,77,123,290,22],[0]),([68,0,1,2,3,4,5],[118,47,43,34,124,0,42,84,38,255,39,291,292,24,40,41],[]),([0,1,18,43,2,7,5],[293,294,295,296,182,81,76,77,57,91,56,297,64],[2,1,0]),([0,1,38,18,69,2,3,4,5],[298,40,38,25,107,76,77],[0]),([0,1,38,8,2,16,4,5],[299,300,121,122,48,64,78,76,77,123,301,302,59,281],[0]),([1,8,2,24,7,16,4,5],[158,303,288,239,81,157,304,305,306,307],[0]),([19,0,1,2,10,7,3,4,5],[38,57,153,48,10,256,308,224,63,25,309,310,311,312,313],[]),([0,1,56,8,2,3,4,5],[214,314,146,147,16,13,133,216,315,123],[0,3,4]),([0,1,38,69,2,3,4,5],[298,316,317,318,47,38,78,123,107,16,215,76,77,57,319,39,320,321],[0,3]),([0,1,56,38,8,2,3,4,5],[214,12,78,57,70,123],[0,3,4]),([0,1,18,70,2,4,5],[215,38,43,22,108,16],[]),([36,0,1,69,2,3,4,5],[157,43,33,34,84,39,47,46,22,25,16,215,24,77,321,322,12,57,323],[0]),([0,1,38,2,71,3,4,5],[13,14,12,159,107,38,57,41],[]),([0,1,72,2,3,4,5],[12,43,47,77,124,57,256,39,40,0,38,24],[]),([9,0,1,18,8,2,4,5],[43,34,25,107,108,16,182,64,272,324,21,93,325,95,326,210],[0]),([1,8,2,24,10,3,4,5],[138,139,224,98,261,327,13,171,328,307,305],[0,5]),([9,0,1,18,2,4,5],[108,43,34,16,182,107,324,21,325,60],[]),([0,1,38,73,8,2,3,4,5],[329,330,78,70,25,59,331,38],[4,3,0]),([68,0,1,38,8,2,3,4,5],[78,107,76,41,77,291,70,123],[4,0,3]),([74,0,1,2,10,7,3,4,5],[38,232,158,48,76,25,332,333,334,335,336],[]),([0,1,38,2,16,4,5],[299,38,300,73,22,41],[0]),([0,1,18,2,75,3,4,5],[13,14,158,43,202,34,182,215,60,41],[]),([0,1,38,18,8,2,16,4,5],[299,64,25,76,77,108],[0]),([0,1,2,10,7,3,60,4,5],[55,25,229,230,45,337,231,46,338],[0,4]),([0,1,45,2,3,21,5],[339,25,56,22,86,185,73,41],[]),([67,0,1,38,2,4,5],[38,124,86,76,159,41],[0]),([36,0,1,2,16,4,5],[22,73,12,77,57,256,41],[]),([57,0,1,8,2,10,3,4,5],[217,150,47,43,340,100,161,107,252,98,99,134,135,74],[0,3,4]),([0,1,38,8,2,10,3,4,5],[341,159,12,48,78,252,38,86,22,41,342],[0,4]),([0,1,18,2,76,3,4,5],[13,14,158,43,77,182,34,22,343,215,60],[]),([74,0,1,2,10,3,4,5],[150,47,98,5,63,34,33,54,38,45,39,327,51,332,333,335],[]),([0,1,72,8,2,3,4,5],[344,77,12,47,45,41,16,13,345,57],[]),([9,19,0,1,2,3,4,5],[0,48,16,41,13,33,34,282,346,153,25,154,77,155,312,311],[]),([68,0,1,18,8,2,3,4,5],[81,78,25,76,107,108,291,24,123,347],[4,0]),([0,1,2,7,3,25,51,4,5],[38,21,159,107,76,348,200,349],[0]),([19,0,1,2,10,3,4,5],[150,137,350,63,16,225,13,351,34,327,309,310,312],[]),([0,1,18,2,10,4,5],[352,38,353,43,34,16,22,108],[]),([8,24,27,7,3,4,5],[186,182,57,158,12,354,355,10,11,166,145,356,357],[0,3]),([77,0,1,2,3,4,5],[84,47,43,34,0,42,39,77,343],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_58_8_1 : checkNodes W_58 G_58 fmask_58 P_58 autos_58 bk_58_7 8 nd_58_8_1 = true := by decide +kernel
def nd_58_8_2 : List NodeSpec := [([77,0,1,8,2,3,21,4,5],[45,46,47,60,358,39,359],[0,2]),([67,0,1,18,2,4,5],[38,43,34,16,108,76,159],[0]),([49,0,1,18,2,16,4,5],[158,25,182,185,38,22,56,57,60,226],[]),([19,0,1,2,7,16,4,5],[186,182,158,116,48,38,45,86,24,360,361,288,153,154,155,311,312,362,310],[0]),([0,1,56,8,2,10,3,4,5],[363,139,98,364,99,224,38,24,39,40,41],[0,1,2]),([0,1,18,2,47,7,4,5],[182,159,16,76,261,38,77,56,22,108],[]),([0,1,2,65,3,4,5],[10,76,159,57,124,38,41,365],[]),([68,0,1,8,2,7,3,4,5],[48,45,24,41,43,78,107,76,77,366,70,38,367,368],[0,3]),([0,1,2,23,10,7,3,4,5],[159,10,76,232,57,38,48,39,24,45,25,369,370,284,283,371],[0]),([78,0,1,2,3,4,5],[255,47,43,34,0,42,38,76,159,24],[]),([0,1,2,23,10,3,4,5],[372,63,43,98,373,34,99,16,224,47,38,45,39,46,369,370,283],[0]),([0,1,18,8,2,10,4,5],[352,353,98,99,45,340,87,374,225,38,375,272,204,64],[0,2]),([36,0,1,8,2,16,4,5],[84,86,182,22,87,77,281,376,12,57,59,323],[0]),([36,0,1,18,2,7,5],[22,255,77,343,108],[]),([68,0,1,8,2,3,4,5],[118,43,124,34,48,47,107,41,123,16,13,76,77,291,292,377,378,379,380,24,40,347,381],[4]),([79,0,1,2,3,4,5],[84,39,43,34,0,73,47,77,155,41,260],[]),([0,1,38,2,47,3,4,5],[13,16,86,159,14,76,382,38,77,154,108],[]),([0,29,1,2,7,16,4],[24,40,21,73,158,383,384],[6]),([0,1,2,46,7,4,5],[10,76,159,57,38,33,108,255],[]),([0,1,8,2,80,7,3,4,5],[385,55,386,76,41,38,24,16,78,107,57,56,11,387],[0,3]),([0,1,2,46,21,4,5],[10,25,388,76,22,56,77,60,260],[]),([79,0,1,2,46,4,5],[13,22,43,33,34,16,77,155,343,260],[]),([0,1,8,2,10,3,81,4,5],[389,171,36,13,172,37,223,47,38,24,98,39,40,41,224],[0]),([1,8,2,24,10,7,3,4,5],[107,256,232,55,308,157,328,307,304,305,390],[0,5]),([57,0,1,2,10,7,3,4,5],[76,45,48,46,74,218,219,221,134],[]),([0,1,2,23,7,16,4,5],[391,116,392,38,48,45,41,40,153,25,77,284,283,393,370],[0]),([0,1,82,2,3,4,5],[339,43,47,25,124,56,24,0],[]),([0,1,56,2,3,4,5],[214,118,47,314,0,42,38,39],[]),([0,1,8,2,83,3,21,4,5],[394,5,395,47,25,60,39,13,11,10,396],[]),([9,1,8,2,24,3,4,5],[33,261,93,13,81,158,305,304,21,397,346],[0]),([0,1,18,8,2,10,7,4,5],[352,159,158,76,45,87,161,38,98,64,108,204],[0,2]),([0,1,18,2,7,21,5],[268,108,269,46,60],[2])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_58_8_2 : checkNodes W_58 G_58 fmask_58 P_58 autos_58 bk_58_7 8 nd_58_8_2 = true := by decide +kernel
def nodes_58_8 : List NodeSpec := nd_58_8_0 ++ nd_58_8_1 ++ nd_58_8_2
lemma chk_58_8 : checkNodes W_58 G_58 fmask_58 P_58 autos_58 bk_58_7 8 nodes_58_8 = true := by
  unfold nodes_58_8 checkNodes
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨chk_58_8_0, chk_58_8_1⟩, chk_58_8_2⟩
def bk_58_8 : Array (List (List Nat)) := buildBuckets 37 W_58 nodes_58_8
lemma bk_58_8_ok : ∀ i (hi : i < bk_58_8.size), ∀ xs ∈ bk_58_8[i], Impossible G_58 8 xs.toFinset :=
  buildBuckets_sound (by decide) gp_58 W_58_ok P_58_ok autos_58_ok bk_58_7_ok chk_58_8
def nd_58_9_0 : List NodeSpec := [([0,1,2,10,7,3,25,4,5],[139,38,39,24,232,70,107,57,55,25,398,399,400,401,402],[0,5]),([26,0,1,2,10,3,4,5],[47,139,137,223,38,39,43,192,403,238],[0,5,1,2,6]),([14,0,1,2,7,16,4,5],[48,182,38,186,45,81,158,40,404,41,405,406],[0,5,6]),([8,24,27,3,4,5],[124,42,16,261,356,357,407],[0,2,1]),([28,14,0,1,2,3,4,5],[43,34,38,182,158,48,238,25,41],[]),([0,29,1,2,7,3,4,5],[45,24,48,41,21,118,158,81,408,409,410,411],[6,0,3]),([6,30,1,2,3,21,4,5],[24,45,25,60,46,118,157,81,202,203,412],[]),([26,0,1,2,3,21,4,5],[47,413,414,78,395,226,24,158,39,202,203,60,415],[0,2]),([0,1,31,2,7,3,4,5],[12,21,38,107,33,34,186,386,70,45,16,215,256,41,416,185,417],[0,3]),([32,0,1,2,3,4,5],[255,158,124,47,34,41,42,0,43,202,418,419],[6]),([0,1,15,2,3,21,4,5],[339,420,60,56,418,226,395,45,33,47,34,39,421,215,422,423,424],[]),([0,1,2,3,33,4,5],[43,48,16,124,33],[]),([0,1,8,2,10,7,3,4,5],[137,21,139,295,296,55,38,48,98,64,39,70,45,252,57,425,224,205,204,340],[0,7,4,3]),([34,0,1,2,7,3,4,5],[38,107,21,386,186,39,45,41,76,159,51,33,215,16,426],[0,3]),([0,1,8,2,7,16,4,5],[427,158,404,186,288,239,243,38,48,64,45,204,41,428,40,252],[0,7,2,3,4]),([35,0,1,18,2,3,4,5],[16,182,261,38,22,108,0],[]),([36,0,1,8,2,3,4,5],[118,77,34,124,84,182,13,16,429,78,430,12,57,41],[0,3]),([9,0,1,8,2,3,4,5],[118,107,43,21,124,34,48,64,13,16,252,431,432,55,346,93,210],[0,7,3]),([0,1,2,7,3,25,4,5],[232,295,139,297,238,70,38,182,296,39,41,159,25,400,402],[]),([0,1,2,10,3,25,4,5],[54,139,43,47,38,39,433,238,24,98,434,40,41,225,398,399,401],[0,5,6]),([0,1,8,2,10,3,4,5],[137,139,43,34,223,224,98,225,47,38,340,39,161,252,13,205,204,64],[0,7,3,4]),([37,0,1,8,2,3,4,5],[118,12,124,159,107,64,295,13,16,78,435,436,296,55,297,70,244],[0,3]),([0,1,38,2,7,3,4,5],[107,437,21,438,186,38,386,43,39,45,41,64,439],[0,3]),([39,0,1,8,2,7,3,4,5],[158,159,182,76,38,297,55,107,56,57,425,252,14,39,70,41,11,64,440],[0,3]),([17,0,1,8,2,3,21,4,5],[81,25,78,76,60,203,441,206,13,266,57,87,442,443,182,261,24],[0,1,3,4]),([40,6,0,1,2,3,21,4,5],[47,24,87,60,25,81,266,202,182,444,418,76,445,5,446],[]),([41,0,13,1,2,3,4,5],[158,33,34,41,78,22,12,447,16,14,261,47,60,70],[]),([0,1,8,2,42,3,4,5],[13,14,186,57,43,39,382,41,78,442],[0,3,4]),([0,1,2,7,16,21],[3,6,193,48,45,46,448,255],[0,5,2,1,6,9,10,11,12,13]),([20,0,1,2,3,21,4,5],[60,449,450,395,226,43,46,16,215,451],[0,2]),([0,1,18,2,7,4,5],[182,452,158,453,38,454,255,43,429,108,64],[0,2]),([0,1,18,43,2,3,4,5],[455,43,16,456,255,38,81,76,77,39,41,280,429],[3,2,0,1]),([0,44,1,2,3,21,4,5],[46,47,45,150,457,60,43,458,459,460],[0,2,6]),([0,29,1,2,3,4,5],[118,43,124,33,42,16,81,47,84,24,158,40,41,461,462],[]),([19,0,1,2,7,3,4,5],[186,153,182,10,158,57,386,16,48,38,39,45,70,463,464,465,154,311,312,466,467],[0,3]),([0,1,45,2,3,4,5],[43,124,34,42,16,468,39,73,22,451],[0]),([14,0,1,2,10,3,4,5],[48,38,137,223,43,45,118,47,21,139,41,469,470,238],[0,5,6]),([0,1,38,18,8,2,3,4,5],[471,77,12,81,76,64,16,215,25,57,123,472,38,429],[0]),([0,1,18,8,2,3,21,4,5],[473,474,475,414,45,206,56,203,77,87,205,429,476,60],[0,3,4,2,1]),([0,1,38,18,2,3,4,5],[12,43,38,471,86,77,472,255,477,16,108,478,429],[0,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_58_9_0 : checkNodes W_58 G_58 fmask_58 P_58 autos_58 bk_58_8 9 nd_58_9_0 = true := by decide +kernel
def nd_58_9_1 : List NodeSpec := [([0,1,38,8,2,3,4,5],[471,479,317,318,48,64,16,57,13,319,76,78,123,39,472,429],[0,3]),([0,1,2,23,7,3,4,5],[10,76,159,480,386,481,38,48,39,70,45,77,25,284,283,482,483],[0,3,4]),([36,0,1,18,2,3,4,5],[182,22,43,34,255,16,77,343,429,57],[3,0]),([0,1,2,46,3,4,5],[43,0,124,34,38,255,22,73,77,482,260,484,60],[0,2]),([1,8,2,24,7,3,4,5],[158,57,485,465,295,81,157,304,305,486,487],[0,3]),([36,0,1,2,3,4,5],[84,39,43,22,34,42,0,429,73,12,77,57,256,232,41,488],[3,0]),([0,1,18,8,2,7,4,5],[452,158,295,453,296,57,81,76,272,454,297,38,64,429],[2,0]),([0,1,18,2,47,3,4,5],[16,261,0,38,153,22,77,154,108,60],[0,2]),([48,13,1,2,3,4,5],[43,158,73,16,33,41],[]),([0,1,38,8,2,7,3,4,5],[437,21,295,438,296,57,297,76,252,64,38,39,41,367,439],[4,0,3]),([0,1,2,46,4,5],[43,0,34,260,484],[0,2]),([0,1,38,2,3,4,5],[471,118,479,42,38,0,478,472,429,73,41],[0,3]),([0,1,18,2,3,21,4,5],[473,45,60,474,395,226,46,206,16,477,429],[0,3,4,2]),([49,0,1,18,2,3,4,5],[16,182,261,0,38,22,382,77,57,56,477,108,39,226,429,489],[0,2])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_58_9_1 : checkNodes W_58 G_58 fmask_58 P_58 autos_58 bk_58_8 9 nd_58_9_1 = true := by decide +kernel
def nodes_58_9 : List NodeSpec := nd_58_9_0 ++ nd_58_9_1
lemma chk_58_9 : checkNodes W_58 G_58 fmask_58 P_58 autos_58 bk_58_8 9 nodes_58_9 = true := by
  unfold nodes_58_9 checkNodes
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨chk_58_9_0, chk_58_9_1⟩
def bk_58_9 : Array (List (List Nat)) := buildBuckets 19 W_58 nodes_58_9
lemma bk_58_9_ok : ∀ i (hi : i < bk_58_9.size), ∀ xs ∈ bk_58_9[i], Impossible G_58 9 xs.toFinset :=
  buildBuckets_sound (by decide) gp_58 W_58_ok P_58_ok autos_58_ok bk_58_8_ok chk_58_9
def nodes_58_10 : List NodeSpec := [([9,0,1,2,3,4,5],[118,48,43,34,124,0,42,490,431,432,491],[0,5,6]),([0,1,2,10,7,3,4,5],[137,139,223,38,48,45,70,46,492,493],[0,5,4,6,14,11,15]),([0,1,2,3,11,4,5],[43,48,16,124,34,33,73],[0]),([12,6,0,1,2,3,4,5],[43,34,33,158,494,81,186,51,13,495,45,14,261,496,46,497,238],[10,2]),([0,13,1,2,3,4,5],[255,158,34,124,0,42,43,73,16,33,81,496,498],[0,6,5]),([14,0,1,2,7,3,4,5],[48,182,38,21,186,118,158,81,45,499,500,501,41,410,502],[0,5,4,6,14,15,3]),([0,1,15,2,3,4,5],[34,43,124,16,158,0,33,261,424,503],[0]),([0,1,8,2,7,3,4,5],[504,158,499,186,465,295,297,43,48,64,505,506,45,252,13],[0,7,3,4]),([0,1,2,7,16,4,5],[427,404,507,48,45,508,490],[0,5,2,6,9,11,12]),([17,0,1,8,2,3,4,5],[118,16,124,182,34,261,0,186,13,81,78,505,382,45,442,443],[0,2,3,4]),([14,0,1,2,3,4,5],[43,34,124,0,42,81,158,73,509,16,33,510,496],[0]),([0,1,18,8,2,3,4,5],[511,43,16,84,182,81,77,429,78,476,505],[0,2]),([0,1,2,10,3,4,5],[137,139,223,43,45,492,46,493,490,34,0,48],[0,5,6,11]),([19,0,1,2,3,4,5],[118,0,124,84,16,261,466,467,512],[0,2,1]),([20,0,1,2,3,4,5],[43,34,0,42,505,255,73,16,451,513],[0,2]),([6,0,1,2,3,21,4,5],[45,78,60,514,226,81,43,158,46,496,515,516,517,518,51,13,448],[0,5,6]),([6,22,1,2,3,4,5],[43,84,118,255,16,33,48,519,496],[2,1]),([0,1,18,2,3,4,5],[182,43,34,84,158,42,16,0,255,429,73,476,505],[0,2]),([0,1,2,23,3,4,5],[43,0,34,84,255,73,482,483,520],[0,3,4,1]),([1,8,2,24,3,4,5],[118,16,261,124,42,486,487,521],[0,2,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_58_10 : checkNodes W_58 G_58 fmask_58 P_58 autos_58 bk_58_9 10 nodes_58_10 = true := by decide +kernel
def bk_58_10 : Array (List (List Nat)) := buildBuckets 7 W_58 nodes_58_10
lemma bk_58_10_ok : ∀ i (hi : i < bk_58_10.size), ∀ xs ∈ bk_58_10[i], Impossible G_58 10 xs.toFinset :=
  buildBuckets_sound (by decide) gp_58 W_58_ok P_58_ok autos_58_ok bk_58_9_ok chk_58_10
def nodes_58_11 : List NodeSpec := [([6,0,1,2,3,4,5],[84,124,43,158,42,118,255,73,16,33,496,515],[0,5,2,6,16]),([0,1,2,7,3,4,5],[504,499,522,48,84,255,490],[0,5,4,6,14,11,15,3]),([0,1,8,2,3,4,5],[124,118,42,16,84,505,255,506,73,523],[0,7,3,4,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_58_11 : checkNodes W_58 G_58 fmask_58 P_58 autos_58 bk_58_10 11 nodes_58_11 = true := by decide +kernel
def bk_58_11 : Array (List (List Nat)) := buildBuckets 2 W_58 nodes_58_11
lemma bk_58_11_ok : ∀ i (hi : i < bk_58_11.size), ∀ xs ∈ bk_58_11[i], Impossible G_58 11 xs.toFinset :=
  buildBuckets_sound (by decide) gp_58 W_58_ok P_58_ok autos_58_ok bk_58_10_ok chk_58_11
def nodes_58_12 : List NodeSpec := [([0,1,2,3,4,5],[124,118,42,84,255,73],[0,5,3,4,6,17,14,11,18,15,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_58_12 : checkNodes W_58 G_58 fmask_58 P_58 autos_58 bk_58_11 12 nodes_58_12 = true := by decide +kernel
def bk_58_12 : Array (List (List Nat)) := buildBuckets 1 W_58 nodes_58_12
lemma bk_58_12_ok : ∀ i (hi : i < bk_58_12.size), ∀ xs ∈ bk_58_12[i], Impossible G_58 12 xs.toFinset :=
  buildBuckets_sound (by decide) gp_58 W_58_ok P_58_ok autos_58_ok bk_58_11_ok chk_58_12
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_58_ok : forestRootCheck R_58 G_58 [(VAR 0,27,26),(VAR 1,27,25),(VAR 2,29,25),(VAR 3,27,19),(VAR 4,27,11),(VAR 5,43,11)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_58_in : bucketContains bk_58_12 R_58 = true := by decide +kernel
lemma low_58 : Lower R_58 G_58 13 := lower_of_forest root_58_ok bk_58_12_ok root_58_in
def wit : List PEqualNP.CircuitLowerBounds.Gate := [
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 2]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 7]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 10]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 10]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 10]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 13]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 14]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 15]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 16]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 17]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 18]⟩
]
def wo : Nat := 19
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by intro g hg; simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4276676608 * 2 ^ 32 + 3892314112) ||| ((4276676608 * 2 ^ 32 + 3892314112) <<< 64)).testBit r.val := by decide +kernel
lemma root_eq : G_58 = ((4276676608 * 2 ^ 32 + 3892314112) ||| ((4276676608 * 2 ^ 32 + 3892314112) <<< 64)) := by decide
lemma low_root : Lower (varsOf 63) ((4276676608 * 2 ^ 32 + 3892314112) ||| ((4276676608 * 2 ^ 32 + 3892314112) <<< 64)) 13 := root_eq ▸ low_58
end PEqualNP.Outside.L_meta_12280
theorem PEqualNP.Outside.L_meta_12280 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676608 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676608 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_12280.table2_of_lower (4276676608 * 2 ^ 32 + 3892314112) (by decide) (by decide) (by decide) (by decide)
    13 PEqualNP.Outside.L_meta_12280.low_root
    PEqualNP.Outside.L_meta_12280.wit PEqualNP.Outside.L_meta_12280.wo (by decide)
    PEqualNP.Outside.L_meta_12280.wit_mono PEqualNP.Outside.L_meta_12280.wit_eval s hcs
