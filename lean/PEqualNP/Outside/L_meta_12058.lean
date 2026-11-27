import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_12058
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
abbrev FastPool := BoundPool × List Nat × Nat
def prepPool (vals : List Nat) (c : BoundPool) : Option FastPool :=
  let miss := vals.filter (fun w => !availM c.dom c.pm w)
  if miss.length > 2 then none
  else some (c, miss, vals.countP (isConstM c.dom))
def fastPoolCut (fp : FastPool) (k : Nat) (a b d : Nat) (ka kb : Bool) : Bool :=
  let c := fp.1
  let miss := fp.2.1
  let totC := fp.2.2
  if !miss.all (fun m => (!ka && m == a) || (!kb && m == b)) then false
  else
    let dropA := if !ka && isConstM c.dom a then 1 else 0
    let dropB := if !kb && isConstM c.dom b then 1 else 0
    let z := bin d a b
    let cRest := totC - dropA - dropB + (if isConstM c.dom z then 1 else 0)
    let zIn := availM c.dom c.pm z
    let extra := if zIn then 0 else 1
    decide (k + c.paid + extra < c.lb + cRest) && (zIn || choiceOK c.dom c.pm (d, a, b))
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
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1)
    (ndc : (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).Nodup)
    (hcut : fastPoolCut fp k a.1 b.1 d ka kb = true) :
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
        have hne_ab : a ≠ b := fun e => hab (congrArg Prod.fst e)
        have hnot_in : ∀ (x : Decor) (kx : Bool), kx = false → x ∈ ws → x.1 ∉ (delTwo ws a b ka kb).map Prod.fst → True := fun _ _ _ _ _ => trivial
        have hmem_del : ∀ u ∈ delTwo ws a b ka kb, u.1 = w → (ka = false → u ≠ a) ∧ (kb = false → u ≠ b) := by
          intro u hu _
          constructor
          · intro hka; subst hka
            have hsub1 : (delTwo ws a b false kb).Sublist (ws.erase a) := by
              cases kb <;> simp [delTwo, delOne, List.erase_sublist]
            have hu1 := hsub1.subset hu
            intro heq; subst heq
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            exact List.Nodup.not_mem_erase hnd_ws hu1
          · intro hkb; subst hkb
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            have hnd2 : (delOne ws a ka).Nodup := by cases ka; exact hnd_ws.erase a; exact hnd_ws
            have h2 := List.Nodup.not_mem_erase hnd2 (a := b)
            exact fun heq => h2 (heq ▸ hu)
        obtain ⟨u, hu, huw⟩ := List.mem_map.mp hw
        have ⟨hna', hnb'⟩ := hmem_del u hu huw
        rcases hm with ⟨hka, hwa⟩ | ⟨hkb, hwb⟩
        · have hu_eq : u = a := unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) ha (huw.trans hwa)
          exact hna' hka hu_eq
        · have hu_eq : u = b := unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) hb (huw.trans hwb)
          exact hnb' hkb hu_eq
      have hcnt := countP_delTwo_fst (isConstM c.dom) nd ha hb hab ka kb
      apply scalarPoolCut_sound (op := (d, a.1, b.1)) (rest := (delTwo ws a b ka kb).map Prod.fst) hP ndc
      unfold scalarPoolCut
      simp only [choiceVal, h_all_avail, Bool.true_and, Bool.and_true, List.countP_cons,
        Bool.and_eq_true, decide_eq_true_eq] at hcut ⊢
      rw [hcnt]
      rcases hcut with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · cases hz : availM c.dom c.pm (bin d a.1 b.1) <;>
          cases hcz : isConstM c.dom (bin d a.1 b.1) <;>
          simp only [hz, hcz, Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false,
            Bool.and_eq_true, Bool.false_eq_true, ite_true, ite_false] at h1 ⊢ <;> omega
      · cases hz : availM c.dom c.pm (bin d a.1 b.1) <;>
          simp only [hz, Bool.not_true, Bool.not_false, Bool.true_or, Bool.false_or] at h2 ⊢ <;>
          exact h2
def evalMoveBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
    if fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChildBT [] autos prevBks (cap - 1) rest (d, a.1, b.1)
def testPairBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  let z := dbin d a b
  let go := evalMoveBT cap n fmask ws cov fpools autos prevBks d a b z
  go false false && go true false && go false true && go true true
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
  have hnz_b : (z.1 == 0) = false := beq_false_of_ne hnz
  have hfr_b : (ws.any (fun v => v.1 == z.1)) = false := by
    rw [Bool.eq_false_iff]; intro h; obtain ⟨v, hv, heq⟩ := List.any_eq_true.mp h
    have hvz : v.1 = bin d a.1 b.1 := beq_iff_eq.mp heq
    exact hfr (hvz ▸ List.mem_map_of_mem hv)
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
  dsimp only [z] at hcov_b hnz_b hfr_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at test
  have hab1 : a.1 ≠ b.1 := fun eq => ne (unique_fst nd ha hb eq)
  by_cases hfp : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = true
  · obtain ⟨fp, hmem, hcut⟩ := List.any_eq_true.mp hfp
    have ⟨hv, hpr⟩ := hPools fp hmem
    exact fastPoolCut_sound hv hpr nd ha hb hab1 ndc hcut k hk h
  · have hfp_f : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = false := Bool.eq_false_iff.mpr hfp
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
      simp only [testPairBT, Bool.and_eq_true] at ht
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
  decide vals.Nodup && !(vals.contains T) &&
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
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (btGet (0, 0, 0) W idx).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply nodeBT_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    ok.1.1
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
def G_0 : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000
def R_0 : List Nat := varsOf 52
def pos_0 : List Nat := [20,20,36,36,48,48,20,36,48]
def neg_0 : List Nat := [16,4,32,4,32,16,32,16,4]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcf,0x10a),(0xffff0000ffff0000ffff0000ffff0000,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def steps_0 : List (Nat × Nat × Nat) := []
def W_0 : BT Decor := buildWiresBT 2 base_0 steps_0
def autosL_0 : List (List (Nat × Nat)) := []
def autos_0 : BT (List (Nat × Nat)) := btOfList 1 autosL_0
def slicesL_0 : List (Option (Nat × Nat)) := []
def slices_0 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_0
def ps_0 : List PoolSpec := []
def P_0 : BT (Option BoundPool) := buildPoolsBT 1 W_0 R_0 slices_0 ps_0
lemma gp_0 : goodPairs G_0 pos_0 neg_0 := goodPairs_of (by decide +kernel)
lemma base_0_ok : ∀ x ∈ base_0, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_0_ok : btAll (fun x => faithful pos_0 neg_0 x ∧ x.1 < 2^128) W_0 := buildWiresBT_faithful base_0_ok
set_option maxRecDepth 500000 in
lemma autos_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_0 = G_0) autos_0 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_0_ok : btAll (fun o => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) slices_0 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_0_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_0 G_0 c) P_0 := buildPoolsBT_sound slices_0_ok
def bk_0_init : BT (List (List Nat)) := BT.empty
lemma bk_0_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 (0 - 1) xs.toFinset) bk_0_init := trivial
def nodes_0_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_0 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_init 0 nodes_0_0 = true := by decide +kernel
def bk_0_0 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_0
set_option maxRecDepth 500000 in
lemma bk_0_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 0 xs.toFinset) bk_0_0 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_init_ok chk_0_0
def nodes_0_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_1 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_0 1 nodes_0_1 = true := by decide +kernel
def bk_0_1 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_1
set_option maxRecDepth 500000 in
lemma bk_0_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 1 xs.toFinset) bk_0_1 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_0_ok chk_0_1
def nodes_0_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_2 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_1 2 nodes_0_2 = true := by decide +kernel
def bk_0_2 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_2
set_option maxRecDepth 500000 in
lemma bk_0_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 2 xs.toFinset) bk_0_2 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_1_ok chk_0_2
def nodes_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_3 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_2 3 nodes_0_3 = true := by decide +kernel
def bk_0_3 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_3
set_option maxRecDepth 500000 in
lemma bk_0_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 3 xs.toFinset) bk_0_3 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_2_ok chk_0_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 2,20,16),(VAR 4,20,4),(VAR 5,36,4)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT bk_0_3 R_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_0 : Lower R_0 G_0 4 := lower_of_forestBT root_0_ok bk_0_3_ok root_0_in
def G_1 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def R_1 : List Nat := varsOf 7
lemma low_1_ok : carryOK [(0,3),(0,5),(1,4),(0,2)] R_1 G_1 R_0 G_0 = true := by decide +kernel
lemma low_1 : Lower R_1 G_1 4 := carry_of low_1_ok low_0
def G_2 : Nat := 0xeeee8888eeee8888eeee8888eeee8888
def R_2 : List Nat := varsOf 19
lemma low_2_ok : carryOK [(3,5),(1,3),(1,4),(0,2)] R_2 G_2 R_0 G_0 = true := by decide +kernel
lemma low_2 : Lower R_2 G_2 4 := carry_of low_2_ok low_0
def G_3 : Nat := 0xeeeeeeee88888888eeeeeeee88888888
def R_3 : List Nat := varsOf 35
lemma low_3_ok : carryOK [(1,3),(1,4),(0,2)] R_3 G_3 R_0 G_0 = true := by decide +kernel
lemma low_3 : Lower R_3 G_3 4 := carry_of low_3_ok low_0
def G_4 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
def R_4 : List Nat := varsOf 21
lemma low_4_ok : carryOK [(3,5),(1,3),(1,4),(0,1),(0,2)] R_4 G_4 R_0 G_0 = true := by decide +kernel
lemma low_4 : Lower R_4 G_4 4 := carry_of low_4_ok low_0
def G_5 : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
def R_5 : List Nat := varsOf 37
lemma low_5_ok : carryOK [(1,3),(1,4),(0,1),(0,2)] R_5 G_5 R_0 G_0 = true := by decide +kernel
lemma low_5 : Lower R_5 G_5 4 := carry_of low_5_ok low_0
def G_6 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def R_6 : List Nat := varsOf 22
lemma low_6_ok : carryOK [(3,5),(1,3),(1,4),(1,2)] R_6 G_6 R_0 G_0 = true := by decide +kernel
lemma low_6 : Lower R_6 G_6 4 := carry_of low_6_ok low_0
def G_7 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def R_7 : List Nat := varsOf 38
lemma low_7_ok : carryOK [(1,3),(1,4),(1,2)] R_7 G_7 R_0 G_0 = true := by decide +kernel
lemma low_7 : Lower R_7 G_7 4 := carry_of low_7_ok low_0
def G_8 : Nat := 0xffffaaaaaaaa0000ffffaaaaaaaa0000
def R_8 : List Nat := varsOf 49
lemma low_8_ok : carryOK [(0,1),(0,2)] R_8 G_8 R_0 G_0 = true := by decide +kernel
lemma low_8 : Lower R_8 G_8 4 := carry_of low_8_ok low_0
def G_9 : Nat := 0xffffcccccccc0000ffffcccccccc0000
def R_9 : List Nat := varsOf 50
lemma low_9_ok : carryOK [(1,2)] R_9 G_9 R_0 G_0 = true := by decide +kernel
lemma low_9 : Lower R_9 G_9 4 := carry_of low_9_ok low_0
def G_10 : Nat := 0xfcfcc0c0c0c00000fcfcc0c0c0c00000
def R_10 : List Nat := varsOf 54
def pos_10 : List Nat := [22,22,22,38,38,38,50,50,50,52,52,52,22,22,22,38,38,38,50,50,50,52,52,52]
def neg_10 : List Nat := [20,18,6,36,34,6,48,34,18,48,36,20,34,36,48,18,20,48,6,20,36,6,18,34]
def fmask_10 : Nat := fullMask 24
def base_10 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x1ff1ff,0xe491b6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xe3fe3f,0x3d2c2d),(0xffff0000ffff0000ffff0000ffff0000,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def steps_10 : List (Nat × Nat × Nat) := [(0,0,1),(3,4,2),(0,0,2),(0,4,2),(0,1,2),(3,7,3)]
def W_10 : BT Decor := buildWiresBT 4 base_10 steps_10
def autosL_10 : List (List (Nat × Nat)) := [[],[(4,5)],[(1,2)],[(4,5),(1,2)],[(2,4)],[(2,5),(2,4)],[(1,2),(1,4)],[(2,5),(1,2),(1,4)],[(2,5),(1,4)]]
def autos_10 : BT (List (Nat × Nat)) := btOfList 4 autosL_10
def slicesL_10 : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 32,4)]
def slices_10 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_10
def ps_10 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_10 : BT (Option BoundPool) := buildPoolsBT 2 W_10 R_10 slices_10 ps_10
lemma gp_10 : goodPairs G_10 pos_10 neg_10 := goodPairs_of (by decide +kernel)
lemma base_10_ok : ∀ x ∈ base_10, faithful pos_10 neg_10 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_10_ok : btAll (fun x => faithful pos_10 neg_10 x ∧ x.1 < 2^128) W_10 := buildWiresBT_faithful base_10_ok
set_option maxRecDepth 500000 in
lemma autos_10_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_10 = G_10) autos_10 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_10_0_ok : sliceDirectCheck 0 16 0 R_10 G_10 R_7 G_7 = true := by decide +kernel
lemma sl_10_0 : Slice R_10 G_10 (subcubeFast 0 16) 4 := slice_fast_direct sl_10_0_ok low_7
lemma sl_10_1_ok : sliceDirectCheck 0 2 0 R_10 G_10 R_0 G_0 = true := by decide +kernel
lemma sl_10_1 : Slice R_10 G_10 (subcubeFast 0 2) 4 := slice_fast_direct sl_10_1_ok low_0
lemma sl_10_2_ok : sliceDirectCheck 0 4 0 R_10 G_10 R_9 G_9 = true := by decide +kernel
lemma sl_10_2 : Slice R_10 G_10 (subcubeFast 0 4) 4 := slice_fast_direct sl_10_2_ok low_9
lemma sl_10_3_ok : sliceDirectCheck 0 32 0 R_10 G_10 R_6 G_6 = true := by decide +kernel
lemma sl_10_3 : Slice R_10 G_10 (subcubeFast 0 32) 4 := slice_fast_direct sl_10_3_ok low_6
set_option maxRecDepth 500000 in
lemma slices_10_ok : btAll (fun o => ∀ p, o = some p → Slice R_10 G_10 p.1 p.2) slices_10 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_10 G_10 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_10_0) (forall_cons (fun _ h => by cases h; exact sl_10_1) (forall_cons (fun _ h => by cases h; exact sl_10_2) (forall_cons (fun _ h => by cases h; exact sl_10_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_10_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_10 G_10 c) P_10 := buildPoolsBT_sound slices_10_ok
def bk_10_init : BT (List (List Nat)) := BT.empty
lemma bk_10_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 (0 - 1) xs.toFinset) bk_10_init := trivial
def nodes_10_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_0 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_init 0 nodes_10_0 = true := by decide +kernel
def bk_10_0 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_0
set_option maxRecDepth 500000 in
lemma bk_10_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 0 xs.toFinset) bk_10_0 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_init_ok chk_10_0
def nodes_10_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_1 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_0 1 nodes_10_1 = true := by decide +kernel
def bk_10_1 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_1
set_option maxRecDepth 500000 in
lemma bk_10_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 1 xs.toFinset) bk_10_1 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_0_ok chk_10_1
def nodes_10_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_2 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_1 2 nodes_10_2 = true := by decide +kernel
def bk_10_2 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_2
set_option maxRecDepth 500000 in
lemma bk_10_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 2 xs.toFinset) bk_10_2 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_1_ok chk_10_2
def nodes_10_3 : List NodeSpec := [([4,6,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_3 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_2 3 nodes_10_3 = true := by decide +kernel
def bk_10_3 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_3
set_option maxRecDepth 500000 in
lemma bk_10_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 3 xs.toFinset) bk_10_3 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_2_ok chk_10_3
def nodes_10_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([4,6,1,2,3],[0,2],[0]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_4 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_3 4 nodes_10_4 = true := by decide +kernel
def bk_10_4 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_4
set_option maxRecDepth 500000 in
lemma bk_10_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 4 xs.toFinset) bk_10_4 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_3_ok chk_10_4
def nodes_10_5 : List NodeSpec := [([4,0,1,2,3],[2,1,0,3],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_5 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_4 5 nodes_10_5 = true := by decide +kernel
def bk_10_5 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_5
set_option maxRecDepth 500000 in
lemma bk_10_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 5 xs.toFinset) bk_10_5 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_4_ok chk_10_5
def nodes_10_6 : List NodeSpec := [([0,1,2,3],[1,2,0,3],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_6 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_5 6 nodes_10_6 = true := by decide +kernel
def bk_10_6 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_6
set_option maxRecDepth 500000 in
lemma bk_10_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 6 xs.toFinset) bk_10_6 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_5_ok chk_10_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_ok : forestRootCheck R_10 G_10 [(VAR 1,22,20),(VAR 2,22,18),(VAR 4,22,6),(VAR 5,38,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_in : bucketContainsBT bk_10_6 R_10 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_10 : Lower R_10 G_10 7 := lower_of_forestBT root_10_ok bk_10_6_ok root_10_in
def G_11 : Nat := 0xff00f000f0000000ff00f000f0000000
def R_11 : List Nat := varsOf 60
lemma low_11_ok : liftCheck 0 8 R_11 G_11 R_0 G_0 [(VAR 3,28,20)] = true := by decide +kernel
lemma low_11 : Lower R_11 G_11 5 := lift_of low_11_ok low_0
def G_12 : Nat := 0xfff0ff00ff00f000fff0ff00ff00f000
def R_12 : List Nat := varsOf 60
def pos_12 : List Nat := [12,12,24,24,28,40,40,44,52,52,52,56,12,12,12,24,24,24,40,40,40,52]
def neg_12 : List Nat := [8,4,16,8,20,32,8,36,48,36,20,48,20,36,48,20,36,48,20,36,48,8]
def fmask_12 : Nat := fullMask 22
def base_12 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x207793,0xdb692),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1ff8ff,0x200049),(0xffff0000ffff0000ffff0000ffff0000,0x238f1c,0x16dd14),(0xffffffff00000000ffffffff00000000,0x3c0fe0,0x1b6ba0)]
def steps_12 : List (Nat × Nat × Nat) := [(2,0,2),(1,0,2),(2,0,1),(0,0,2),(3,0,1),(1,0,1),(0,0,1),(3,0,2),(3,4,3),(2,9,2),(0,9,2),(1,4,3),(3,10,2),(1,10,2),(3,7,5)]
def W_12 : BT Decor := buildWiresBT 5 base_12 steps_12
def autosL_12 : List (List (Nat × Nat)) := [[],[(4,5)],[(2,4)],[(2,5),(2,4)],[(2,4),(2,5)],[(2,5)]]
def autos_12 : BT (List (Nat × Nat)) := btOfList 3 autosL_12
def slicesL_12 : List (Option (Nat × Nat)) := []
def slices_12 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_12
def ps_12 : List PoolSpec := []
def P_12 : BT (Option BoundPool) := buildPoolsBT 1 W_12 R_12 slices_12 ps_12
lemma gp_12 : goodPairs G_12 pos_12 neg_12 := goodPairs_of (by decide +kernel)
lemma base_12_ok : ∀ x ∈ base_12, faithful pos_12 neg_12 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_12_ok : btAll (fun x => faithful pos_12 neg_12 x ∧ x.1 < 2^128) W_12 := buildWiresBT_faithful base_12_ok
set_option maxRecDepth 500000 in
lemma autos_12_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_12 = G_12) autos_12 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_12_ok : btAll (fun o => ∀ p, o = some p → Slice R_12 G_12 p.1 p.2) slices_12 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_12 G_12 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_12_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_12 G_12 c) P_12 := buildPoolsBT_sound slices_12_ok
def bk_12_init : BT (List (List Nat)) := BT.empty
lemma bk_12_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 (0 - 1) xs.toFinset) bk_12_init := trivial
def nodes_12_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_0 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_init 0 nodes_12_0 = true := by decide +kernel
def bk_12_0 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_0
set_option maxRecDepth 500000 in
lemma bk_12_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 0 xs.toFinset) bk_12_0 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_init_ok chk_12_0
def nodes_12_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_1 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_0 1 nodes_12_1 = true := by decide +kernel
def bk_12_1 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_1
set_option maxRecDepth 500000 in
lemma bk_12_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 1 xs.toFinset) bk_12_1 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_0_ok chk_12_1
def nodes_12_2 : List NodeSpec := [([18,1,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_2 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_1 2 nodes_12_2 = true := by decide +kernel
def bk_12_2 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_2
set_option maxRecDepth 500000 in
lemma bk_12_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 2 xs.toFinset) bk_12_2 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_1_ok chk_12_2
def nodes_12_3 : List NodeSpec := [([4,11,1,3],[],[0]),([0,1,2,12],[],[]),([7,1,5,3],[],[0]),([13,0,1,3],[],[]),([0,1,14,3],[],[]),([6,8,2,3],[],[]),([0,1,2,15],[],[]),([16,0,1,3],[],[]),([0,1,17,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_3 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_2 3 nodes_12_3 = true := by decide +kernel
def bk_12_3 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_3
set_option maxRecDepth 500000 in
lemma bk_12_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 3 xs.toFinset) bk_12_3 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_2_ok chk_12_3
def nodes_12_4 : List NodeSpec := [([4,0,1,2,3],[],[0]),([0,1,2,5,3],[],[0]),([6,0,1,2,3],[],[0]),([7,0,1,2,3],[],[0]),([8,0,1,2,3],[],[0]),([0,1,9,2,3],[],[0,1]),([10,0,1,2,3],[],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_4 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_3 4 nodes_12_4 = true := by decide +kernel
def bk_12_4 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_4
set_option maxRecDepth 500000 in
lemma bk_12_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 4 xs.toFinset) bk_12_4 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_3_ok chk_12_4
def nodes_12_5 : List NodeSpec := [([0,1,2,3],[],[0,2,1,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_5 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_4 5 nodes_12_5 = true := by decide +kernel
def bk_12_5 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_5
set_option maxRecDepth 500000 in
lemma bk_12_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 5 xs.toFinset) bk_12_5 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_4_ok chk_12_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_ok : forestRootCheck R_12 G_12 [(VAR 2,12,8),(VAR 3,12,4),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_in : bucketContainsBT bk_12_5 R_12 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_12 : Lower R_12 G_12 6 := lower_of_forestBT root_12_ok bk_12_5_ok root_12_in
def G_13 : Nat := 0xfffffcfcfcfcc0c0fffffcfcfcfcc0c0
def R_13 : List Nat := varsOf 54
def pos_13 : List Nat := [6,6,18,18,20,20,34,34,36,36,48,48,6,6,18,18,20,20,34,34,36,36,48,48]
def neg_13 : List Nat := [4,2,16,2,16,4,32,2,32,4,32,16,16,32,4,32,2,32,4,16,2,16,2,4]
def fmask_13 : Nat := fullMask 24
def base_13 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf0cf,0x51008a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x333333,0x844221),(0xffff0000ffff0000ffff0000ffff0000,0xc3cc3c,0x281814),(0xffffffff00000000ffffffff00000000,0xfc0fc0,0x2a540)]
def steps_13 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def W_13 : BT Decor := buildWiresBT 4 base_13 steps_13
def autosL_13 : List (List (Nat × Nat)) := [[],[(4,5)],[(1,2)],[(4,5),(1,2)],[(2,4)],[(2,5),(2,4)],[(1,2),(1,4)],[(2,5),(1,2),(1,4)],[(2,5),(1,4)]]
def autos_13 : BT (List (Nat × Nat)) := btOfList 4 autosL_13
def slicesL_13 : List (Option (Nat × Nat)) := [some (subcubeFast 4 0,4),some (subcubeFast 2 0,4),some (subcubeFast 32 0,4),some (subcubeFast 16 0,4)]
def slices_13 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_13
def ps_13 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_13 : BT (Option BoundPool) := buildPoolsBT 2 W_13 R_13 slices_13 ps_13
lemma gp_13 : goodPairs G_13 pos_13 neg_13 := goodPairs_of (by decide +kernel)
lemma base_13_ok : ∀ x ∈ base_13, faithful pos_13 neg_13 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_13_ok : btAll (fun x => faithful pos_13 neg_13 x ∧ x.1 < 2^128) W_13 := buildWiresBT_faithful base_13_ok
set_option maxRecDepth 500000 in
lemma autos_13_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_13 = G_13) autos_13 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_13_0_ok : sliceDirectCheck 4 0 0 R_13 G_13 R_9 G_9 = true := by decide +kernel
lemma sl_13_0 : Slice R_13 G_13 (subcubeFast 4 0) 4 := slice_fast_direct sl_13_0_ok low_9
lemma sl_13_1_ok : sliceDirectCheck 2 0 0 R_13 G_13 R_0 G_0 = true := by decide +kernel
lemma sl_13_1 : Slice R_13 G_13 (subcubeFast 2 0) 4 := slice_fast_direct sl_13_1_ok low_0
lemma sl_13_2_ok : sliceDirectCheck 32 0 0 R_13 G_13 R_6 G_6 = true := by decide +kernel
lemma sl_13_2 : Slice R_13 G_13 (subcubeFast 32 0) 4 := slice_fast_direct sl_13_2_ok low_6
lemma sl_13_3_ok : sliceDirectCheck 16 0 0 R_13 G_13 R_7 G_7 = true := by decide +kernel
lemma sl_13_3 : Slice R_13 G_13 (subcubeFast 16 0) 4 := slice_fast_direct sl_13_3_ok low_7
set_option maxRecDepth 500000 in
lemma slices_13_ok : btAll (fun o => ∀ p, o = some p → Slice R_13 G_13 p.1 p.2) slices_13 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_13 G_13 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_13_0) (forall_cons (fun _ h => by cases h; exact sl_13_1) (forall_cons (fun _ h => by cases h; exact sl_13_2) (forall_cons (fun _ h => by cases h; exact sl_13_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_13_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_13 G_13 c) P_13 := buildPoolsBT_sound slices_13_ok
def bk_13_init : BT (List (List Nat)) := BT.empty
lemma bk_13_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 (0 - 1) xs.toFinset) bk_13_init := trivial
def nodes_13_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_0 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_init 0 nodes_13_0 = true := by decide +kernel
def bk_13_0 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_0
set_option maxRecDepth 500000 in
lemma bk_13_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 0 xs.toFinset) bk_13_0 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_init_ok chk_13_0
def nodes_13_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_1 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_0 1 nodes_13_1 = true := by decide +kernel
def bk_13_1 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_1
set_option maxRecDepth 500000 in
lemma bk_13_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 1 xs.toFinset) bk_13_1 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_0_ok chk_13_1
def nodes_13_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_2 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_1 2 nodes_13_2 = true := by decide +kernel
def bk_13_2 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_2
set_option maxRecDepth 500000 in
lemma bk_13_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 2 xs.toFinset) bk_13_2 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_1_ok chk_13_2
def nodes_13_3 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_3 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_2 3 nodes_13_3 = true := by decide +kernel
def bk_13_3 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_3
set_option maxRecDepth 500000 in
lemma bk_13_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 3 xs.toFinset) bk_13_3 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_2_ok chk_13_3
def nodes_13_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_4 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_3 4 nodes_13_4 = true := by decide +kernel
def bk_13_4 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_4
set_option maxRecDepth 500000 in
lemma bk_13_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 4 xs.toFinset) bk_13_4 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_3_ok chk_13_4
def nodes_13_5 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_5 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_4 5 nodes_13_5 = true := by decide +kernel
def bk_13_5 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_5
set_option maxRecDepth 500000 in
lemma bk_13_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 5 xs.toFinset) bk_13_5 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_4_ok chk_13_5
def nodes_13_6 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_6 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_5 6 nodes_13_6 = true := by decide +kernel
def bk_13_6 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_6
set_option maxRecDepth 500000 in
lemma bk_13_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 6 xs.toFinset) bk_13_6 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_5_ok chk_13_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_ok : forestRootCheck R_13 G_13 [(VAR 1,6,4),(VAR 2,6,2),(VAR 4,18,2),(VAR 5,34,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_in : bucketContainsBT bk_13_6 R_13 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_13 : Lower R_13 G_13 7 := lower_of_forestBT root_13_ok bk_13_6_ok root_13_in
def G_14 : Nat := 0xe800e800e800e800e800e800e800e800
def R_14 : List Nat := varsOf 15
lemma low_14_ok : carryOK [(0,1),(0,5),(1,4),(0,2)] R_14 G_14 R_11 G_11 = true := by decide +kernel
lemma low_14 : Lower R_14 G_14 5 := carry_of low_14_ok low_11
def G_15 : Nat := 0xe8e88080e8e88080e8e88080e8e88080
def R_15 : List Nat := varsOf 23
lemma low_15_ok : carryOK [(3,5),(0,3),(0,4),(0,2),(0,1)] R_15 G_15 R_10 G_10 = true := by decide +kernel
lemma low_15 : Lower R_15 G_15 7 := carry_of low_15_ok low_10
def G_16 : Nat := 0xe8e8e8e880808080e8e8e8e880808080
def R_16 : List Nat := varsOf 39
lemma low_16_ok : carryOK [(0,3),(0,4),(0,2),(0,1)] R_16 G_16 R_10 G_10 = true := by decide +kernel
lemma low_16 : Lower R_16 G_16 7 := carry_of low_16_ok low_10
def G_17 : Nat := 0xee008800ee008800ee008800ee008800
def R_17 : List Nat := varsOf 27
lemma low_17_ok : carryOK [(1,5),(1,4),(0,2)] R_17 G_17 R_11 G_11 = true := by decide +kernel
lemma low_17 : Lower R_17 G_17 5 := carry_of low_17_ok low_11
def G_18 : Nat := 0xee00ee0088008800ee00ee0088008800
def R_18 : List Nat := varsOf 43
lemma low_18_ok : carryOK [(1,4),(0,2)] R_18 G_18 R_11 G_11 = true := by decide +kernel
lemma low_18 : Lower R_18 G_18 5 := carry_of low_18_ok low_11
def G_19 : Nat := 0xeeee888888880000eeee888888880000
def R_19 : List Nat := varsOf 51
lemma low_19_ok : carryOK [(0,2),(0,1)] R_19 G_19 R_10 G_10 = true := by decide +kernel
lemma low_19 : Lower R_19 G_19 7 := carry_of low_19_ok low_10
def G_20 : Nat := 0xfa00a000fa00a000fa00a000fa00a000
def R_20 : List Nat := varsOf 29
lemma low_20_ok : carryOK [(1,5),(1,4),(0,1),(0,2)] R_20 G_20 R_11 G_11 = true := by decide +kernel
lemma low_20 : Lower R_20 G_20 5 := carry_of low_20_ok low_11
def G_21 : Nat := 0xfa00fa00a000a000fa00fa00a000a000
def R_21 : List Nat := varsOf 45
lemma low_21_ok : carryOK [(1,4),(0,1),(0,2)] R_21 G_21 R_11 G_11 = true := by decide +kernel
lemma low_21 : Lower R_21 G_21 5 := carry_of low_21_ok low_11
def G_22 : Nat := 0xfafaa0a0a0a00000fafaa0a0a0a00000
def R_22 : List Nat := varsOf 53
lemma low_22_ok : carryOK [(0,1)] R_22 G_22 R_10 G_10 = true := by decide +kernel
lemma low_22 : Lower R_22 G_22 7 := carry_of low_22_ok low_10
def G_23 : Nat := 0xfc00c000fc00c000fc00c000fc00c000
def R_23 : List Nat := varsOf 30
lemma low_23_ok : carryOK [(1,5),(1,4),(1,2)] R_23 G_23 R_11 G_11 = true := by decide +kernel
lemma low_23 : Lower R_23 G_23 5 := carry_of low_23_ok low_11
def G_24 : Nat := 0xfc00fc00c000c000fc00fc00c000c000
def R_24 : List Nat := varsOf 46
lemma low_24_ok : carryOK [(1,4),(1,2)] R_24 G_24 R_11 G_11 = true := by decide +kernel
lemma low_24 : Lower R_24 G_24 5 := carry_of low_24_ok low_11
def G_25 : Nat := 0xfe80fe80fe80fe80fe80fe80fe80fe80
def R_25 : List Nat := varsOf 15
lemma low_25_ok : carryOK [(0,1),(0,5),(1,4),(0,2)] R_25 G_25 R_12 G_12 = true := by decide +kernel
lemma low_25 : Lower R_25 G_25 6 := carry_of low_25_ok low_12
def G_26 : Nat := 0xfefee8e8fefee8e8fefee8e8fefee8e8
def R_26 : List Nat := varsOf 23
lemma low_26_ok : carryOK [(3,5),(0,3),(0,4),(0,2),(0,1)] R_26 G_26 R_13 G_13 = true := by decide +kernel
lemma low_26 : Lower R_26 G_26 7 := carry_of low_26_ok low_13
def G_27 : Nat := 0xfefefefee8e8e8e8fefefefee8e8e8e8
def R_27 : List Nat := varsOf 39
lemma low_27_ok : carryOK [(0,3),(0,4),(0,2),(0,1)] R_27 G_27 R_13 G_13 = true := by decide +kernel
lemma low_27 : Lower R_27 G_27 7 := carry_of low_27_ok low_13
def G_28 : Nat := 0xff00aa00aa000000ff00aa00aa000000
def R_28 : List Nat := varsOf 57
lemma low_28_ok : carryOK [(0,1),(0,2)] R_28 G_28 R_11 G_11 = true := by decide +kernel
lemma low_28 : Lower R_28 G_28 5 := carry_of low_28_ok low_11
def G_29 : Nat := 0xff00cc00cc000000ff00cc00cc000000
def R_29 : List Nat := varsOf 58
lemma low_29_ok : carryOK [(1,2)] R_29 G_29 R_11 G_11 = true := by decide +kernel
lemma low_29 : Lower R_29 G_29 5 := carry_of low_29_ok low_11
def G_30 : Nat := 0xff88ee00ff88ee00ff88ee00ff88ee00
def R_30 : List Nat := varsOf 27
lemma low_30_ok : carryOK [(1,5),(1,4),(0,2)] R_30 G_30 R_12 G_12 = true := by decide +kernel
lemma low_30 : Lower R_30 G_30 6 := carry_of low_30_ok low_12
def G_31 : Nat := 0xff88ff88ee00ee00ff88ff88ee00ee00
def R_31 : List Nat := varsOf 43
lemma low_31_ok : carryOK [(1,4),(0,2)] R_31 G_31 R_12 G_12 = true := by decide +kernel
lemma low_31 : Lower R_31 G_31 6 := carry_of low_31_ok low_12
def G_32 : Nat := 0xffa0fa00ffa0fa00ffa0fa00ffa0fa00
def R_32 : List Nat := varsOf 29
lemma low_32_ok : carryOK [(1,5),(1,4),(0,1),(0,2)] R_32 G_32 R_12 G_12 = true := by decide +kernel
lemma low_32 : Lower R_32 G_32 6 := carry_of low_32_ok low_12
def G_33 : Nat := 0xffa0ffa0fa00fa00ffa0ffa0fa00fa00
def R_33 : List Nat := varsOf 45
lemma low_33_ok : carryOK [(1,4),(0,1),(0,2)] R_33 G_33 R_12 G_12 = true := by decide +kernel
lemma low_33 : Lower R_33 G_33 6 := carry_of low_33_ok low_12
def G_34 : Nat := 0xffaaff00ff00aa00ffaaff00ff00aa00
def R_34 : List Nat := varsOf 57
lemma low_34_ok : carryOK [(0,1),(0,2)] R_34 G_34 R_12 G_12 = true := by decide +kernel
lemma low_34 : Lower R_34 G_34 6 := carry_of low_34_ok low_12
def G_35 : Nat := 0xffc0fc00ffc0fc00ffc0fc00ffc0fc00
def R_35 : List Nat := varsOf 30
lemma low_35_ok : carryOK [(1,5),(1,4),(1,2)] R_35 G_35 R_12 G_12 = true := by decide +kernel
lemma low_35 : Lower R_35 G_35 6 := carry_of low_35_ok low_12
def G_36 : Nat := 0xffc0ffc0fc00fc00ffc0ffc0fc00fc00
def R_36 : List Nat := varsOf 46
lemma low_36_ok : carryOK [(1,4),(1,2)] R_36 G_36 R_12 G_12 = true := by decide +kernel
lemma low_36 : Lower R_36 G_36 6 := carry_of low_36_ok low_12
def G_37 : Nat := 0xffccff00ff00cc00ffccff00ff00cc00
def R_37 : List Nat := varsOf 58
lemma low_37_ok : carryOK [(1,2)] R_37 G_37 R_12 G_12 = true := by decide +kernel
lemma low_37 : Lower R_37 G_37 6 := carry_of low_37_ok low_12
def G_38 : Nat := 0xffffeeeeeeee8888ffffeeeeeeee8888
def R_38 : List Nat := varsOf 51
lemma low_38_ok : carryOK [(0,2),(0,1)] R_38 G_38 R_13 G_13 = true := by decide +kernel
lemma low_38 : Lower R_38 G_38 7 := carry_of low_38_ok low_13
def G_39 : Nat := 0xfffffafafafaa0a0fffffafafafaa0a0
def R_39 : List Nat := varsOf 53
lemma low_39_ok : carryOK [(0,1)] R_39 G_39 R_13 G_13 = true := by decide +kernel
lemma low_39 : Lower R_39 G_39 7 := carry_of low_39_ok low_13
def G_40 : Nat := 0xfc00c000c0000000fc00c000c0000000
def R_40 : List Nat := varsOf 62
lemma low_40_ok : liftCheck 0 8 R_40 G_40 R_10 G_10 [(VAR 3,30,22)] = true := by decide +kernel
lemma low_40 : Lower R_40 G_40 8 := lift_of low_40_ok low_10
def G_41 : Nat := 0xfefee8e8e8e88080fefee8e8e8e88080
def R_41 : List Nat := varsOf 55
def pos_41 : List Nat := [7,7,7,19,19,19,21,21,21,22,22,22,35,35,35,37,37,37,38,38,38,49,49,49,50,50,50,52,52,52,7,7,7,7,7,7,7,19,19,19,19,19,19,19,21,21,21,21,21,21,21,22,22,22,22,22,22,22,35,35,35,35,35,35,35,37,37,37,37,37,37,37,38,38,38,38,38,38,38,49,49,49,49,49,49,49,50,50,50,50,50,50,50,52,52,52,52,52,52,52]
def neg_41 : List Nat := [6,5,3,18,17,3,20,17,5,20,18,6,34,33,3,36,33,5,36,34,6,48,33,17,48,34,18,48,36,20,17,18,20,33,34,36,48,5,6,20,33,34,36,48,3,6,18,33,34,36,48,3,5,17,33,34,36,48,5,6,17,18,20,36,48,3,6,17,18,20,34,48,3,5,17,18,20,33,48,3,5,6,18,20,34,36,3,5,6,17,20,33,36,3,5,6,17,18,33,34]
def fmask_41 : Nat := fullMask 100
def base_41 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3f80fffc07ffffc0e3f1ff,0x56ac1a70a1478912240c361b6),(0xcccccccccccccccccccccccccccccccc,0x1fc07f01fff80fffc71c7e3f,0xaa15689562889724486185c2d),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfe0007ffe03fff01ff81f8fc7,0xd5ab1224cd1224e930168b43),(0xffff0000ffff0000ffff0000ffff0000,0xfffff800003ffffe03fe00ff8,0x3060c5cb972244891eda006d8),(0xffffffff00000000ffffffff00000000,0xffffffffffc0000003ffff000,0xc183060c183c78f1e1b6db000)]
def steps_41 : List (Nat × Nat × Nat) := []
def W_41 : BT Decor := buildWiresBT 3 base_41 steps_41
def autosL_41 : List (List (Nat × Nat)) := []
def autos_41 : BT (List (Nat × Nat)) := btOfList 1 autosL_41
def slicesL_41 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,7),some (subcubeFast 0 1,7),some (subcubeFast 1 0,7),some (subcubeFast 0 2,7),some (subcubeFast 16 0,7),some (subcubeFast 0 16,7),some (subcubeFast 32 0,7),some (subcubeFast 0 32,7)]
def slices_41 : BT (Option (Nat × Nat)) := btOfList 3 slicesL_41
def ps_41 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[])]
def P_41 : BT (Option BoundPool) := buildPoolsBT 3 W_41 R_41 slices_41 ps_41
lemma gp_41 : goodPairs G_41 pos_41 neg_41 := goodPairs_of (by decide +kernel)
lemma base_41_ok : ∀ x ∈ base_41, faithful pos_41 neg_41 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_41_ok : btAll (fun x => faithful pos_41 neg_41 x ∧ x.1 < 2^128) W_41 := buildWiresBT_faithful base_41_ok
set_option maxRecDepth 500000 in
lemma autos_41_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_41 = G_41) autos_41 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_41_0_ok : sliceDirectCheck 2 0 0 R_41 G_41 R_22 G_22 = true := by decide +kernel
lemma sl_41_0 : Slice R_41 G_41 (subcubeFast 2 0) 7 := slice_fast_direct sl_41_0_ok low_22
lemma sl_41_1_ok : sliceDirectCheck 0 1 0 R_41 G_41 R_13 G_13 = true := by decide +kernel
lemma sl_41_1 : Slice R_41 G_41 (subcubeFast 0 1) 7 := slice_fast_direct sl_41_1_ok low_13
lemma sl_41_2_ok : sliceDirectCheck 1 0 0 R_41 G_41 R_10 G_10 = true := by decide +kernel
lemma sl_41_2 : Slice R_41 G_41 (subcubeFast 1 0) 7 := slice_fast_direct sl_41_2_ok low_10
lemma sl_41_3_ok : sliceDirectCheck 0 2 0 R_41 G_41 R_39 G_39 = true := by decide +kernel
lemma sl_41_3 : Slice R_41 G_41 (subcubeFast 0 2) 7 := slice_fast_direct sl_41_3_ok low_39
lemma sl_41_4_ok : sliceDirectCheck 16 0 0 R_41 G_41 R_16 G_16 = true := by decide +kernel
lemma sl_41_4 : Slice R_41 G_41 (subcubeFast 16 0) 7 := slice_fast_direct sl_41_4_ok low_16
lemma sl_41_5_ok : sliceDirectCheck 0 16 0 R_41 G_41 R_27 G_27 = true := by decide +kernel
lemma sl_41_5 : Slice R_41 G_41 (subcubeFast 0 16) 7 := slice_fast_direct sl_41_5_ok low_27
lemma sl_41_6_ok : sliceDirectCheck 32 0 0 R_41 G_41 R_15 G_15 = true := by decide +kernel
lemma sl_41_6 : Slice R_41 G_41 (subcubeFast 32 0) 7 := slice_fast_direct sl_41_6_ok low_15
lemma sl_41_7_ok : sliceDirectCheck 0 32 0 R_41 G_41 R_26 G_26 = true := by decide +kernel
lemma sl_41_7 : Slice R_41 G_41 (subcubeFast 0 32) 7 := slice_fast_direct sl_41_7_ok low_26
set_option maxRecDepth 500000 in
lemma slices_41_ok : btAll (fun o => ∀ p, o = some p → Slice R_41 G_41 p.1 p.2) slices_41 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_41 G_41 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_41_0) (forall_cons (fun _ h => by cases h; exact sl_41_1) (forall_cons (fun _ h => by cases h; exact sl_41_2) (forall_cons (fun _ h => by cases h; exact sl_41_3) (forall_cons (fun _ h => by cases h; exact sl_41_4) (forall_cons (fun _ h => by cases h; exact sl_41_5) (forall_cons (fun _ h => by cases h; exact sl_41_6) (forall_cons (fun _ h => by cases h; exact sl_41_7) (fun _ h => (List.not_mem_nil h).elim)))))))))
set_option maxRecDepth 500000 in
lemma P_41_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_41 G_41 c) P_41 := buildPoolsBT_sound slices_41_ok
def bk_41_init : BT (List (List Nat)) := BT.empty
lemma bk_41_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 (0 - 1) xs.toFinset) bk_41_init := trivial
def nodes_41_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_0 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_init 0 nodes_41_0 = true := by decide +kernel
def bk_41_0 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_0
set_option maxRecDepth 500000 in
lemma bk_41_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 0 xs.toFinset) bk_41_0 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_init_ok chk_41_0
def nodes_41_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_1 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_0 1 nodes_41_1 = true := by decide +kernel
def bk_41_1 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_1
set_option maxRecDepth 500000 in
lemma bk_41_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 1 xs.toFinset) bk_41_1 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_0_ok chk_41_1
def nodes_41_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_2 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_1 2 nodes_41_2 = true := by decide +kernel
def bk_41_2 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_2
set_option maxRecDepth 500000 in
lemma bk_41_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 2 xs.toFinset) bk_41_2 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_1_ok chk_41_2
def nodes_41_3 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_3 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_2 3 nodes_41_3 = true := by decide +kernel
def bk_41_3 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_3
set_option maxRecDepth 500000 in
lemma bk_41_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 3 xs.toFinset) bk_41_3 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_2_ok chk_41_3
def nodes_41_4 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_4 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_3 4 nodes_41_4 = true := by decide +kernel
def bk_41_4 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_4
set_option maxRecDepth 500000 in
lemma bk_41_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 4 xs.toFinset) bk_41_4 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_3_ok chk_41_4
def nodes_41_5 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_5 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_4 5 nodes_41_5 = true := by decide +kernel
def bk_41_5 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_5
set_option maxRecDepth 500000 in
lemma bk_41_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 5 xs.toFinset) bk_41_5 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_4_ok chk_41_5
def nodes_41_6 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_6 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_5 6 nodes_41_6 = true := by decide +kernel
def bk_41_6 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_6
set_option maxRecDepth 500000 in
lemma bk_41_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 6 xs.toFinset) bk_41_6 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_5_ok chk_41_6
def nodes_41_7 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_7 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_6 7 nodes_41_7 = true := by decide +kernel
def bk_41_7 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_7
set_option maxRecDepth 500000 in
lemma bk_41_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 7 xs.toFinset) bk_41_7 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_6_ok chk_41_7
def nodes_41_8 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_8 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_7 8 nodes_41_8 = true := by decide +kernel
def bk_41_8 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_8
set_option maxRecDepth 500000 in
lemma bk_41_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 8 xs.toFinset) bk_41_8 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_7_ok chk_41_8
def nodes_41_9 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,4,5,6,7],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_9 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_8 9 nodes_41_9 = true := by decide +kernel
def bk_41_9 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_9
set_option maxRecDepth 500000 in
lemma bk_41_9_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 9 xs.toFinset) bk_41_9 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_8_ok chk_41_9
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_41_ok : forestRootCheck R_41 G_41 [(VAR 0,7,6),(VAR 1,7,5),(VAR 2,7,3),(VAR 4,19,3),(VAR 5,35,3)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_41_in : bucketContainsBT bk_41_9 R_41 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_41 : Lower R_41 G_41 10 := lower_of_forestBT root_41_ok bk_41_9_ok root_41_in
def G_42 : Nat := 0xffc0fc00fc00c000ffc0fc00fc00c000
def R_42 : List Nat := varsOf 62
def pos_42 : List Nat := [14,14,14,26,26,26,28,28,28,30,42,42,42,44,44,44,46,54,54,54,54,56,56,56,58,60,14,14,14,14,14,14,26,26,26,26,26,26,28,28,28,28,28,28,42,42,42,42,42,42,44,44,44,44,44,44,54,54,54,54,56,56,56,56,56,56]
def neg_42 : List Nat := [12,10,6,24,18,10,24,20,12,22,40,34,10,40,36,12,38,52,50,38,22,48,40,24,50,52,22,24,38,40,50,52,12,22,38,40,50,52,10,22,38,40,50,52,12,22,24,38,50,52,10,22,24,38,50,52,10,12,24,40,10,12,22,38,50,52]
def fmask_42 : Nat := fullMask 66
def base_42 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xf03f03ffd1f1e3f,0x1d16da5d6551d1a36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffc0fc0fe1fe3c7,0x2e2aab9a7961bc385),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3f0ffffffffe1ffff,0x3f14524928c0b56b),(0xffff0000ffff0000ffff0000ffff0000,0x3ff000fff03fe03f8,0x344db6cb2cfb602d8),(0xffffffff00000000ffffffff00000000,0x3fffff00003fffc00,0x388e38f3cf36f6c00)]
def steps_42 : List (Nat × Nat × Nat) := [(0,0,1),(0,3,4),(1,5,6)]
def W_42 : BT Decor := buildWiresBT 3 base_42 steps_42
def autosL_42 : List (List (Nat × Nat)) := [[],[(2,4)],[(2,5),(2,4)],[(1,2),(1,4)],[(2,5),(1,2),(1,4)],[(2,5),(1,4)]]
def autos_42 : BT (List (Nat × Nat)) := btOfList 3 autosL_42
def slicesL_42 : List (Option (Nat × Nat)) := [some (subcubeFast 4 0,5),some (subcubeFast 32 0,5),some (subcubeFast 0 16,6),some (subcubeFast 16 0,5),some (subcubeFast 0 32,6),some (subcubeFast 0 2,6),some (subcubeFast 2 0,5),some (subcubeFast 0 4,6),some (subcubeFast 0 8,7),some (subcubeFast 4 8,4)]
def slices_42 : BT (Option (Nat × Nat)) := btOfList 4 slicesL_42
def ps_42 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[(0,3,4)]),(6,[]),(7,[]),(4,[(0,0,1)]),(5,[]),(8,[]),(9,[]),(2,[(0,0,1)])]
def P_42 : BT (Option BoundPool) := buildPoolsBT 4 W_42 R_42 slices_42 ps_42
lemma gp_42 : goodPairs G_42 pos_42 neg_42 := goodPairs_of (by decide +kernel)
lemma base_42_ok : ∀ x ∈ base_42, faithful pos_42 neg_42 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_42_ok : btAll (fun x => faithful pos_42 neg_42 x ∧ x.1 < 2^128) W_42 := buildWiresBT_faithful base_42_ok
set_option maxRecDepth 500000 in
lemma autos_42_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_42 = G_42) autos_42 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_42_0_ok : sliceDirectCheck 4 0 0 R_42 G_42 R_29 G_29 = true := by decide +kernel
lemma sl_42_0 : Slice R_42 G_42 (subcubeFast 4 0) 5 := slice_fast_direct sl_42_0_ok low_29
lemma sl_42_1_ok : sliceDirectCheck 32 0 0 R_42 G_42 R_23 G_23 = true := by decide +kernel
lemma sl_42_1 : Slice R_42 G_42 (subcubeFast 32 0) 5 := slice_fast_direct sl_42_1_ok low_23
lemma sl_42_2_ok : sliceDirectCheck 0 16 0 R_42 G_42 R_36 G_36 = true := by decide +kernel
lemma sl_42_2 : Slice R_42 G_42 (subcubeFast 0 16) 6 := slice_fast_direct sl_42_2_ok low_36
lemma sl_42_3_ok : sliceDirectCheck 16 0 0 R_42 G_42 R_24 G_24 = true := by decide +kernel
lemma sl_42_3 : Slice R_42 G_42 (subcubeFast 16 0) 5 := slice_fast_direct sl_42_3_ok low_24
lemma sl_42_4_ok : sliceDirectCheck 0 32 0 R_42 G_42 R_35 G_35 = true := by decide +kernel
lemma sl_42_4 : Slice R_42 G_42 (subcubeFast 0 32) 6 := slice_fast_direct sl_42_4_ok low_35
lemma sl_42_5_ok : sliceDirectCheck 0 2 0 R_42 G_42 R_12 G_12 = true := by decide +kernel
lemma sl_42_5 : Slice R_42 G_42 (subcubeFast 0 2) 6 := slice_fast_direct sl_42_5_ok low_12
lemma sl_42_6_ok : sliceDirectCheck 2 0 0 R_42 G_42 R_11 G_11 = true := by decide +kernel
lemma sl_42_6 : Slice R_42 G_42 (subcubeFast 2 0) 5 := slice_fast_direct sl_42_6_ok low_11
lemma sl_42_7_ok : sliceDirectCheck 0 4 0 R_42 G_42 R_37 G_37 = true := by decide +kernel
lemma sl_42_7 : Slice R_42 G_42 (subcubeFast 0 4) 6 := slice_fast_direct sl_42_7_ok low_37
lemma sl_42_8_ok : sliceDirectCheck 0 8 0 R_42 G_42 R_13 G_13 = true := by decide +kernel
lemma sl_42_8 : Slice R_42 G_42 (subcubeFast 0 8) 7 := slice_fast_direct sl_42_8_ok low_13
lemma sl_42_9_ok : sliceDirectCheck 4 8 0 R_42 G_42 R_9 G_9 = true := by decide +kernel
lemma sl_42_9 : Slice R_42 G_42 (subcubeFast 4 8) 4 := slice_fast_direct sl_42_9_ok low_9
set_option maxRecDepth 500000 in
lemma slices_42_ok : btAll (fun o => ∀ p, o = some p → Slice R_42 G_42 p.1 p.2) slices_42 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_42 G_42 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_42_0) (forall_cons (fun _ h => by cases h; exact sl_42_1) (forall_cons (fun _ h => by cases h; exact sl_42_2) (forall_cons (fun _ h => by cases h; exact sl_42_3) (forall_cons (fun _ h => by cases h; exact sl_42_4) (forall_cons (fun _ h => by cases h; exact sl_42_5) (forall_cons (fun _ h => by cases h; exact sl_42_6) (forall_cons (fun _ h => by cases h; exact sl_42_7) (forall_cons (fun _ h => by cases h; exact sl_42_8) (forall_cons (fun _ h => by cases h; exact sl_42_9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 500000 in
lemma P_42_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_42 G_42 c) P_42 := buildPoolsBT_sound slices_42_ok
def bk_42_init : BT (List (List Nat)) := BT.empty
lemma bk_42_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 (0 - 1) xs.toFinset) bk_42_init := trivial
def nodes_42_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_0 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_init 0 nodes_42_0 = true := by decide +kernel
def bk_42_0 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_0
set_option maxRecDepth 500000 in
lemma bk_42_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 0 xs.toFinset) bk_42_0 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_init_ok chk_42_0
def nodes_42_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_1 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_0 1 nodes_42_1 = true := by decide +kernel
def bk_42_1 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_1
set_option maxRecDepth 500000 in
lemma bk_42_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 1 xs.toFinset) bk_42_1 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_0_ok chk_42_1
def nodes_42_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_2 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_1 2 nodes_42_2 = true := by decide +kernel
def bk_42_2 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_2
set_option maxRecDepth 500000 in
lemma bk_42_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 2 xs.toFinset) bk_42_2 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_1_ok chk_42_2
def nodes_42_3 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_3 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_2 3 nodes_42_3 = true := by decide +kernel
def bk_42_3 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_3
set_option maxRecDepth 500000 in
lemma bk_42_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 3 xs.toFinset) bk_42_3 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_2_ok chk_42_3
def nodes_42_4 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_4 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_3 4 nodes_42_4 = true := by decide +kernel
def bk_42_4 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_4
set_option maxRecDepth 500000 in
lemma bk_42_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 4 xs.toFinset) bk_42_4 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_3_ok chk_42_4
def nodes_42_5 : List NodeSpec := [([0,1,2,3,7,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_5 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_4 5 nodes_42_5 = true := by decide +kernel
def bk_42_5 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_5
set_option maxRecDepth 500000 in
lemma bk_42_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 5 xs.toFinset) bk_42_5 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_4_ok chk_42_5
def nodes_42_6 : List NodeSpec := [([5,0,1,2,6,3,4],[0,1,2,3,4,5,6,7,8],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_6 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_5 6 nodes_42_6 = true := by decide +kernel
def bk_42_6 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_6
set_option maxRecDepth 500000 in
lemma bk_42_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 6 xs.toFinset) bk_42_6 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_5_ok chk_42_6
def nodes_42_7 : List NodeSpec := [([5,0,1,2,3,4],[7,9,0,10,11,2,3,4,1,8,12],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_7 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_6 7 nodes_42_7 = true := by decide +kernel
def bk_42_7 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_7
set_option maxRecDepth 500000 in
lemma bk_42_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 7 xs.toFinset) bk_42_7 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_6_ok chk_42_7
def nodes_42_8 : List NodeSpec := [([0,1,2,3,4],[9,7,10,2,4],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_8 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_7 8 nodes_42_8 = true := by decide +kernel
def bk_42_8 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_8
set_option maxRecDepth 500000 in
lemma bk_42_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 8 xs.toFinset) bk_42_8 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_7_ok chk_42_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_42_ok : forestRootCheck R_42 G_42 [(VAR 1,14,12),(VAR 2,14,10),(VAR 3,14,6),(VAR 4,26,10),(VAR 5,42,10)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_42_in : bucketContainsBT bk_42_8 R_42 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_42 : Lower R_42 G_42 9 := lower_of_forestBT root_42_ok bk_42_8_ok root_42_in
def G_43 : Nat := 0xe8008000e8008000e8008000e8008000
def R_43 : List Nat := varsOf 31
lemma low_43_ok : carryOK [(0,5),(0,4),(0,2),(0,1)] R_43 G_43 R_40 G_40 = true := by decide +kernel
lemma low_43 : Lower R_43 G_43 8 := carry_of low_43_ok low_40
def G_44 : Nat := 0xe800e80080008000e800e80080008000
def R_44 : List Nat := varsOf 47
lemma low_44_ok : carryOK [(0,4),(0,2),(0,1)] R_44 G_44 R_40 G_40 = true := by decide +kernel
lemma low_44 : Lower R_44 G_44 8 := carry_of low_44_ok low_40
def G_45 : Nat := 0xee00880088000000ee00880088000000
def R_45 : List Nat := varsOf 59
lemma low_45_ok : carryOK [(0,2),(0,1)] R_45 G_45 R_40 G_40 = true := by decide +kernel
lemma low_45 : Lower R_45 G_45 8 := carry_of low_45_ok low_40
def G_46 : Nat := 0xfa00a000a0000000fa00a000a0000000
def R_46 : List Nat := varsOf 61
lemma low_46_ok : carryOK [(0,1)] R_46 G_46 R_40 G_40 = true := by decide +kernel
lemma low_46 : Lower R_46 G_46 8 := carry_of low_46_ok low_40
def G_47 : Nat := 0xfe80e800fe80e800fe80e800fe80e800
def R_47 : List Nat := varsOf 31
lemma low_47_ok : carryOK [(0,5),(0,4),(0,2),(0,1)] R_47 G_47 R_42 G_42 = true := by decide +kernel
lemma low_47 : Lower R_47 G_47 9 := carry_of low_47_ok low_42
def G_48 : Nat := 0xfe80fe80e800e800fe80fe80e800e800
def R_48 : List Nat := varsOf 47
lemma low_48_ok : carryOK [(0,4),(0,2),(0,1)] R_48 G_48 R_42 G_42 = true := by decide +kernel
lemma low_48 : Lower R_48 G_48 9 := carry_of low_48_ok low_42
def G_49 : Nat := 0xff88ee00ee008800ff88ee00ee008800
def R_49 : List Nat := varsOf 59
lemma low_49_ok : carryOK [(0,2),(0,1)] R_49 G_49 R_42 G_42 = true := by decide +kernel
lemma low_49 : Lower R_49 G_49 9 := carry_of low_49_ok low_42
def G_50 : Nat := 0xffa0fa00fa00a000ffa0fa00fa00a000
def R_50 : List Nat := varsOf 61
lemma low_50_ok : carryOK [(0,1)] R_50 G_50 R_42 G_42 = true := by decide +kernel
lemma low_50 : Lower R_50 G_50 9 := carry_of low_50_ok low_42
def G_51 : Nat := 0xfe80e800e8008000fe80e800e8008000
def R_51 : List Nat := varsOf 63
def pos_51 : List Nat := [15,15,15,15,27,27,27,27,29,29,29,29,30,30,30,30,31,43,43,43,43,45,45,45,45,46,46,46,46,47,55,55,55,55,55,57,57,57,57,58,58,58,58,59,60,60,60,60,61,62,15,15,15,15,15,15,15,15,15,15,15,15,27,27,27,27,27,27,27,27,27,27,27,27,29,29,29,29,29,29,29,29,29,29,29,29,30,30,30,30,30,30,30,30,30,30,30,30,43,43,43,43,43,43,43,43,43,43,43,43,45,45,45,45,45,45,45,45,45,45,45,45,46,46,46,46,46,46]
def neg_51 : List Nat := [14,13,11,7,26,25,19,11,28,25,21,13,28,26,22,14,23,42,41,35,11,44,41,37,13,44,42,38,14,39,54,53,51,39,23,56,49,41,25,56,50,42,26,51,56,52,44,28,53,54,23,25,26,28,39,41,42,44,51,53,54,56,13,14,23,28,39,41,42,44,51,53,54,56,11,14,23,26,39,41,42,44,51,53,54,56,11,13,23,25,39,41,42,44,51,53,54,56,13,14,23,25,26,28,39,44,51,53,54,56,11,14,23,25,26,28,39,42,51,53,54,56,11,13,23,25,26,28]
def fmask_51 : Nat := fullMask 128
def base_51 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3fffffc003ffffffffd087fe1ff0fff,0x3cd34d34cfccd4cd4ccd0877a1dd0eee),(0xcccccccccccccccccccccccccccccccc,0xfc003fffffc003fffffe0f87fe1ff0ff,0x5575d55955557d5595560f077c1be0dd),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffc003fffffc003ffff007ffe1ff0f,0x99999b9da59a59a7da67e006fba1dd0b),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfffffffffffffffffffffff83fffffff,0xee2ee2ee3ae3ae3ae3b8d6e81776bbb7),(0xffff0000ffff0000ffff0000ffff0000,0x3ffffffffc003ffffc001fff0,0xf3cf3cf3c33c33c33c3fbdddc0017770),(0xffffffff00000000ffffffff00000000,0xfffffffc000000000003fffffffe0000,0x3f03f03fc3fc3fc3fc37bbbeeee0000)]
def steps_51 : List (Nat × Nat × Nat) := [(3,0,3),(0,0,3),(2,0,1),(1,0,1),(0,0,1),(3,7,1),(3,2,3),(0,1,3),(0,10,3),(3,8,3),(3,8,2),(3,0,1),(3,10,3),(2,2,4),(0,2,3),(3,6,1),(0,9,2),(0,2,4),(3,10,2),(1,2,4),(0,9,3),(1,10,2),(0,10,2),(2,4,5),(3,2,4),(3,19,5),(3,19,9),(1,4,5),(1,19,10),(0,25,5),(0,3,25),(3,10,25),(3,12,4),(3,20,4),(0,4,5),(1,10,23),(0,9,25),(3,10,9),(1,19,8),(3,24,4),(3,19,3),(0,27,4),(1,29,8),(3,4,5),(3,30,9),(3,39,9),(3,29,9),(3,30,5),(3,37,3),(0,41,5),(0,41,3),(3,29,27),(1,29,10),(1,10,40),(3,10,33),(0,26,25),(3,14,25),(0,3,33),(3,43,2),(0,27,33),(3,24,33),(0,43,2),(3,43,3),(1,19,14),(1,39,8),(0,34,3),(0,9,33),(3,28,33),(1,43,2),(2,27,40),(1,29,24),(3,29,2),(0,43,3),(2,43,2),(1,29,28),(3,19,26),(3,19,15),(2,56,5),(1,56,5),(0,56,5),(0,3,59),(3,56,5),(0,26,33),(3,43,25),(1,43,23),(2,43,23),(1,12,43),(1,68,2),(1,61,5),(3,68,2),(3,78,2),(3,64,4),(1,64,4),(0,64,4),(0,64,3),(3,64,3),(2,3,4),(0,3,4),(3,40,33),(2,61,5),(3,23,25),(0,74,4),(3,79,3),(1,19,43),(3,67,4),(0,74,3),(3,67,3),(0,61,5),(1,43,20),(3,61,5),(3,79,4),(3,113,3),(3,88,2),(1,88,2),(3,85,3),(2,2,86),(2,9,55),(1,29,64),(3,105,3),(3,29,74),(0,2,33),(1,2,86),(2,74,40),(2,106,5),(1,19,68),(3,68,25),(3,68,4),(1,68,23),(3,29,3),(3,91,5),(3,64,33),(3,83,3),(1,64,40),(3,102,5),(3,43,33),(3,103,5),(0,97,5),(3,64,5),(0,74,33),(0,98,5),(3,97,5),(3,104,27),(1,79,40),(1,79,64),(1,104,2),(1,67,40),(1,29,67),(3,67,33),(1,68,4),(3,104,2),(3,106,5),(3,79,33),(1,106,5),(0,106,5),(1,104,24),(0,90,5),(1,29,79),(3,113,94),(3,106,43),(1,106,43),(2,106,43),(0,106,43),(3,29,92),(3,149,4),(0,92,33),(0,114,33),(1,29,95),(1,29,96),(3,96,33),(0,101,33),(3,136,3),(0,3,138),(1,149,4),(3,29,114),(1,159,14),(3,143,4),(3,29,101),(0,123,3),(1,29,100),(1,49,79),(3,68,33),(0,3,148),(3,95,33),(1,141,64),(0,149,3),(1,141,67),(2,149,4),(0,3,151),(3,29,108),(0,149,4),(3,85,84),(3,14,158),(3,128,3),(3,29,112),(0,152,3),(1,10,113),(1,49,67),(0,108,33),(3,10,94),(0,112,33),(3,100,33),(3,49,74),(3,149,3),(3,141,74),(3,29,111),(1,141,79),(1,129,14),(0,111,33),(3,153,3),(1,14,156),(3,129,3),(3,55,25),(3,164,5),(1,164,5),(0,165,5),(0,165,3),(3,167,5),(3,167,3),(3,166,3),(3,106,68),(1,106,68),(1,2,40),(0,104,2),(3,104,64),(2,104,2),(3,166,5),(0,149,33),(2,42,55),(3,64,178),(3,104,74),(1,104,79),(1,104,67),(3,195,5),(1,29,149),(2,9,155),(0,195,5),(3,102,149),(1,102,149),(3,149,33),(2,149,103),(1,149,40),(3,169,5),(1,106,78),(3,29,149),(2,9,147),(0,169,5),(3,192,5),(3,192,3),(1,104,64),(0,190,4),(0,208,4),(0,178,5),(0,3,178),(3,195,3),(3,159,158),(2,149,40),(3,190,4),(1,149,103),(3,169,3),(3,208,4),(3,167,165),(1,43,155)]
def W_51 : BT Decor := buildWiresBT 9 base_51 steps_51
def autosL_51 : List (List (Nat × Nat)) := [[],[(1,4),(0,2)],[(1,5),(0,4)],[(2,5),(2,4)],[(0,1),(0,5),(1,4),(0,2)],[(4,5)],[(1,2),(0,2),(1,5),(0,4)],[(2,4)],[(2,4),(2,5)],[(2,5)],[(1,5),(1,4),(0,2)],[(0,1)],[(0,1),(1,2),(0,4)],[(0,1),(1,4),(0,2)],[(0,5),(0,1),(1,4),(0,2)],[(0,5),(1,4),(0,2)],[(1,5),(0,1),(1,2),(0,4)],[(1,5),(1,2),(0,4)],[(1,2)],[(1,4),(1,2)],[(1,5),(1,4),(1,2)],[(0,1),(0,2)],[(0,2)],[(1,4),(0,1),(0,2)],[(0,4),(0,2)],[(1,5),(1,4),(0,1),(0,2)],[(0,5),(0,4),(0,2)],[(0,2),(0,1)],[(0,4),(0,2),(0,1)],[(0,5),(0,4),(0,2),(0,1)]]
def autos_51 : BT (List (Nat × Nat)) := btOfList 5 autosL_51
def slicesL_51 : List (Option (Nat × Nat)) := [some (subcubeFast 0 20,6),some (subcubeFast 0 3,6),some (subcubeFast 0 4,9),some (subcubeFast 0 5,6),some (subcubeFast 0 32,9),some (subcubeFast 1 24,4),some (subcubeFast 32 10,4),some (subcubeFast 0 33,6),some (subcubeFast 0 16,9),some (subcubeFast 4 9,4),some (subcubeFast 0 48,6),some (subcubeFast 1 16,5),some (subcubeFast 4 2,5),some (subcubeFast 32 1,5),some (subcubeFast 0 18,6),some (subcubeFast 2 12,4),some (subcubeFast 16 9,4),some (subcubeFast 0 8,10),some (subcubeFast 32 0,8),some (subcubeFast 2 40,4),some (subcubeFast 2 0,8),some (subcubeFast 2 24,4),some (subcubeFast 0 10,7),some (subcubeFast 1 10,4),some (subcubeFast 1 2,5),some (subcubeFast 2 16,5),some (subcubeFast 16 2,5),some (subcubeFast 0 1,9),some (subcubeFast 2 8,7),some (subcubeFast 4 10,4),some (subcubeFast 4 16,5),some (subcubeFast 0 36,6),some (subcubeFast 2 32,5),some (subcubeFast 4 32,5),some (subcubeFast 4 24,4),some (subcubeFast 32 4,5),some (subcubeFast 16 32,5),some (subcubeFast 2 4,5),some (subcubeFast 0 2,9),some (subcubeFast 16 12,4),some (subcubeFast 4 8,7),some (subcubeFast 0 34,6),some (subcubeFast 2 1,5),some (subcubeFast 32 24,4),some (subcubeFast 0 40,7),some (subcubeFast 2 9,4),some (subcubeFast 1 40,4),some (subcubeFast 16 1,5),some (subcubeFast 16 0,8),some (subcubeFast 0 6,6),some (subcubeFast 0 24,7),some (subcubeFast 4 0,8),some (subcubeFast 32 8,7),some (subcubeFast 1 0,8),some (subcubeFast 1 32,5),some (subcubeFast 32 16,5),some (subcubeFast 0 12,7),some (subcubeFast 1 8,7),some (subcubeFast 0 17,6),some (subcubeFast 1 4,5),some (subcubeFast 0 9,7),some (subcubeFast 16 4,5),some (subcubeFast 1 12,4),some (subcubeFast 4 40,4),some (subcubeFast 16 8,7),some (subcubeFast 32 12,4),some (subcubeFast 32 9,4),some (subcubeFast 4 1,5),some (subcubeFast 32 2,5)]
def slices_51 : BT (Option (Nat × Nat)) := btOfList 7 slicesL_51
def ps_51 : List PoolSpec := [(0,[(0,0,1),(1,0,1),(3,10,9)]),(1,[(0,4,5),(1,4,5),(3,40,33)]),(2,[(0,0,1),(1,0,1),(3,10,9),(0,4,5),(1,4,5),(3,40,33)]),(3,[]),(4,[(0,0,1),(1,0,1),(3,10,9),(0,43,2),(1,43,2),(3,67,74)]),(5,[]),(6,[]),(7,[]),(8,[(0,0,1),(1,0,1),(3,10,9),(0,43,2),(1,43,2),(3,67,74)]),(9,[]),(10,[(0,0,1),(1,0,1),(3,10,9)]),(8,[(0,0,1),(1,0,1),(3,10,9),(2,43,2),(3,43,2),(1,79,64)]),(1,[(0,2,4),(1,2,4),(3,23,25)]),(11,[]),(12,[]),(4,[(0,0,1),(1,0,1),(3,10,9),(0,2,4),(1,2,4),(3,23,25)]),(2,[(0,0,1),(1,0,1),(3,10,9),(0,4,5),(1,4,5)]),(1,[(0,4,5),(1,4,5)]),(13,[]),(2,[(0,0,1),(1,0,1),(3,10,9),(2,4,5),(3,4,5)]),(1,[(2,4,5),(3,4,5)]),(4,[(0,0,1),(1,0,1),(3,10,9),(2,43,2),(3,43,2)]),(8,[(0,0,1),(1,0,1),(3,10,9),(2,43,2),(3,43,2)]),(14,[]),(4,[(0,0,1),(1,0,1),(3,10,9),(2,43,2),(3,43,2),(1,79,64)]),(4,[(0,0,1),(1,0,1),(3,10,9),(0,43,2),(1,43,2)]),(8,[(0,0,1),(1,0,1),(3,10,9),(0,43,2),(1,43,2)]),(15,[]),(16,[]),(4,[(0,0,1),(1,0,1),(3,10,9),(0,43,2),(1,67,40)]),(0,[]),(8,[(0,0,1),(1,0,1),(3,10,9),(2,43,23)]),(10,[(0,0,1),(1,0,1)]),(10,[]),(17,[]),(18,[]),(14,[(1,10,23)]),(1,[(0,2,4),(1,2,4)]),(0,[(0,0,1),(1,0,1)]),(4,[(0,0,1),(1,0,1),(0,2,4),(1,2,4),(0,9,25)]),(19,[]),(20,[]),(1,[(2,4,5),(1,29,64)]),(1,[(2,4,5),(3,29,74)]),(1,[]),(21,[]),(22,[]),(2,[(0,0,1),(1,0,1),(3,10,9),(1,4,5)]),(1,[(3,2,3)]),(23,[]),(24,[]),(1,[(0,2,3)]),(25,[]),(1,[(2,2,4),(3,2,4)]),(4,[(0,0,1),(1,0,1),(3,10,9),(2,2,4),(3,2,4)]),(4,[(0,0,1),(1,0,1),(3,10,9),(0,2,4),(1,2,4)]),(1,[(3,68,2)]),(26,[]),(27,[(1,10,2),(0,4,5),(1,4,5),(0,27,33)]),(2,[(0,0,1),(1,0,1),(0,4,5),(1,4,5)]),(4,[(0,0,1),(1,0,1),(3,10,9),(0,43,2)]),(4,[(0,0,1),(1,0,1),(3,10,9),(3,43,2)]),(2,[(0,0,1),(1,0,1),(3,10,9),(0,4,5)]),(2,[(0,0,1),(1,0,1),(0,4,5),(1,4,5),(0,9,33)]),(7,[(3,10,2)]),(1,[(2,4,5)]),(2,[(0,0,1),(1,0,1),(3,10,9),(2,4,5)]),(1,[(1,4,5)]),(8,[(0,0,1),(1,0,1),(3,10,9),(3,43,2)]),(1,[(3,64,3)]),(4,[(0,0,1),(1,0,1),(3,10,9),(2,43,2)]),(8,[(0,0,1),(1,0,1),(3,10,9),(2,43,2)]),(1,[(0,4,5)]),(4,[(0,0,1),(1,0,1),(3,10,9),(1,43,2)]),(2,[(0,0,1),(1,0,1),(3,10,9),(3,64,4)]),(8,[(0,0,1),(1,0,1),(3,10,9),(1,43,2)]),(7,[(0,2,3)]),(28,[(0,4,5),(2,27,40)]),(4,[(0,0,1),(1,0,1),(3,10,9),(0,43,2),(3,67,4)]),(2,[(0,0,1),(1,0,1),(3,10,9),(1,64,4)]),(7,[(3,2,3)]),(29,[]),(30,[]),(8,[(0,0,1),(1,0,1),(3,10,9),(0,43,2)]),(8,[(0,0,1),(1,0,1),(3,10,9),(0,43,2),(1,29,67)]),(31,[(0,0,1),(1,0,1),(3,10,9)]),(32,[]),(1,[(0,64,3)]),(33,[]),(10,[(0,0,1)]),(2,[(0,0,1),(0,4,5),(1,4,5),(3,40,33)]),(34,[]),(7,[(1,10,2)]),(35,[]),(36,[]),(27,[(3,10,2),(2,4,5),(3,4,5)]),(2,[(0,0,1),(1,0,1),(0,4,5),(1,4,5),(3,40,33)]),(37,[]),(27,[(3,10,2),(0,4,5),(1,4,5)]),(4,[]),(2,[]),(2,[(2,0,1),(3,0,1),(2,4,5),(3,4,5)]),(4,[(0,0,1),(1,0,1),(0,2,4),(1,2,4)]),(27,[(0,2,3),(1,4,5),(0,3,33)]),(28,[]),(22,[(1,4,5)]),(28,[(0,2,4)]),(22,[(1,2,4)]),(2,[(0,0,1),(1,0,1),(3,10,9),(3,19,5)]),(4,[(0,0,1),(1,0,1),(3,10,9),(0,2,4)]),(8,[(0,0,1),(1,0,1),(3,10,9),(1,43,23)]),(2,[(0,0,1),(1,0,1),(3,10,9),(1,43,23)]),(27,[(3,10,2),(2,4,5)]),(1,[(2,2,4)]),(4,[(0,0,1),(1,0,1),(3,10,9),(2,2,4)]),(1,[(1,2,4)]),(4,[(0,0,1),(1,0,1),(3,10,9),(1,2,4)]),(1,[(0,2,4)]),(27,[(3,10,2),(0,4,5)]),(28,[(0,4,5)]),(2,[(0,0,1),(1,0,1),(1,4,5),(0,9,33)]),(1,[(3,64,4)]),(2,[(0,0,1),(1,0,1),(2,4,5),(3,4,5)]),(1,[(0,74,4)]),(2,[(0,0,1),(1,0,1),(3,10,9),(1,19,43)]),(2,[(0,0,1),(1,0,1),(3,10,9),(3,67,4)]),(1,[(2,2,4),(3,19,5)]),(27,[(3,10,2),(1,4,5)]),(27,[(3,10,2),(0,4,5),(1,4,5),(3,40,33)]),(38,[(3,10,2),(0,4,5),(1,4,5),(3,40,33)]),(27,[(1,10,2),(0,4,5),(1,4,5)]),(27,[(1,10,2),(1,4,5),(0,27,33)]),(2,[(0,0,1),(1,0,1),(1,4,5)]),(2,[(0,0,1),(0,4,5),(1,4,5)]),(0,[(0,0,1)]),(39,[]),(27,[(1,10,2),(0,4,5),(2,27,40)]),(2,[(0,0,1),(1,0,1),(0,4,5)]),(27,[(1,10,2),(2,4,5),(3,4,5)]),(40,[(0,0,1)]),(27,[(1,10,2),(2,4,5),(3,29,27)]),(41,[]),(40,[]),(42,[]),(2,[(2,0,1),(2,4,5),(1,29,8)]),(43,[]),(44,[]),(45,[]),(46,[]),(2,[(2,0,1),(3,0,1),(2,4,5)]),(38,[]),(47,[]),(48,[]),(49,[]),(50,[]),(51,[]),(52,[]),(53,[]),(27,[]),(50,[(1,0,1)]),(54,[]),(55,[]),(2,[(1,0,1),(2,4,5),(3,29,9)]),(48,[(0,0,1)]),(2,[(0,0,1),(3,4,5)]),(31,[]),(20,[(0,2,4),(0,41,5)]),(17,[(0,0,1),(0,2,4),(1,10,23)]),(2,[(0,0,1),(2,4,5)]),(2,[(0,0,1),(2,4,5),(1,29,10)]),(2,[(0,0,1),(0,4,5),(1,10,40)]),(10,[(0,2,3)]),(56,[]),(17,[(0,0,1),(0,4,5),(1,10,40)]),(2,[(0,0,1),(1,4,5),(3,10,33)]),(57,[]),(2,[(0,0,1),(2,4,5),(3,4,5)]),(27,[(0,2,3),(1,4,5)]),(58,[]),(2,[(1,0,1),(2,4,5),(3,4,5)]),(59,[]),(17,[(1,0,1),(1,2,4),(0,26,25)]),(38,[(3,10,2),(0,4,5),(1,4,5)]),(2,[(0,0,1),(1,0,1),(2,4,5)]),(27,[(3,2,3),(1,4,5)]),(28,[(3,12,4)]),(60,[]),(56,[(1,0,1)]),(4,[(1,0,1),(0,9,3),(0,2,3)]),(2,[(0,0,1),(1,4,5)]),(20,[(0,2,4)]),(4,[(0,0,1),(1,0,1),(0,2,4)]),(61,[]),(62,[]),(2,[(1,0,1),(1,4,5),(0,9,33)]),(17,[(1,0,1),(1,4,5),(0,9,33)]),(2,[(0,0,1),(1,0,1),(3,19,5)]),(38,[(1,10,2),(0,4,5),(2,27,40)]),(2,[(0,0,1),(0,4,5)]),(10,[(3,2,3)]),(20,[(0,4,5)]),(27,[(1,10,2),(0,4,5)]),(27,[(1,10,2),(2,4,5)]),(27,[(1,10,2),(1,4,5)]),(2,[(2,0,1),(2,4,5)]),(8,[]),(63,[]),(4,[(1,0,1),(3,2,3)]),(2,[(1,0,1),(2,4,5)]),(8,[(0,0,1)]),(2,[(0,0,1)]),(2,[(0,0,1),(3,19,5)]),(51,[(0,0,1)]),(52,[(0,0,1)]),(18,[(0,0,1)]),(64,[]),(17,[(0,0,1),(3,12,4)]),(52,[(3,12,4)]),(56,[(1,4,5)]),(65,[]),(27,[(0,2,4)]),(17,[(0,0,1),(0,2,4)]),(52,[(0,2,4)]),(40,[(0,4,5)]),(66,[]),(53,[(0,2,4)]),(38,[(0,2,4)]),(67,[]),(4,[(0,0,1),(0,2,4)]),(18,[(0,2,4)]),(17,[(1,0,1),(1,2,4),(0,9,25)]),(27,[(0,10,2)]),(38,[(0,10,2)]),(38,[(3,10,2),(0,4,5)]),(38,[(3,10,2),(2,4,5)]),(48,[(0,0,1),(3,10,2)]),(68,[]),(2,[(1,0,1),(1,4,5)]),(17,[(1,0,1),(1,4,5)]),(38,[(0,4,5)]),(53,[(0,4,5)]),(27,[(0,4,5)]),(51,[(0,4,5)]),(4,[(1,0,1),(0,2,3)]),(38,[(1,10,2),(0,4,5)]),(4,[(0,0,1)]),(20,[(0,27,4)]),(53,[(0,27,4)]),(28,[(0,27,4)]),(27,[(3,8,2)]),(4,[(0,2,4)]),(17,[(1,0,1),(1,2,4)])]
def P_51 : BT (Option BoundPool) := buildPoolsBT 8 W_51 R_51 slices_51 ps_51
lemma gp_51 : goodPairs G_51 pos_51 neg_51 := goodPairs_of (by decide +kernel)
lemma base_51_ok : ∀ x ∈ base_51, faithful pos_51 neg_51 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_51_ok : btAll (fun x => faithful pos_51 neg_51 x ∧ x.1 < 2^128) W_51 := buildWiresBT_faithful base_51_ok
set_option maxRecDepth 500000 in
lemma autos_51_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_51 = G_51) autos_51 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_51_0_ok : sliceDirectCheck 0 20 0 R_51 G_51 R_31 G_31 = true := by decide +kernel
lemma sl_51_0 : Slice R_51 G_51 (subcubeFast 0 20) 6 := slice_fast_direct sl_51_0_ok low_31
lemma sl_51_1_ok : sliceDirectCheck 0 3 0 R_51 G_51 R_12 G_12 = true := by decide +kernel
lemma sl_51_1 : Slice R_51 G_51 (subcubeFast 0 3) 6 := slice_fast_direct sl_51_1_ok low_12
lemma sl_51_2_ok : sliceDirectCheck 0 4 0 R_51 G_51 R_49 G_49 = true := by decide +kernel
lemma sl_51_2 : Slice R_51 G_51 (subcubeFast 0 4) 9 := slice_fast_direct sl_51_2_ok low_49
lemma sl_51_3_ok : sliceDirectCheck 0 5 0 R_51 G_51 R_37 G_37 = true := by decide +kernel
lemma sl_51_3 : Slice R_51 G_51 (subcubeFast 0 5) 6 := slice_fast_direct sl_51_3_ok low_37
lemma sl_51_4_ok : sliceDirectCheck 0 32 0 R_51 G_51 R_47 G_47 = true := by decide +kernel
lemma sl_51_4 : Slice R_51 G_51 (subcubeFast 0 32) 9 := slice_fast_direct sl_51_4_ok low_47
lemma sl_51_5_ok : sliceDirectCheck 1 24 0 R_51 G_51 R_7 G_7 = true := by decide +kernel
lemma sl_51_5 : Slice R_51 G_51 (subcubeFast 1 24) 4 := slice_fast_direct sl_51_5_ok low_7
lemma sl_51_6_ok : sliceDirectCheck 32 10 0 R_51 G_51 R_4 G_4 = true := by decide +kernel
lemma sl_51_6 : Slice R_51 G_51 (subcubeFast 32 10) 4 := slice_fast_direct sl_51_6_ok low_4
lemma sl_51_7_ok : sliceDirectCheck 0 33 0 R_51 G_51 R_35 G_35 = true := by decide +kernel
lemma sl_51_7 : Slice R_51 G_51 (subcubeFast 0 33) 6 := slice_fast_direct sl_51_7_ok low_35
lemma sl_51_8_ok : sliceDirectCheck 0 16 0 R_51 G_51 R_48 G_48 = true := by decide +kernel
lemma sl_51_8 : Slice R_51 G_51 (subcubeFast 0 16) 9 := slice_fast_direct sl_51_8_ok low_48
lemma sl_51_9_ok : sliceDirectCheck 4 9 0 R_51 G_51 R_9 G_9 = true := by decide +kernel
lemma sl_51_9 : Slice R_51 G_51 (subcubeFast 4 9) 4 := slice_fast_direct sl_51_9_ok low_9
lemma sl_51_10_ok : sliceDirectCheck 0 48 0 R_51 G_51 R_25 G_25 = true := by decide +kernel
lemma sl_51_10 : Slice R_51 G_51 (subcubeFast 0 48) 6 := slice_fast_direct sl_51_10_ok low_25
lemma sl_51_11_ok : sliceDirectCheck 1 16 0 R_51 G_51 R_24 G_24 = true := by decide +kernel
lemma sl_51_11 : Slice R_51 G_51 (subcubeFast 1 16) 5 := slice_fast_direct sl_51_11_ok low_24
lemma sl_51_12_ok : sliceDirectCheck 4 2 0 R_51 G_51 R_28 G_28 = true := by decide +kernel
lemma sl_51_12 : Slice R_51 G_51 (subcubeFast 4 2) 5 := slice_fast_direct sl_51_12_ok low_28
lemma sl_51_13_ok : sliceDirectCheck 32 1 0 R_51 G_51 R_23 G_23 = true := by decide +kernel
lemma sl_51_13 : Slice R_51 G_51 (subcubeFast 32 1) 5 := slice_fast_direct sl_51_13_ok low_23
lemma sl_51_14_ok : sliceDirectCheck 0 18 0 R_51 G_51 R_33 G_33 = true := by decide +kernel
lemma sl_51_14 : Slice R_51 G_51 (subcubeFast 0 18) 6 := slice_fast_direct sl_51_14_ok low_33
lemma sl_51_15_ok : sliceDirectCheck 2 12 0 R_51 G_51 R_8 G_8 = true := by decide +kernel
lemma sl_51_15 : Slice R_51 G_51 (subcubeFast 2 12) 4 := slice_fast_direct sl_51_15_ok low_8
lemma sl_51_16_ok : sliceDirectCheck 16 9 0 R_51 G_51 R_7 G_7 = true := by decide +kernel
lemma sl_51_16 : Slice R_51 G_51 (subcubeFast 16 9) 4 := slice_fast_direct sl_51_16_ok low_7
lemma sl_51_17_ok : sliceDirectCheck 0 8 0 R_51 G_51 R_41 G_41 = true := by decide +kernel
lemma sl_51_17 : Slice R_51 G_51 (subcubeFast 0 8) 10 := slice_fast_direct sl_51_17_ok low_41
lemma sl_51_18_ok : sliceDirectCheck 32 0 0 R_51 G_51 R_43 G_43 = true := by decide +kernel
lemma sl_51_18 : Slice R_51 G_51 (subcubeFast 32 0) 8 := slice_fast_direct sl_51_18_ok low_43
lemma sl_51_19_ok : sliceDirectCheck 2 40 0 R_51 G_51 R_4 G_4 = true := by decide +kernel
lemma sl_51_19 : Slice R_51 G_51 (subcubeFast 2 40) 4 := slice_fast_direct sl_51_19_ok low_4
lemma sl_51_20_ok : sliceDirectCheck 2 0 0 R_51 G_51 R_46 G_46 = true := by decide +kernel
lemma sl_51_20 : Slice R_51 G_51 (subcubeFast 2 0) 8 := slice_fast_direct sl_51_20_ok low_46
lemma sl_51_21_ok : sliceDirectCheck 2 24 0 R_51 G_51 R_5 G_5 = true := by decide +kernel
lemma sl_51_21 : Slice R_51 G_51 (subcubeFast 2 24) 4 := slice_fast_direct sl_51_21_ok low_5
lemma sl_51_22_ok : sliceDirectCheck 0 10 0 R_51 G_51 R_39 G_39 = true := by decide +kernel
lemma sl_51_22 : Slice R_51 G_51 (subcubeFast 0 10) 7 := slice_fast_direct sl_51_22_ok low_39
lemma sl_51_23_ok : sliceDirectCheck 1 10 0 R_51 G_51 R_0 G_0 = true := by decide +kernel
lemma sl_51_23 : Slice R_51 G_51 (subcubeFast 1 10) 4 := slice_fast_direct sl_51_23_ok low_0
lemma sl_51_24_ok : sliceDirectCheck 1 2 0 R_51 G_51 R_11 G_11 = true := by decide +kernel
lemma sl_51_24 : Slice R_51 G_51 (subcubeFast 1 2) 5 := slice_fast_direct sl_51_24_ok low_11
lemma sl_51_25_ok : sliceDirectCheck 2 16 0 R_51 G_51 R_21 G_21 = true := by decide +kernel
lemma sl_51_25 : Slice R_51 G_51 (subcubeFast 2 16) 5 := slice_fast_direct sl_51_25_ok low_21
lemma sl_51_26_ok : sliceDirectCheck 16 2 0 R_51 G_51 R_21 G_21 = true := by decide +kernel
lemma sl_51_26 : Slice R_51 G_51 (subcubeFast 16 2) 5 := slice_fast_direct sl_51_26_ok low_21
lemma sl_51_27_ok : sliceDirectCheck 0 1 0 R_51 G_51 R_42 G_42 = true := by decide +kernel
lemma sl_51_27 : Slice R_51 G_51 (subcubeFast 0 1) 9 := slice_fast_direct sl_51_27_ok low_42
lemma sl_51_28_ok : sliceDirectCheck 2 8 0 R_51 G_51 R_22 G_22 = true := by decide +kernel
lemma sl_51_28 : Slice R_51 G_51 (subcubeFast 2 8) 7 := slice_fast_direct sl_51_28_ok low_22
lemma sl_51_29_ok : sliceDirectCheck 4 10 0 R_51 G_51 R_8 G_8 = true := by decide +kernel
lemma sl_51_29 : Slice R_51 G_51 (subcubeFast 4 10) 4 := slice_fast_direct sl_51_29_ok low_8
lemma sl_51_30_ok : sliceDirectCheck 4 16 0 R_51 G_51 R_18 G_18 = true := by decide +kernel
lemma sl_51_30 : Slice R_51 G_51 (subcubeFast 4 16) 5 := slice_fast_direct sl_51_30_ok low_18
lemma sl_51_31_ok : sliceDirectCheck 0 36 0 R_51 G_51 R_30 G_30 = true := by decide +kernel
lemma sl_51_31 : Slice R_51 G_51 (subcubeFast 0 36) 6 := slice_fast_direct sl_51_31_ok low_30
lemma sl_51_32_ok : sliceDirectCheck 2 32 0 R_51 G_51 R_20 G_20 = true := by decide +kernel
lemma sl_51_32 : Slice R_51 G_51 (subcubeFast 2 32) 5 := slice_fast_direct sl_51_32_ok low_20
lemma sl_51_33_ok : sliceDirectCheck 4 32 0 R_51 G_51 R_17 G_17 = true := by decide +kernel
lemma sl_51_33 : Slice R_51 G_51 (subcubeFast 4 32) 5 := slice_fast_direct sl_51_33_ok low_17
lemma sl_51_34_ok : sliceDirectCheck 4 24 0 R_51 G_51 R_3 G_3 = true := by decide +kernel
lemma sl_51_34 : Slice R_51 G_51 (subcubeFast 4 24) 4 := slice_fast_direct sl_51_34_ok low_3
lemma sl_51_35_ok : sliceDirectCheck 32 4 0 R_51 G_51 R_17 G_17 = true := by decide +kernel
lemma sl_51_35 : Slice R_51 G_51 (subcubeFast 32 4) 5 := slice_fast_direct sl_51_35_ok low_17
lemma sl_51_36_ok : sliceDirectCheck 16 32 0 R_51 G_51 R_14 G_14 = true := by decide +kernel
lemma sl_51_36 : Slice R_51 G_51 (subcubeFast 16 32) 5 := slice_fast_direct sl_51_36_ok low_14
lemma sl_51_37_ok : sliceDirectCheck 2 4 0 R_51 G_51 R_28 G_28 = true := by decide +kernel
lemma sl_51_37 : Slice R_51 G_51 (subcubeFast 2 4) 5 := slice_fast_direct sl_51_37_ok low_28
lemma sl_51_38_ok : sliceDirectCheck 0 2 0 R_51 G_51 R_50 G_50 = true := by decide +kernel
lemma sl_51_38 : Slice R_51 G_51 (subcubeFast 0 2) 9 := slice_fast_direct sl_51_38_ok low_50
lemma sl_51_39_ok : sliceDirectCheck 16 12 0 R_51 G_51 R_3 G_3 = true := by decide +kernel
lemma sl_51_39 : Slice R_51 G_51 (subcubeFast 16 12) 4 := slice_fast_direct sl_51_39_ok low_3
lemma sl_51_40_ok : sliceDirectCheck 4 8 0 R_51 G_51 R_19 G_19 = true := by decide +kernel
lemma sl_51_40 : Slice R_51 G_51 (subcubeFast 4 8) 7 := slice_fast_direct sl_51_40_ok low_19
lemma sl_51_41_ok : sliceDirectCheck 0 34 0 R_51 G_51 R_32 G_32 = true := by decide +kernel
lemma sl_51_41 : Slice R_51 G_51 (subcubeFast 0 34) 6 := slice_fast_direct sl_51_41_ok low_32
lemma sl_51_42_ok : sliceDirectCheck 2 1 0 R_51 G_51 R_11 G_11 = true := by decide +kernel
lemma sl_51_42 : Slice R_51 G_51 (subcubeFast 2 1) 5 := slice_fast_direct sl_51_42_ok low_11
lemma sl_51_43_ok : sliceDirectCheck 32 24 0 R_51 G_51 R_1 G_1 = true := by decide +kernel
lemma sl_51_43 : Slice R_51 G_51 (subcubeFast 32 24) 4 := slice_fast_direct sl_51_43_ok low_1
lemma sl_51_44_ok : sliceDirectCheck 0 40 0 R_51 G_51 R_26 G_26 = true := by decide +kernel
lemma sl_51_44 : Slice R_51 G_51 (subcubeFast 0 40) 7 := slice_fast_direct sl_51_44_ok low_26
lemma sl_51_45_ok : sliceDirectCheck 2 9 0 R_51 G_51 R_0 G_0 = true := by decide +kernel
lemma sl_51_45 : Slice R_51 G_51 (subcubeFast 2 9) 4 := slice_fast_direct sl_51_45_ok low_0
lemma sl_51_46_ok : sliceDirectCheck 1 40 0 R_51 G_51 R_6 G_6 = true := by decide +kernel
lemma sl_51_46 : Slice R_51 G_51 (subcubeFast 1 40) 4 := slice_fast_direct sl_51_46_ok low_6
lemma sl_51_47_ok : sliceDirectCheck 16 1 0 R_51 G_51 R_24 G_24 = true := by decide +kernel
lemma sl_51_47 : Slice R_51 G_51 (subcubeFast 16 1) 5 := slice_fast_direct sl_51_47_ok low_24
lemma sl_51_48_ok : sliceDirectCheck 16 0 0 R_51 G_51 R_44 G_44 = true := by decide +kernel
lemma sl_51_48 : Slice R_51 G_51 (subcubeFast 16 0) 8 := slice_fast_direct sl_51_48_ok low_44
lemma sl_51_49_ok : sliceDirectCheck 0 6 0 R_51 G_51 R_34 G_34 = true := by decide +kernel
lemma sl_51_49 : Slice R_51 G_51 (subcubeFast 0 6) 6 := slice_fast_direct sl_51_49_ok low_34
lemma sl_51_50_ok : sliceDirectCheck 0 24 0 R_51 G_51 R_27 G_27 = true := by decide +kernel
lemma sl_51_50 : Slice R_51 G_51 (subcubeFast 0 24) 7 := slice_fast_direct sl_51_50_ok low_27
lemma sl_51_51_ok : sliceDirectCheck 4 0 0 R_51 G_51 R_45 G_45 = true := by decide +kernel
lemma sl_51_51 : Slice R_51 G_51 (subcubeFast 4 0) 8 := slice_fast_direct sl_51_51_ok low_45
lemma sl_51_52_ok : sliceDirectCheck 32 8 0 R_51 G_51 R_15 G_15 = true := by decide +kernel
lemma sl_51_52 : Slice R_51 G_51 (subcubeFast 32 8) 7 := slice_fast_direct sl_51_52_ok low_15
lemma sl_51_53_ok : sliceDirectCheck 1 0 0 R_51 G_51 R_40 G_40 = true := by decide +kernel
lemma sl_51_53 : Slice R_51 G_51 (subcubeFast 1 0) 8 := slice_fast_direct sl_51_53_ok low_40
lemma sl_51_54_ok : sliceDirectCheck 1 32 0 R_51 G_51 R_23 G_23 = true := by decide +kernel
lemma sl_51_54 : Slice R_51 G_51 (subcubeFast 1 32) 5 := slice_fast_direct sl_51_54_ok low_23
lemma sl_51_55_ok : sliceDirectCheck 32 16 0 R_51 G_51 R_14 G_14 = true := by decide +kernel
lemma sl_51_55 : Slice R_51 G_51 (subcubeFast 32 16) 5 := slice_fast_direct sl_51_55_ok low_14
lemma sl_51_56_ok : sliceDirectCheck 0 12 0 R_51 G_51 R_38 G_38 = true := by decide +kernel
lemma sl_51_56 : Slice R_51 G_51 (subcubeFast 0 12) 7 := slice_fast_direct sl_51_56_ok low_38
lemma sl_51_57_ok : sliceDirectCheck 1 8 0 R_51 G_51 R_10 G_10 = true := by decide +kernel
lemma sl_51_57 : Slice R_51 G_51 (subcubeFast 1 8) 7 := slice_fast_direct sl_51_57_ok low_10
lemma sl_51_58_ok : sliceDirectCheck 0 17 0 R_51 G_51 R_36 G_36 = true := by decide +kernel
lemma sl_51_58 : Slice R_51 G_51 (subcubeFast 0 17) 6 := slice_fast_direct sl_51_58_ok low_36
lemma sl_51_59_ok : sliceDirectCheck 1 4 0 R_51 G_51 R_29 G_29 = true := by decide +kernel
lemma sl_51_59 : Slice R_51 G_51 (subcubeFast 1 4) 5 := slice_fast_direct sl_51_59_ok low_29
lemma sl_51_60_ok : sliceDirectCheck 0 9 0 R_51 G_51 R_13 G_13 = true := by decide +kernel
lemma sl_51_60 : Slice R_51 G_51 (subcubeFast 0 9) 7 := slice_fast_direct sl_51_60_ok low_13
lemma sl_51_61_ok : sliceDirectCheck 16 4 0 R_51 G_51 R_18 G_18 = true := by decide +kernel
lemma sl_51_61 : Slice R_51 G_51 (subcubeFast 16 4) 5 := slice_fast_direct sl_51_61_ok low_18
lemma sl_51_62_ok : sliceDirectCheck 1 12 0 R_51 G_51 R_9 G_9 = true := by decide +kernel
lemma sl_51_62 : Slice R_51 G_51 (subcubeFast 1 12) 4 := slice_fast_direct sl_51_62_ok low_9
lemma sl_51_63_ok : sliceDirectCheck 4 40 0 R_51 G_51 R_2 G_2 = true := by decide +kernel
lemma sl_51_63 : Slice R_51 G_51 (subcubeFast 4 40) 4 := slice_fast_direct sl_51_63_ok low_2
lemma sl_51_64_ok : sliceDirectCheck 16 8 0 R_51 G_51 R_16 G_16 = true := by decide +kernel
lemma sl_51_64 : Slice R_51 G_51 (subcubeFast 16 8) 7 := slice_fast_direct sl_51_64_ok low_16
lemma sl_51_65_ok : sliceDirectCheck 32 12 0 R_51 G_51 R_2 G_2 = true := by decide +kernel
lemma sl_51_65 : Slice R_51 G_51 (subcubeFast 32 12) 4 := slice_fast_direct sl_51_65_ok low_2
lemma sl_51_66_ok : sliceDirectCheck 32 9 0 R_51 G_51 R_6 G_6 = true := by decide +kernel
lemma sl_51_66 : Slice R_51 G_51 (subcubeFast 32 9) 4 := slice_fast_direct sl_51_66_ok low_6
lemma sl_51_67_ok : sliceDirectCheck 4 1 0 R_51 G_51 R_29 G_29 = true := by decide +kernel
lemma sl_51_67 : Slice R_51 G_51 (subcubeFast 4 1) 5 := slice_fast_direct sl_51_67_ok low_29
lemma sl_51_68_ok : sliceDirectCheck 32 2 0 R_51 G_51 R_20 G_20 = true := by decide +kernel
lemma sl_51_68 : Slice R_51 G_51 (subcubeFast 32 2) 5 := slice_fast_direct sl_51_68_ok low_20
set_option maxRecDepth 500000 in
lemma slices_51_ok : btAll (fun o => ∀ p, o = some p → Slice R_51 G_51 p.1 p.2) slices_51 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_51 G_51 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_51_0) (forall_cons (fun _ h => by cases h; exact sl_51_1) (forall_cons (fun _ h => by cases h; exact sl_51_2) (forall_cons (fun _ h => by cases h; exact sl_51_3) (forall_cons (fun _ h => by cases h; exact sl_51_4) (forall_cons (fun _ h => by cases h; exact sl_51_5) (forall_cons (fun _ h => by cases h; exact sl_51_6) (forall_cons (fun _ h => by cases h; exact sl_51_7) (forall_cons (fun _ h => by cases h; exact sl_51_8) (forall_cons (fun _ h => by cases h; exact sl_51_9) (forall_cons (fun _ h => by cases h; exact sl_51_10) (forall_cons (fun _ h => by cases h; exact sl_51_11) (forall_cons (fun _ h => by cases h; exact sl_51_12) (forall_cons (fun _ h => by cases h; exact sl_51_13) (forall_cons (fun _ h => by cases h; exact sl_51_14) (forall_cons (fun _ h => by cases h; exact sl_51_15) (forall_cons (fun _ h => by cases h; exact sl_51_16) (forall_cons (fun _ h => by cases h; exact sl_51_17) (forall_cons (fun _ h => by cases h; exact sl_51_18) (forall_cons (fun _ h => by cases h; exact sl_51_19) (forall_cons (fun _ h => by cases h; exact sl_51_20) (forall_cons (fun _ h => by cases h; exact sl_51_21) (forall_cons (fun _ h => by cases h; exact sl_51_22) (forall_cons (fun _ h => by cases h; exact sl_51_23) (forall_cons (fun _ h => by cases h; exact sl_51_24) (forall_cons (fun _ h => by cases h; exact sl_51_25) (forall_cons (fun _ h => by cases h; exact sl_51_26) (forall_cons (fun _ h => by cases h; exact sl_51_27) (forall_cons (fun _ h => by cases h; exact sl_51_28) (forall_cons (fun _ h => by cases h; exact sl_51_29) (forall_cons (fun _ h => by cases h; exact sl_51_30) (forall_cons (fun _ h => by cases h; exact sl_51_31) (forall_cons (fun _ h => by cases h; exact sl_51_32) (forall_cons (fun _ h => by cases h; exact sl_51_33) (forall_cons (fun _ h => by cases h; exact sl_51_34) (forall_cons (fun _ h => by cases h; exact sl_51_35) (forall_cons (fun _ h => by cases h; exact sl_51_36) (forall_cons (fun _ h => by cases h; exact sl_51_37) (forall_cons (fun _ h => by cases h; exact sl_51_38) (forall_cons (fun _ h => by cases h; exact sl_51_39) (forall_cons (fun _ h => by cases h; exact sl_51_40) (forall_cons (fun _ h => by cases h; exact sl_51_41) (forall_cons (fun _ h => by cases h; exact sl_51_42) (forall_cons (fun _ h => by cases h; exact sl_51_43) (forall_cons (fun _ h => by cases h; exact sl_51_44) (forall_cons (fun _ h => by cases h; exact sl_51_45) (forall_cons (fun _ h => by cases h; exact sl_51_46) (forall_cons (fun _ h => by cases h; exact sl_51_47) (forall_cons (fun _ h => by cases h; exact sl_51_48) (forall_cons (fun _ h => by cases h; exact sl_51_49) (forall_cons (fun _ h => by cases h; exact sl_51_50) (forall_cons (fun _ h => by cases h; exact sl_51_51) (forall_cons (fun _ h => by cases h; exact sl_51_52) (forall_cons (fun _ h => by cases h; exact sl_51_53) (forall_cons (fun _ h => by cases h; exact sl_51_54) (forall_cons (fun _ h => by cases h; exact sl_51_55) (forall_cons (fun _ h => by cases h; exact sl_51_56) (forall_cons (fun _ h => by cases h; exact sl_51_57) (forall_cons (fun _ h => by cases h; exact sl_51_58) (forall_cons (fun _ h => by cases h; exact sl_51_59) (forall_cons (fun _ h => by cases h; exact sl_51_60) (forall_cons (fun _ h => by cases h; exact sl_51_61) (forall_cons (fun _ h => by cases h; exact sl_51_62) (forall_cons (fun _ h => by cases h; exact sl_51_63) (forall_cons (fun _ h => by cases h; exact sl_51_64) (forall_cons (fun _ h => by cases h; exact sl_51_65) (forall_cons (fun _ h => by cases h; exact sl_51_66) (forall_cons (fun _ h => by cases h; exact sl_51_67) (forall_cons (fun _ h => by cases h; exact sl_51_68) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 500000 in
lemma P_51_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_51 G_51 c) P_51 := buildPoolsBT_sound slices_51_ok
def bk_51_init : BT (List (List Nat)) := BT.empty
lemma bk_51_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_51 (0 - 1) xs.toFinset) bk_51_init := trivial
def nodes_51_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_51_0 : checkNodesBT W_51 G_51 fmask_51 P_51 autos_51 bk_51_init 0 nodes_51_0 = true := by decide +kernel
def bk_51_0 : BT (List (List Nat)) := buildBucketsBT W_51 nodes_51_0
set_option maxRecDepth 500000 in
lemma bk_51_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_51 0 xs.toFinset) bk_51_0 :=
  buildBucketsBT_sound (by decide) gp_51 W_51_ok P_51_ok autos_51_ok bk_51_init_ok chk_51_0
def nodes_51_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_51_1 : checkNodesBT W_51 G_51 fmask_51 P_51 autos_51 bk_51_0 1 nodes_51_1 = true := by decide +kernel
def bk_51_1 : BT (List (List Nat)) := buildBucketsBT W_51 nodes_51_1
set_option maxRecDepth 500000 in
lemma bk_51_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_51 1 xs.toFinset) bk_51_1 :=
  buildBucketsBT_sound (by decide) gp_51 W_51_ok P_51_ok autos_51_ok bk_51_0_ok chk_51_1
def nodes_51_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_51_2 : checkNodesBT W_51 G_51 fmask_51 P_51 autos_51 bk_51_1 2 nodes_51_2 = true := by decide +kernel
def bk_51_2 : BT (List (List Nat)) := buildBucketsBT W_51 nodes_51_2
set_option maxRecDepth 500000 in
lemma bk_51_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_51 2 xs.toFinset) bk_51_2 :=
  buildBucketsBT_sound (by decide) gp_51 W_51_ok P_51_ok autos_51_ok bk_51_1_ok chk_51_2
def nodes_51_3 : List NodeSpec := [([163,10,23,3],[],[]),([201,23,3,94],[],[]),([266,165,3,5],[],[]),([228,43,254,3],[],[]),([266,64,3,5],[],[]),([104,64,149,3],[],[]),([195,258,3,5],[],[]),([64,203,3,40],[],[]),([165,223,3,5],[],[]),([104,149,3,40],[],[]),([149,63,3,40],[],[]),([64,108,63,40],[],[]),([266,149,3,5],[],[]),([195,3,263,5],[],[]),([104,149,3],[],[]),([266,195,3,5],[],[]),([104,64,108,3],[],[]),([169,266,3,5],[],[]),([266,3,5],[],[]),([104,24,267,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_51_3 : checkNodesBT W_51 G_51 fmask_51 P_51 autos_51 bk_51_2 3 nodes_51_3 = true := by decide +kernel
def bk_51_3 : BT (List (List Nat)) := buildBucketsBT W_51 nodes_51_3
set_option maxRecDepth 500000 in
lemma bk_51_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_51 3 xs.toFinset) bk_51_3 :=
  buildBucketsBT_sound (by decide) gp_51 W_51_ok P_51_ok autos_51_ok bk_51_2_ok chk_51_3
def nd_51_4_0 : List NodeSpec := [([163,10,2,3,4],[],[0]),([10,61,23,124,5],[],[]),([204,61,23,3,5],[],[]),([118,10,88,20,40],[],[]),([217,43,23,3,5],[],[]),([106,43,218,23,3],[],[]),([106,43,23,3,219],[],[]),([106,43,165,3,5],[0],[]),([106,43,220,3,5],[],[]),([106,43,221,3,5],[],[]),([106,43,222,3,5],[],[]),([106,43,223,3,5],[],[0]),([104,43,92,2,3],[],[]),([104,43,2,114,3],[],[]),([106,43,224,3,5],[],[]),([106,43,225,3,5],[],[]),([201,2,3,4,94],[],[0]),([106,43,226,3,5],[],[]),([167,165,3,5],[0],[0]),([106,164,68,3,5],[],[]),([106,78,165,3,5],[0],[]),([104,43,96,2,3],[],[]),([104,43,64,3,227],[],[]),([228,104,43,64,3],[1],[0]),([104,43,229,2,3],[],[]),([104,12,43,64,3],[2],[]),([104,43,64,20,3],[1],[]),([104,43,101,2,3],[],[]),([104,43,100,2,3],[],[]),([64,68,2,63,40],[],[]),([230,104,43,64,3],[],[]),([104,79,64,3,40],[],[0]),([104,79,64,3],[2],[0]),([106,43,231,3,5],[],[]),([104,78,64,2,3],[2],[]),([79,64,63,3,40],[],[0]),([29,49,64,149,3],[],[0]),([106,43,135,3,5],[],[]),([64,232,3,4,5],[3],[]),([105,115,10,23,3],[],[0]),([64,149,3,40,33],[],[0]),([149,3,4,138,5],[],[]),([43,2,108,63,40],[],[0]),([64,108,134,4,5],[],[]),([64,203,3,4,5],[],[0]),([233,10,23,3,5],[],[]),([149,3,40,33],[4],[0]),([234,149,3,4,5],[],[]),([64,108,3,40,33],[],[0]),([10,88,20,119,40],[5,6],[]),([49,149,103,3,5],[],[]),([64,108,103,40,5],[],[]),([104,43,2,235,3],[2],[]),([149,134,3,4,5],[],[]),([149,3,4,145,5],[],[]),([142,149,3,4,5],[],[]),([67,74,63,3,40],[],[0]),([228,104,43,74,3],[],[]),([43,2,114,63,40],[],[]),([104,43,2,111,3],[],[]),([43,2,111,63,40],[],[]),([64,157,3,40],[0],[0]),([104,43,20,74,3],[],[]),([236,43,2,3,40],[7],[]),([104,237,43,2,3],[],[]),([67,68,2,63,40],[6],[]),([104,67,74,3,40],[],[0]),([29,49,149,3],[4,8],[0]),([238,149,3,4,5],[],[]),([149,3,40,4,5],[4],[]),([149,239,3,4,5],[],[]),([141,64,108,4,5],[],[]),([117,10,61,23,5],[],[]),([192,169,64,3,5],[],[0]),([104,67,74,3],[1,2],[0]),([146,149,3,4,5],[],[]),([232,149,3,4,5],[],[]),([43,2,203,3,40],[],[0]),([64,108,63,4,5],[],[0]),([104,240,24,10,3],[],[]),([241,149,3,4,5],[],[]),([104,67,68,2,3],[],[]),([43,64,20,63,40],[],[]),([190,195,3,4,5],[9,8],[]),([102,149,3,40,5],[4],[]),([95,43,2,63,40],[],[]),([149,3,4,139,5],[],[]),([106,43,161,3,5],[],[]),([104,43,2,108,3],[],[0]),([242,149,3,4,5],[],[]),([149,243,3,4,5],[8],[]),([195,3,178,5],[8],[0]),([192,169,149,3,5],[],[0]),([244,64,3,4,5],[],[]),([245,149,3,4,5],[],[]),([149,103,3,40,5],[9,4],[]),([104,43,24,155,3],[10],[0]),([43,20,74,63,40],[],[]),([149,3,4,246,5],[],[]),([149,247,3,4,5],[],[]),([10,113,23,3,94],[],[0,1]),([106,43,55,3,5],[],[]),([106,43,248,3,5],[],[]),([208,195,3,4,5],[8],[]),([192,149,103,3,5],[],[]),([249,149,3,4,5],[],[]),([208,169,3,4,5],[9,8],[]),([250,10,2,3,40],[],[]),([192,169,3,5],[8],[0]),([251,149,3,4,5],[],[]),([49,64,108,103,5],[],[]),([104,95,43,2,3],[],[]),([136,149,3,4,5],[],[]),([149,3,4,252,5],[],[]),([244,149,3,4,5],[],[]),([149,253,3,4,5],[],[]),([149,63,3,4,5],[],[0]),([64,195,3,178,5],[],[0]),([104,250,10,2,3],[],[]),([104,236,43,2,3],[],[]),([43,112,2,63,40],[],[]),([61,201,23,3,5],[],[0]),([104,43,254,2,3],[1],[0]),([255,149,3,4,5],[],[]),([195,149,3,4,5],[8],[]),([104,43,24,150,3],[],[]),([256,149,3,4,5],[],[]),([102,195,149,3,5],[8],[]),([104,43,64,2,3],[2],[]),([97,195,149,3,5],[3,11],[]),([195,149,103,3,5],[9],[0]),([141,149,3,4,5],[],[]),([149,3,4,257,5],[],[]),([169,195,149,3,5],[3,8],[]),([149,258,3,4,5],[],[0]),([259,149,3,4,5],[],[]),([18,0,1,260,3],[],[]),([208,190,149,4,5],[3,9],[]),([261,149,3,4,5],[],[]),([169,149,3,4,5],[8],[]),([14,0,1,260,3],[],[]),([180,0,1,3,158],[],[]),([104,43,112,2,3],[],[]),([195,149,3,98,5],[11],[]),([123,149,3,4,5],[],[]),([195,149,3,178,5],[],[0]),([192,97,149,3,5],[11],[]),([262,149,3,4,5],[],[]),([166,164,3,5],[0,12],[0]),([149,3,263,4,5],[9],[0]),([29,49,64,108,3],[],[0]),([14,0,1,156,216],[],[]),([104,43,160,2,3],[],[]),([169,190,3,4,5],[],[]),([104,64,68,2,3],[5,2],[]),([264,149,3,4,5],[],[]),([104,240,10,27,3],[],[]),([106,165,68,3,5],[0],[]),([43,100,2,63,40],[],[]),([104,43,2,147,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_51_4_0 : checkNodesBT W_51 G_51 fmask_51 P_51 autos_51 bk_51_3 4 nd_51_4_0 = true := by decide +kernel
def nd_51_4_1 : List NodeSpec := [([149,265,3,4,5],[],[]),([43,2,147,3,40],[7],[]),([43,2,63,3,151],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_51_4_1 : checkNodesBT W_51 G_51 fmask_51 P_51 autos_51 bk_51_3 4 nd_51_4_1 = true := by decide +kernel
def nodes_51_4 : List NodeSpec := nd_51_4_0 ++ nd_51_4_1
set_option maxRecDepth 500000 in
lemma chk_51_4 : checkNodesBT W_51 G_51 fmask_51 P_51 autos_51 bk_51_3 4 nodes_51_4 = true := by
  unfold nodes_51_4 checkNodesBT; simp only [List.all_append, Bool.and_eq_true]
  exact ⟨chk_51_4_0, chk_51_4_1⟩
def bk_51_4 : BT (List (List Nat)) := buildBucketsBT W_51 nodes_51_4
set_option maxRecDepth 500000 in
lemma bk_51_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_51 4 xs.toFinset) bk_51_4 :=
  buildBucketsBT_sound (by decide) gp_51 W_51_ok P_51_ok autos_51_ok bk_51_3_ok chk_51_4
def nd_51_5_0 : List NodeSpec := [([163,0,1,2,3,4],[],[0,1]),([10,61,2,124,4,5],[],[0]),([10,113,2,3,4,94],[],[0]),([117,10,61,2,4,5],[],[0]),([105,10,61,23,3,5],[],[0]),([10,113,61,23,3,5],[5,9],[0,1]),([10,88,20,119,4,5],[5,6],[0]),([10,88,20,2,40],[5,7,6],[0]),([43,23,55,3,25,5],[],[0]),([106,43,41,3,5],[13,14,9,15,0],[0]),([128,43,10,2,3,33],[],[]),([106,43,23,3,5,158],[0,14],[]),([106,164,43,23,3,5],[0,14],[0]),([106,43,165,23,3,5],[0,14],[]),([122,10,23,3,25,5],[],[0,1]),([166,106,43,3,5],[0,9,15,12],[0,1]),([167,106,43,3,5],[0,12,9,15],[0]),([43,23,161,3,25,5],[0],[0]),([106,43,90,3,5],[0,9,15],[0]),([104,12,43,2,3],[2,10,1,5],[2,0]),([43,168,2,3,4,5],[],[]),([169,149,3,4,5],[8,9,4],[0]),([43,170,2,3,4,5],[],[]),([43,92,2,3,40,33],[],[0]),([29,49,43,2,114,3],[],[0]),([43,2,65,3,40],[16,17,5,10],[]),([43,2,114,63,4,5],[],[0]),([43,2,171,3,4,5],[],[]),([172,43,2,3,4,5],[],[]),([95,43,2,3,40,33],[],[0]),([106,78,43,3,5],[0,12,9,15],[0,3]),([79,64,123,3,4,5],[],[0]),([43,173,2,3,4,5],[],[]),([43,174,2,3,4,5],[],[]),([43,175,2,3,4,5],[],[]),([43,176,2,3,4,5],[],[]),([43,20,144,3,4,5],[],[]),([104,43,64,2,3,40],[18,10],[0,2]),([104,43,64,2,3],[10,2,1,5],[0]),([118,10,88,20,4,5],[],[0]),([43,64,2,63,3,40],[5],[0]),([43,2,177,3,4,5],[],[]),([149,3,4,178,5],[8,9,4],[0]),([29,49,12,43,64,3],[19],[0]),([105,115,10,2,3,4],[],[0]),([12,43,123,3,4,5],[],[]),([29,49,43,64,20,3],[20],[0]),([79,64,103,3,40,5],[9,21],[0]),([43,2,179,3,4,5],[],[]),([43,68,23,36,5],[9,5],[3]),([106,180,0,1,3,5],[],[0]),([43,64,20,63,4,5],[],[0]),([43,64,20,3,40,33],[17],[0]),([123,68,2,3,4,5],[],[]),([43,181,2,3,98,5],[],[]),([102,149,3,4,5],[8,9,4],[0]),([29,49,43,101,2,3],[],[0]),([104,10,9,2,147,3],[7],[0]),([43,96,2,3,40,33],[],[0]),([43,182,2,3,4,5],[],[]),([43,183,2,3,4,5],[],[]),([43,184,2,3,4,5],[],[]),([185,43,2,103,3,5],[],[]),([43,100,2,3,40,33],[],[0]),([29,49,64,68,2,3],[5,19],[0]),([186,64,2,3,4,5],[3],[]),([29,49,43,92,2,3],[],[0]),([136,68,2,3,4,5],[],[]),([29,49,78,64,2,3],[19],[0]),([78,123,2,3,4,5],[],[]),([64,68,2,3,40,33],[5,16],[0]),([104,79,43,2,3],[2,10,1,5],[0]),([43,2,187,3,4,5],[],[]),([12,43,64,3,40,33],[16],[0]),([29,49,79,64,3],[21,22,19],[0]),([79,64,3,40,4,5],[21],[0]),([79,64,134,3,4,5],[],[0]),([49,43,2,108,103,5],[],[0]),([43,100,2,63,4,5],[7],[0]),([43,2,103,3,148,5],[],[]),([43,188,2,3,4,5],[],[]),([79,64,63,3,4,5],[3],[0]),([149,3,40,4,5],[9,4,8],[0,4,5]),([43,189,2,3,4,5],[],[]),([79,136,64,3,4,5],[3],[0]),([43,123,20,3,4,5],[],[]),([64,157,3,4,5],[21,0],[0]),([79,64,3,40,33],[16,21],[0]),([79,64,3,4,138,5],[],[0]),([106,43,68,3,5],[0,9,12,15],[0,3]),([141,79,64,3,4,5],[],[0]),([43,23,135,3,25,5],[],[0]),([190,149,3,4,5],[9,8,4],[0,5]),([79,64,146,3,4,5],[],[0]),([10,61,23,3,5,94],[5,9,23],[0,1,3]),([79,142,64,3,4,5],[],[0]),([29,49,43,96,2,3],[],[0]),([79,64,3,4,145,5],[],[0]),([43,2,108,3,40,33],[7],[0]),([104,43,2,27,3],[10,2,1,5],[0]),([64,149,3,40,4,5],[14],[0]),([43,101,2,3,40,33],[],[0]),([169,64,149,3,4,5],[0],[0]),([106,43,10,90,3,5],[13,23],[]),([191,43,2,3,4,5],[],[]),([102,79,64,3,40,5],[21],[0]),([29,49,95,43,2,3],[],[0]),([192,64,149,3,4,5],[14,3,11],[0]),([97,149,3,4,5],[3,11,9,24],[0]),([43,2,193,3,4,5],[],[]),([29,49,43,2,108,3],[],[0]),([43,2,108,134,4,5],[7],[0]),([115,10,61,23,3,5],[23,9],[0,3]),([29,49,43,100,2,3],[],[0]),([43,2,194,3,4,5],[],[]),([43,2,108,63,4,5],[7],[0]),([104,43,24,2,3,40],[18,10],[]),([43,2,108,103,40,5],[],[0]),([29,49,67,74,3],[25,26,20,19],[0]),([141,43,2,108,4,5],[],[0]),([149,3,4,98,5],[11,3,9,24],[0]),([64,195,149,3,4,5],[14,3],[0]),([29,64,108,3,4,5],[9],[0,5]),([196,0,1,2,3,4],[],[]),([64,108,103,4,5],[9,3,27],[4,0]),([104,43,24,2,3],[10,1,5],[0]),([64,108,3,40,4,5],[9],[4,0,5]),([104,24,10,9,150,3],[13],[0]),([43,2,74,63,3,40],[5],[0]),([10,9,2,147,3,40],[7],[0]),([43,136,10,2,3,40],[],[]),([106,197,0,1,3,5],[],[]),([43,2,198,3,4,5],[],[]),([64,68,2,63,4,5],[],[0]),([102,67,74,3,40,5],[25],[0]),([128,43,2,103,3,5],[],[]),([29,49,43,20,74,3],[],[0]),([67,74,3,40,4,5],[25],[0]),([43,2,111,3,40,33],[],[0]),([43,136,20,3,4,5],[],[]),([43,20,74,63,4,5],[],[0]),([192,149,3,4,5],[8,9,4],[0]),([67,68,2,63,4,5],[28,6],[0]),([43,2,111,63,4,5],[7],[0]),([129,18,0,1,156,3],[],[0]),([43,136,2,3,4,5],[],[]),([43,112,2,3,40,33],[],[0]),([64,108,3,4,5,33],[27],[0]),([43,199,2,3,4,5],[],[]),([95,43,2,63,4,5],[],[0]),([200,43,2,3,4,5],[],[]),([104,67,43,2,3],[10,1,5,2],[0]),([106,43,165,3,5],[0,12,9,15],[0,1,3]),([79,64,3,4,139,5],[],[0]),([78,136,2,3,4,5],[],[]),([43,20,125,3,4,5],[],[]),([61,201,2,3,4,5],[],[0]),([43,2,114,3,40,33],[],[0]),([43,20,74,3,40,33],[],[0]),([67,43,2,63,3,40],[5,6],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_51_5_0 : checkNodesBT W_51 G_51 fmask_51 P_51 autos_51 bk_51_4 5 nd_51_5_0 = true := by decide +kernel
def nd_51_5_1 : List NodeSpec := [([202,43,2,103,3,5],[],[]),([43,2,203,3,4,5],[],[0]),([67,74,134,3,4,5],[],[0]),([29,49,67,68,2,3],[],[0]),([152,68,2,3,4,5],[],[]),([67,186,2,3,4,5],[],[]),([43,2,103,3,151,5],[29],[]),([106,43,23,156,3,5],[0,14],[]),([43,20,2,63,40],[5,6],[0]),([29,49,43,2,111,3],[],[0]),([149,3,4,5,33],[4,9,8],[0]),([67,68,2,3,40,33],[6],[0]),([29,49,43,112,2,3],[],[0]),([67,74,3,40,33],[17,16,25],[0]),([129,14,0,1,156,3],[],[0]),([141,67,74,3,4,5],[],[0]),([204,61,2,3,4,5],[],[0]),([29,149,3,4,5],[4,9,8],[0,5]),([64,149,3,4,178,5],[],[0]),([43,112,2,63,4,5],[7],[0]),([10,42,23,55,3,5],[23],[0]),([43,205,2,3,4,5],[],[]),([104,43,20,2,3],[10,1,5,2],[2,0]),([195,149,3,4,5],[8,9,4],[0]),([43,206,2,3,4,5],[],[]),([104,43,2,74,3,40],[2,18,10],[0,2]),([104,43,2,74,3],[2,10,1,5],[0]),([49,79,64,103,3,5],[],[0]),([43,2,207,103,3,5],[],[]),([159,14,0,1,3,158],[30],[0]),([208,149,3,4,5],[9,8,4],[0,5]),([104,10,9,155,27,3],[13],[0]),([43,2,209,3,4,5],[],[]),([91,106,43,3,5],[31,0,14,9,15],[0]),([67,74,103,3,40,5],[9,25],[0]),([29,49,43,64,2,3],[19],[0]),([29,64,149,3,4,5],[14,24],[0]),([43,2,210,3,4,5],[],[]),([211,43,2,3,4,5],[],[]),([79,43,2,63,3,40],[5],[0]),([43,64,2,3,40,33],[16],[0]),([104,79,43,2,3,40],[10,18],[0]),([67,74,63,3,4,5],[],[0]),([49,67,74,103,3,5],[],[0]),([159,18,0,1,3,158],[],[0]),([12,43,136,3,4,5],[],[]),([106,212,0,1,3,5],[],[]),([43,2,3,151,33],[17,29],[0]),([104,24,10,9,155,3],[32,13],[0]),([43,2,213,3,4,5],[],[]),([43,2,157,3,40],[16,17,0,10],[0]),([67,74,3,4,139,5],[],[0]),([104,160,10,9,2,3],[1],[0]),([104,67,43,2,3,40],[18,10],[0]),([214,43,2,3,4,5],[],[]),([64,149,3,4,5,33],[14,24],[0]),([106,0,1,215,3,5],[],[]),([104,43,2,27,3,40],[10,18],[0]),([149,103,3,4,5],[8,9,4],[0,4]),([68,153,2,3,4,5],[],[]),([43,123,2,3,4,5],[],[]),([78,64,2,3,40,33],[16],[0]),([106,14,0,1,216,5],[33],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_51_5_1 : checkNodesBT W_51 G_51 fmask_51 P_51 autos_51 bk_51_4 5 nd_51_5_1 = true := by decide +kernel
def nodes_51_5 : List NodeSpec := nd_51_5_0 ++ nd_51_5_1
set_option maxRecDepth 500000 in
lemma chk_51_5 : checkNodesBT W_51 G_51 fmask_51 P_51 autos_51 bk_51_4 5 nodes_51_5 = true := by
  unfold nodes_51_5 checkNodesBT; simp only [List.all_append, Bool.and_eq_true]
  exact ⟨chk_51_5_0, chk_51_5_1⟩
def bk_51_5 : BT (List (List Nat)) := buildBucketsBT W_51 nodes_51_5
set_option maxRecDepth 500000 in
lemma bk_51_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_51 5 xs.toFinset) bk_51_5 :=
  buildBucketsBT_sound (by decide) gp_51 W_51_ok P_51_ok autos_51_ok bk_51_4_ok chk_51_5
def nd_51_6_0 : List NodeSpec := [([105,115,0,1,2,3,4],[],[0,1]),([117,0,1,61,2,4,5],[34,35],[0,1]),([118,0,1,88,20,4,5],[],[0,2]),([0,1,88,20,119,4,5],[5,6],[0,2]),([83,87,0,1,2,3,4],[],[0]),([120,0,1,2,56,4,5],[34,35],[]),([121,0,1,20,86,4,5],[],[]),([122,10,23,2,3,4,5],[],[0]),([10,9,23,55,3,25,5],[23],[0,1]),([10,42,23,41,3,5],[13,36,14,9,37,38,39],[0]),([105,10,61,2,3,4,5],[],[0]),([10,113,61,2,3,4,5],[5,3,9,28],[0]),([29,49,10,26,20,2],[40,5,7,6],[2]),([43,10,23,90,3,25,5],[14,0],[0]),([29,49,43,10,64,2,3],[20,13],[4]),([43,10,123,2,3,4,5],[41,7,42],[]),([43,10,64,2,3,40,33],[17,13],[0,4]),([49,43,97,10,2,3,5],[],[]),([0,1,61,2,124,4,5],[34],[0,1]),([43,10,2,125,3,4,5],[43,41],[]),([29,43,100,2,3,4,5],[7,14],[0]),([43,10,126,74,3,4,5],[44,13],[]),([0,1,20,86,127,4,5],[5,45,40],[]),([128,43,10,2,3,4,5],[41,44],[0]),([128,43,2,3,4,5],[44,14,10,46],[0,5]),([106,43,3,5],[9],[0,1,6,3]),([12,43,64,3,4,5,33],[47,9,48,49],[0]),([29,49,12,43,2,3],[40,5,19,20],[0]),([29,49,43,20,2,3],[40,5,20,19],[0]),([29,43,2,114,3,4,5],[7,50],[0]),([43,2,114,3,4,5,33],[14,27,7],[0]),([43,2,114,3,40,4,5],[50,51,18,10],[0]),([129,106,18,0,1,3,5],[33,5,12,52],[0]),([19,30,43,68,3,5],[9,27,53,54],[0,3]),([43,23,41,3,25,5],[0,14,9,55],[0]),([43,130,2,3,4,5],[23,46,9,50,18,7],[]),([43,68,2,36,4,5],[9,44,5,3],[3,0]),([43,131,2,3,4,5],[23,46,14,3,44,50,18,7],[3]),([43,126,74,3,4,5],[44,14,47,9,23,7],[]),([43,68,130,2,3,4,5],[46,44,23],[]),([43,68,23,3,25,5],[9,37,5,55],[3,0]),([95,43,2,3,4,5,33],[14,7,56,50,9],[0]),([43,2,27,3,40,4,5],[18,3,10,57,13],[]),([10,9,2,65,3,40],[13,58,59,5,32],[0]),([43,132,2,93,3,4,5],[50,3,9,57,5],[]),([67,43,2,3,40,33],[16,17,5,10,18,60],[0]),([43,68,2,133,3,4,5],[44,46,14],[]),([19,30,78,43,3,5],[9,27,53,54],[0,3]),([29,43,96,2,3,4,5],[7,14],[0]),([43,96,2,3,40,4,5],[18,10,27,14],[0]),([78,43,23,3,25,5],[9,37,23,5,55],[3,0]),([43,64,2,134,3,4,5],[14,40],[0]),([43,10,2,107,3,5,33],[50,18],[]),([43,23,2,135,3,4,5],[18,0,7],[0]),([43,136,64,2,3,4,5],[44,3,7],[0]),([0,1,2,56,137,4,5],[34],[]),([43,136,2,3,4,5],[7,3,44,46,14,23],[0]),([106,43,10,23,3,5],[13,0,9,12],[1,0,3,6]),([43,2,3,4,138,5],[44,3,46,10],[0]),([102,43,64,2,3,40,5],[61,57,9],[0]),([43,64,2,3,4,139,5],[18,10,3,14],[0]),([49,43,64,2,103,3,5],[23,9],[0]),([43,64,2,103,3,40,5],[57,9,61],[0]),([24,140,2,3,4,5],[50,5,7],[]),([141,43,64,2,3,4,5],[18,14],[0]),([12,43,64,3,40,4,5],[62,9,6],[0]),([24,10,72,2,3,40],[63,64,13,5,18,32,17],[]),([29,43,64,20,3,4,5],[14,65],[0]),([29,12,43,64,3,4,5],[14,66],[0]),([43,64,20,3,4,5,33],[67,51,49,14,27],[0]),([10,26,23,36,5],[9,5],[]),([43,142,64,2,3,4,5],[10,3,44],[0]),([43,143,2,3,4,98,5],[23,18,61],[0]),([106,43,23,3,5],[0,23,9],[0,3,6]),([29,49,43,64,2,3],[61,68,19,20,5],[0]),([43,10,2,144,3,4,5],[7,41],[]),([29,43,101,2,3,4,5],[7,9],[0]),([43,92,2,3,40,4,5],[18,50,10],[0]),([95,43,2,3,40,4,5],[18,10],[0]),([95,43,132,2,3,4,5],[14,5,3,57,27],[]),([115,10,61,2,3,4,5],[23,9],[0,3]),([43,101,2,3,4,5,33],[69,50,7,9,27],[0]),([43,101,2,3,40,4,5],[18,9,10],[0]),([43,100,2,3,40,4,5],[18,10],[0]),([43,64,2,3,4,145,5],[18,10,3,14],[0]),([43,2,74,134,3,4,5],[3,40],[0]),([43,10,2,3,4,138,5],[3,44],[]),([29,64,68,2,3,4,5],[50,5,66],[0]),([64,68,2,3,4,5,33],[5,50,47,9,27],[0]),([29,49,79,43,2,3],[70,71,19,20,5],[0]),([43,2,111,3,4,5,33],[9,3,7,27],[0]),([43,64,146,2,3,4,5],[18,7],[0,5]),([10,0,1,2,147,3,40],[1],[0]),([29,43,2,111,3,4,5],[7,27],[0]),([79,43,2,134,3,4,5],[3,40,6],[0]),([79,43,2,63,3,4,5],[3,5],[0]),([43,2,3,4,148,5],[62,72,10,46],[0,5]),([43,2,27,3,40,33],[16,17,5,18,10],[0]),([79,43,2,3,4,139,5],[23,28,10,18],[0]),([49,79,43,2,103,3,5],[23,5,57],[0]),([49,67,43,2,103,3,5],[23,40,6],[0]),([79,43,2,103,3,40,5],[5,57,40,6,9,70],[0]),([43,10,2,74,3,40,33],[17,13,18],[0,4]),([0,1,2,85,3,4,84],[],[0]),([78,64,2,3,4,5,33],[47,44,49,9,27],[0]),([43,2,74,3,40,4,5],[3,14,18,10,73],[0]),([29,79,64,3,4,5],[3,66,14,21,9,22],[0,5]),([67,132,68,2,3,4,5],[44,27,28,50],[]),([102,79,43,2,3,40,5],[28,23,70,10,6],[0]),([79,97,64,3,4,5],[3,74,14,9,22,21],[0]),([29,43,92,2,3,4,5],[7,50],[0]),([64,149,3,4,5],[3,14,9],[0,5]),([64,108,3,4,5],[9,3,27],[0,5]),([149,3,4,5],[9],[0,5]),([0,1,113,2,3,4,94],[],[0,1]),([29,49,43,2,74,3],[73,75,20,19,5],[0]),([43,92,2,3,4,5,33],[48,50,7,9,3],[0]),([12,43,2,3,40,33],[16,17,5,6],[0]),([43,131,68,2,3,4,5],[44,46,23],[]),([104,24,10,9,2,3],[32,1,13,5],[0]),([104,24,10,0,1,150,3],[30,13],[0]),([102,67,43,2,3,40,5],[60,10,57],[0]),([43,2,74,63,3,4,5],[14,3,5],[0]),([10,72,20,2,3,40],[13,5,76,63,18,6],[0]),([43,2,144,3,4,5],[47,7,14,46,0],[0]),([43,23,36,3,5],[9,5],[0,3]),([102,43,2,74,3,40,5],[73,9,57,10],[0]),([43,2,74,103,3,40,5],[9,57,73],[0]),([43,96,2,3,4,5,33],[44,49,7,14,27],[0]),([43,2,3,4,151,5],[72,14,3,10,46],[0,5]),([141,43,2,74,3,4,5],[18,3],[0]),([78,64,2,3,40,4,5],[62,50,6,27,9],[0]),([43,112,2,3,40,4,5],[18,9,10],[0]),([75,43,2,3,4,5],[44,18,41,77,7,62,72],[]),([43,2,111,3,40,4,5],[18,27,10],[0]),([43,64,2,3,40,33],[16,17,61,5,18,10],[0,2]),([43,20,74,3,4,5,33],[14,27],[0]),([43,97,143,2,3,4,5],[18,7,61,68,57],[0]),([43,110,2,3,5,33],[28,44,18,78,14],[]),([79,64,3,4,98,5],[79,14,9,22,21],[0]),([43,20,74,3,40,4,5],[27,14,6],[0]),([12,10,72,2,3,40],[13,5,63,7,80,6],[]),([129,106,14,0,1,3,5],[33,13,9,81,52,82,30],[0]),([102,79,64,3,4,5],[3,27,14,9,22,21],[0]),([29,67,74,3,4,5],[44,65,25,3,66,9,26],[0,5]),([29,49,67,43,2,3],[60,83,19,20,5],[0]),([67,43,2,103,3,40,5],[57,9,60],[0]),([152,43,2,3,4,5],[3,7,14,46,18,65,60,84],[0,5]),([67,43,2,63,3,4,5],[44,5,28,7,6,50],[0]),([43,153,2,3,4,5],[3,7,67,14,46,23],[0]),([43,2,125,3,4,5],[7,14,3,66,46,85,18],[0,5]),([43,112,2,3,4,5,33],[44,49,7,9],[0]),([43,2,74,3,40,33],[17,16,73,5,18,10],[0,2]),([29,49,43,2,27,3],[86,13,19,20,5],[0]),([43,64,2,3,4,138,5],[18,3,44],[0]),([43,23,2,55,3,4,5],[18,13,7,0,14,57],[0]),([141,67,43,2,3,4,5],[44,18,40],[0]),([67,68,2,3,4,5,33],[28,6,44,50,9],[0]),([43,23,90,3,25,5],[14,0,9,55],[0]),([10,88,20,2,4,5],[5,7,6],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_51_6_0 : checkNodesBT W_51 G_51 fmask_51 P_51 autos_51 bk_51_5 6 nd_51_6_0 = true := by decide +kernel
def nd_51_6_1 : List NodeSpec := [([49,43,2,116,3,5],[44,3,71,57,28,7],[]),([67,68,2,3,4,154,5],[28,50,9,27],[]),([43,64,2,63,3,4,5],[44,50,5,14,3],[0]),([67,74,3,40,4,5],[72,62,9,25,26],[0,4,5]),([43,100,2,3,4,5,33],[87,50,7,14,27],[0]),([67,74,103,3,4,5],[9,27,26,25],[0,4]),([104,10,0,1,155,27,3],[13,88,52],[0]),([79,43,2,3,40,33],[16,17,5,10,18,70],[0]),([67,140,2,3,4,5],[0,50,49,7],[]),([29,95,43,2,3,4,5],[7,14],[0]),([29,43,64,2,3,4,5],[7,14,66],[0]),([91,43,23,3,25,5],[14,0,9,55],[0]),([67,43,2,3,4,139,5],[44,10,18],[0]),([29,78,64,2,3,4,5],[50,66],[0]),([43,64,2,3,4,5,33],[47,44,50,7,14],[0]),([104,24,10,0,1,155,3],[89,30,13,52],[0]),([67,43,2,134,3,4,5],[44,40,5,57],[0]),([104,24,0,1,150,3],[33,88,90,91,13,52],[]),([67,43,2,3,40,4,5],[44,10,18,60],[0]),([67,74,3,4,5,33],[67,47,9,25,26],[0]),([43,2,108,103,4,5],[9,27,49,44,23],[0,4]),([10,72,2,27,3,40],[13,63,92,5,18,32],[]),([43,20,2,3,40,33],[17,5,16,18,6],[0]),([106,14,0,1,156,3,5],[13,93,33],[0]),([43,64,20,3,40,4,5],[72,14,6,27],[0]),([10,26,20,2,40,33],[5,7,6],[0,2]),([43,2,157,3,4,5],[47,67,46,0,7,70],[0]),([106,18,0,1,3,5,158],[93,33,12,5],[0]),([106,14,0,1,3,5,158],[82,30,33,93,13],[0]),([67,68,2,3,40,4,5],[44,6],[0]),([159,106,18,0,1,3,5],[30,5,12],[0]),([29,67,68,2,3,4,5],[44,28],[0]),([104,160,10,0,1,2,3],[94,1,33],[0]),([29,43,112,2,3,4,5],[7,9],[0]),([79,43,2,3,40,4,5],[3,10,18,57,70],[0]),([79,64,3,4,5,33],[47,21,14,9,22],[0]),([104,24,10,9,2,3,40],[18,32,13,1],[0]),([29,43,20,74,3,4,5],[3],[0]),([49,43,2,74,103,3,5],[23],[0]),([79,64,103,3,4,5],[27,9,22,21],[0,4]),([29,49,43,24,2,3],[86,13,95,19,20,5],[0]),([104,10,9,2,27,3],[1,13,96,32,5],[0]),([43,64,2,3,40,4,5],[62,18,10,14],[0]),([43,24,2,3,40,4,5],[44,97,13],[]),([10,61,23,3,5],[5,9,23],[0,3]),([43,23,2,161,3,4,5],[18,0,7],[0]),([104,10,9,2,27,3,40],[32,13,18],[0]),([43,24,2,3,40,33],[98,16,17,5,10,18],[0]),([29,43,2,108,3,4,5],[7,27,18],[0,5]),([141,79,43,2,3,4,5],[3,18,5,57],[0]),([106,18,0,1,156,3,5],[93,5,12,33],[0]),([29,49,43,10,2,74,3],[20,13],[4]),([159,106,14,0,1,3,5],[30,13],[0]),([43,2,74,3,4,139,5],[3,14,18,10],[0]),([43,2,133,3,4,5],[9,28,18,7],[]),([79,64,3,40,4,5],[62,14,9,21,22],[0,4,5]),([102,67,74,3,4,5],[44,9,27,26,25],[0]),([43,2,108,3,40,4,5],[18,27,10,57],[0,4,5]),([43,2,65,3,4,5],[47,67,5,7,86],[0]),([43,123,2,3,4,5],[7,3,44,46,18,23],[0]),([162,43,2,3,4,5],[44,7,3,85,46,18],[0,5]),([43,2,108,3,4,5,33],[7,27],[0]),([43,20,2,63,4,5],[5,3,7,6],[0]),([64,68,2,3,40,4,5],[5,50,6,62,27,9],[0]),([104,24,0,1,150,3,40],[33],[]),([104,10,0,1,2,147,3],[94,1,33,13,52],[0]),([43,2,57,3,4,5],[44,7,41,40,18],[]),([43,136,10,2,3,4,5],[7,41],[0]),([43,64,123,2,3,4,5],[7],[0]),([10,61,2,3,4,5,94],[5,9,3],[0,3]),([49,43,2,47,3,5],[3,13,57,5,7],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_51_6_1 : checkNodesBT W_51 G_51 fmask_51 P_51 autos_51 bk_51_5 6 nd_51_6_1 = true := by decide +kernel
def nodes_51_6 : List NodeSpec := nd_51_6_0 ++ nd_51_6_1
set_option maxRecDepth 500000 in
lemma chk_51_6 : checkNodesBT W_51 G_51 fmask_51 P_51 autos_51 bk_51_5 6 nodes_51_6 = true := by
  unfold nodes_51_6 checkNodesBT; simp only [List.all_append, Bool.and_eq_true]
  exact ⟨chk_51_6_0, chk_51_6_1⟩
def bk_51_6 : BT (List (List Nat)) := buildBucketsBT W_51 nodes_51_6
set_option maxRecDepth 500000 in
lemma bk_51_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_51 6 xs.toFinset) bk_51_6 :=
  buildBucketsBT_sound (by decide) gp_51 W_51_ok P_51_ok autos_51_ok bk_51_5_ok chk_51_6
def nodes_51_7 : List NodeSpec := [([29,49,0,1,26,20,2],[28,6,30],[2,0]),([83,0,1,2,56,3,4,5],[35,99],[0]),([0,1,2,56,3,4,5,84],[5,44,9,30,99,35,27],[0,3]),([0,1,2,85,56,3,4,5],[44,5,27,9,99,28,35],[0]),([0,1,20,2,86,4,5],[5,45,100,33,28,6],[0]),([29,49,12,8,17,2,3],[40,5,101],[2,0]),([10,42,23,3,5],[23,13,14,9,5],[0,3,6]),([29,49,8,17,20,2,3],[40,5,101],[2,0]),([87,0,1,2,56,3,4,5],[99,30,9,35],[0,3]),([10,9,23,41,3,25,5],[13,14,9,37,38,102],[0,1]),([10,9,20,2,63,4,5],[5,103,3,7,6],[0,2]),([10,61,2,3,4,5],[5,3],[0,3]),([10,9,23,2,55,3,4,5],[23,18,13,7,38,14,57],[0]),([29,10,26,20,2,4,5],[104,40,46,28,27,14],[0]),([10,26,20,2,4,5,33],[5,7,6,105,14,27,40],[0]),([0,1,88,20,2,4,5],[5,45,100,7,28,6],[0,2]),([30,10,26,20,4,5],[104,3,46,5,14,6,9,27,28],[]),([10,26,20,23,4,5],[9,104,5,106,3,6,28],[]),([10,26,2,36,4,5],[5,3,107,18],[0]),([19,30,43,10,3,5],[23,3,5,53],[1,3]),([43,10,23,2,3,4,5],[23,44,50,9,13,7,18],[3]),([10,89,2,3,4,5],[23,3,13,5,50],[3]),([43,10,23,3,25,5],[23,14,37,5],[0,3,1,6]),([43,10,23,2,90,3,4,5],[14,0,44],[0]),([43,10,64,2,3,4,5,33],[67,50,13,14,3],[0]),([43,10,64,2,3,40,4,5],[72,50,13,18,57,7,3,14],[0]),([43,10,2,74,3,4,5,33],[67,50,13,3,7],[0,5]),([43,10,2,74,3,40,4,5],[72,50,13,3,18],[2,0]),([19,30,43,3,5],[23,3,9],[0,3]),([43,2,3,4,31,5],[14,108,6,23,50,44],[]),([43,2,46,3,4,5],[14,9,44,50,23,18,7],[3]),([43,10,2,3,4,35,5],[23,5,44,50,18,3],[3]),([43,23,2,3,4,5],[44,14,50,9,23,7,18],[3]),([43,2,3,4,35,5],[3,6,23,50,44],[3]),([43,23,2,90,3,4,5],[14,0,44,9,109],[0]),([43,2,90,3,4,5],[14,50,57,3,49,110,111,18,7],[]),([29,12,43,2,3,4,5],[7,3,9,40,49,48,6,66,65,23,57,28],[0]),([29,43,24,2,3,4,5],[44,50,7,97,86,14,104,40,112,66,65,23,57,13],[0]),([12,43,2,3,4,5,33],[47,67,5,7,18,9,48,49,6,40],[0]),([91,43,23,2,3,4,5],[14,50,0,9,109],[0]),([43,92,2,3,4,5],[3,9,50,57,23,18,7],[0,5]),([43,64,2,3,4,5],[3,44,50,46,9,23,57,7,18],[0,5]),([19,43,68,2,3,4,5],[44,50,9,5,40,6,113,114],[0,3]),([43,68,2,93,3,4,5],[50,9,27,0,85,28,5,6,40],[7,3,0,5]),([19,78,43,2,3,4,5],[23,44,49,9,5,40,6,113,114],[3,0]),([0,1,61,2,3,4,5,94],[5,3,23,99,35,9],[0,1,3]),([95,43,2,3,4,5],[3,14,46,44,23,57,7,18,50,9,56],[0,5]),([39,10,26,2,4,5],[57,44,46,18,5,9,27,28],[]),([78,43,2,3,4,25,5],[9,3,115,5,49,116,27,6,40],[3,0]),([43,89,2,3,4,5],[23,3,49,7,18],[3]),([12,43,23,3,4,5],[3,9,49,28,6],[3]),([78,43,23,2,3,4,5],[9,49,44,117,23,57,109,28,40,6],[3,0]),([43,96,2,3,4,5],[46,44,14,9,23,57,7,18],[0,5]),([67,43,2,3,4,5,33],[47,67,5,57,7,18,60,14,9,83],[0,5]),([43,64,2,3,4,5,33],[47,67,44,61,50,5,57,14,3,9,68],[0]),([43,23,3,25,5],[14,9,23],[0,3,6]),([43,68,23,2,3,4,5],[9,50,44,117,28,109,40,6],[3,0]),([12,10,9,2,3,40,33],[13,5,6,59],[0,2]),([43,97,64,2,3,4,5],[44,3,50,14,9,23,68,61],[0,5]),([43,64,2,3,4,98,5],[50,14,9,68,57,10,61],[0]),([79,64,3,4,5],[3,14,9],[0,5]),([12,43,64,3,4,5],[3,44,9,49,28,6],[0,5]),([43,99,2,3,4,5],[50,9,57,7,18],[]),([29,43,2,27,3,4,5],[44,50,86,3,14,66,104,40,65,57,23,13],[0,5]),([95,43,68,2,3,4,5],[44,9,46,3,50,5,28,40,6],[7,3]),([43,24,2,3,40,4,5],[118,62,72,119,97,10,18,57,14,86,13],[0]),([43,100,2,3,4,5],[50,14,9,23,57,7,18],[0,5]),([10,72,20,2,3,4,5],[5,76,120],[0]),([64,68,2,3,4,5],[50,46,44,28,6,3,9],[0,5]),([43,2,36,3,4,5],[3,44,5,50,18,7],[0,3]),([78,64,2,3,4,5],[44,9,28,6],[0,5]),([29,79,43,2,3,4,5],[7,3,70,66,50,44,9,65,5,57,71],[0,5]),([79,43,2,3,4,5,33],[47,67,5,57,7,18,70,9,71],[0]),([43,97,2,3,4,5],[23,57,3,14,50,74,28,121,7,18],[]),([43,20,23,3,4,5],[14,49,9,28,46,23,6],[3]),([43,2,27,3,40,4,5],[62,72,119,18,10,57,23,7,86,13],[0]),([43,101,2,3,4,5],[46,9,3,50,49,57,23,18,7],[0,5]),([102,79,43,2,3,4,5],[23,3,28,27,44,50,71,70,9,40,6,49],[0]),([10,9,20,2,3,40,33],[5,6,59],[0,2]),([43,2,74,3,4,5,33],[67,47,50,73,5,57,9,75],[0]),([30,43,20,3,4,5],[3,49,5,14,6,27,28],[3]),([102,43,2,74,3,4,5],[44,50,14,3,23,27,28,75,73,49,6,40],[0]),([43,20,2,3,4,5,33],[67,51,5,49,47,18,7,14,27,6,40],[0]),([29,49,10,9,20,2,3],[40,5,6,122],[2,0]),([43,2,74,103,3,4,5],[49,9,27,57,5,6,40,75,73],[0,4]),([10,9,2,27,3,40,4,5],[13,18,3,32,57],[0]),([12,10,72,2,3,4,5],[13,5,120,7,80],[0]),([29,43,20,2,3,4,5],[40,49,51,27,14,6,65,66,57,23,28],[0]),([43,20,74,3,4,5],[44,14,27,49,28,6],[0,5]),([104,10,0,1,2,27,3],[13,1,90,89,88,52,5],[0]),([10,26,2,46,4,5],[9,44,23,5,18],[]),([67,43,2,3,40,4,5],[62,72,5,10,18,57,14,9,60,83],[0,4,5]),([102,67,43,2,3,4,5],[23,44,28,9,50,83,60,27,40,6,49],[0]),([105,0,1,61,2,3,4,5],[35,99],[0,1]),([106,14,0,1,3,5],[30,13,82,52,5,33,93],[0]),([10,26,23,3,25,5],[9,5],[0,1,3]),([43,68,2,3,4,25,5],[9,115,5,44,50,3,116,27,46,6,40],[3,0]),([67,68,2,3,4,5],[44,27,50,28,6,9],[0,5]),([29,49,12,10,9,2,3],[40,5,6,122],[2,0]),([29,43,2,74,3,4,5],[44,50,14,3,7,73,66,9,65,5,57,75],[0,5]),([43,10,2,107,3,4,5],[3,23,50,27,57,123,7,18],[0]),([67,74,3,4,5],[44,3,9],[0,5]),([104,24,10,0,1,2,3,40],[30,18,89,13,1],[0]),([24,10,72,2,3,4,5],[120,64,13,5,44],[0]),([24,10,9,2,3,40,33],[59,98,13,5,18,32,17],[0]),([102,43,64,2,3,4,5],[44,50,23,28,9,68,61,27,49,40,6],[0]),([43,2,108,3,4,5],[3,44,57,27,23,18,7],[0,5]),([10,26,20,2,40,4,5],[119,7,6,27,14,57,28],[0]),([43,109,2,3,4,5],[23,14,50,49,3,18,7,124],[]),([43,110,2,3,4,5],[3,44,28,14,7,18,125],[0]),([79,43,2,103,3,4,5],[9,27,5,57,40,6,49,44,71,70],[0,4]),([43,2,27,3,4,5,33],[47,67,5,18,7,86],[0]),([43,10,2,3,4,31,5],[23,5,44,50,18,126,108,14],[]),([43,24,2,3,4,5,33],[127,47,67,5,7,18,97,14,86],[0]),([43,64,2,103,3,4,5],[27,9,49,5,57,40,6,68,61],[0,4]),([104,24,10,0,1,2,3],[89,1,13,30,5],[0]),([104,24,0,1,2,3,40],[33,94,88,91,7,23,13,128,52,129],[0]),([43,2,111,3,4,5],[3,46,27,14,50,49,57,23,18,7],[0,5]),([43,2,107,3,4,5],[3,23,57,50,49,123,28,7,18],[]),([10,9,2,27,3,40,33],[13,130,59,5,18,32],[0]),([10,9,2,65,3,4,5],[13,131,132,5,7,86],[0]),([104,24,0,1,2,3],[33,88,94,13,128,52,129,91],[0]),([29,43,10,2,74,3,4,5],[97,44,7,65,13,57],[0]),([29,43,64,2,3,4,5],[44,50,7,61,3,14,9,66,65,5,57,68],[0,5]),([43,2,38,3,4,5],[3,44,57,50,9,7,18],[3]),([19,30,10,26,3,5],[23,3,9,5],[1,3]),([43,2,47,3,4,5],[3,44,57,46,28,7,18],[0]),([43,2,74,3,40,4,5],[72,62,50,5,18,10,57,9,73,75],[0,2,4,5]),([104,28,0,1,2,3,40],[33,94,13,5,52,88],[]),([43,64,20,3,4,5],[3,44,14,9,49,28,6],[0,5]),([10,0,1,2,65,3,40],[13,52,30,133,134,135,5,17,89],[0]),([43,112,2,3,4,5],[3,44,14,9,57,23,18,7],[0,5]),([75,10,9,2,3,4,5],[41,44,136,18,77,7,137],[0]),([43,45,2,3,4,5],[3,44,27,7,18,57],[]),([24,10,9,2,3,40,4,5],[44,97,13],[0]),([43,20,2,3,40,4,5],[72,6,49,51,62,27,14,57,23,28],[0]),([29,49,24,10,9,2,3],[86,13,122,95,5],[0]),([43,64,2,3,40,4,5],[62,72,50,5,18,10,57,14,3,9,61,68],[0,2,4,5]),([29,49,10,9,2,27,3],[86,13,138,122,5],[0]),([43,23,2,41,3,4,5],[44,0,14,41,9,109],[0]),([104,28,0,1,2,3],[33,13,94,52,88,5],[]),([12,43,2,3,40,4,5],[62,72,6,9,23,57,49,48,28],[0]),([10,9,77,27,3,4,5],[86,14,9,57],[]),([0,1,113,61,2,3,4,5],[3,5,27,99,9,28,35],[0,1]),([14,0,1,23,36,5],[13,52,30,93,9,5,139],[]),([43,97,10,2,3,4,5],[23,3,14,49,121,18,7,57],[0]),([10,72,2,27,3,4,5],[44,13,120,92,5],[0]),([43,2,114,3,4,5],[14,50,27,57,23,18,7],[0,5]),([73,0,1,2,3,40],[13,5,33,88,52],[]),([49,10,9,2,47,3,5],[44,13,57,3,5,7],[0]),([29,67,43,2,3,4,5],[7,44,60,65,3,14,9,5,23,57,66,83],[0,5]),([67,43,2,103,3,4,5],[9,27,5,57,40,6,49,44,83,60],[0,4]),([79,43,2,3,40,4,5],[62,5,10,18,23,57,7,72,9,70,71],[0,4,5]),([106,18,0,1,3,5],[30,5,82,52,27,93,33],[0]),([115,0,1,61,2,3,4,5],[99,23,9,35],[0,1,3]),([29,43,10,64,2,3,4,5],[50,44,7,65,13],[0,5]),([43,2,116,3,4,5],[3,44,57,46,28,7,18],[0]),([104,10,0,1,2,27,3,40],[89,13,88,1,18],[0]),([39,43,2,3,4,5],[44,57,50,23,46,3,7,18,14,27],[3]),([10,9,2,57,3,4,5],[86,140,40,18,23],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_51_7 : checkNodesBT W_51 G_51 fmask_51 P_51 autos_51 bk_51_6 7 nodes_51_7 = true := by decide +kernel
def bk_51_7 : BT (List (List Nat)) := buildBucketsBT W_51 nodes_51_7
set_option maxRecDepth 500000 in
lemma bk_51_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_51 7 xs.toFinset) bk_51_7 :=
  buildBucketsBT_sound (by decide) gp_51 W_51_ok P_51_ok autos_51_ok bk_51_6_ok chk_51_7
def nodes_51_8 : List NodeSpec := [([12,48,0,1,2,3,4,5],[100,141,142,143,13,5,144,145,146,46,147],[]),([29,8,17,20,2,3,4,5],[46,147,49,7,14,27,40,6,148,149,57,23,28],[0]),([39,8,17,2,3,4,5],[150,14,143,57,50,23,3,7,18,151,9,27],[0]),([29,49,0,1,16,2,3],[141,23,13,7,88,5,91],[4]),([19,30,10,0,1,3,5],[23,3,13,142,5,33,93],[1]),([10,0,1,23,2,3,4,5],[23,3,41,152,30,44,13,142,9,33,93,7,18],[]),([0,1,50,20,3,4,5],[3,100,153,154,155,156,14,82,91],[]),([0,1,51,2,3,4,5],[57,157,158,14,82,151,91],[]),([19,30,0,1,26,3,5],[23,3,93,9,33],[1,0,3]),([0,1,26,2,36,4,5],[3,23,93,107,18,159],[0,1]),([29,49,0,1,22,2,3],[7,23,88,156,91],[4]),([12,0,1,52,2,3,4,5],[160,7,86,23,100,161,142,145,162,104,146,28,40],[]),([12,10,9,2,3,40,4,5],[13,119,6,137,9,57,28],[0]),([0,1,22,53,3,4,5],[3,153,82,6],[]),([49,10,0,1,2,47,3,5],[30,44,13,3,163,5,52,164,165,93,7],[0]),([54,0,1,2,3,4,5],[157,44,13,100,99,35,97,5],[]),([10,9,2,3,4,35,5],[23,3,13,5,44,18,6],[0]),([10,0,1,23,2,55,3,4,5],[166,30,44,14,117,13,134,57],[0,1]),([10,9,23,3,25,5],[23,13,14,9,5],[0,3,1,6]),([0,1,2,56,3,4,5],[44,155,30,35,99,167],[0,3]),([10,0,1,2,57,3,4,5],[86,160,30,168,44,165,161,135,40,18],[0]),([12,58,0,1,2,3,4,5],[100,86,142,44,13,5,169,145,146,104,45],[]),([0,1,20,2,3,4,59,5],[13,44,5,156,52,45,170,57,155,171,172,173],[0]),([12,60,0,1,2,3,4,5],[100,44,142,13,52,5,174,7,40],[]),([30,0,1,26,20,4,5],[175,3,104,46,159,14,6,153,28,27],[0]),([14,0,1,2,36,4,5],[13,52,100,93,97,5],[0]),([29,49,10,0,1,20,2,3],[40,5,135,88,176],[2,0]),([58,0,1,20,2,3,4,5],[46,146,104,155,86,172,44,145,13,5,45,169],[]),([10,9,20,2,3,4,5,33],[5,177,132,18,7,14,27,6,40],[0]),([19,30,6,10,1,3,5],[178,3,5,145,27],[1]),([29,49,0,1,9,20,2,3],[28,6,88,135,179],[2,0]),([19,30,10,7,1,3,5],[13,180,142,3,145,23,5,27],[1]),([10,7,1,2,36,4,5],[13,3,142,154,145,180,5,27],[1]),([29,49,12,0,1,9,2,3],[28,6,30,91,179],[2,0]),([0,1,61,2,3,4,5],[3,23,35,99,181],[0,1,3]),([34,7,1,2,3,4,5],[44,142,157,156,13,135],[]),([24,0,1,2,3,40,33],[23,13,7,88,156,91,33,98,52,182],[0]),([10,9,2,36,3,4,5],[5,23,46,3,18,7],[0,1,3]),([43,2,3,4,25,5],[3,5,23,44,46,7],[0,3]),([29,49,12,10,0,1,2,3],[40,5,91,30,176],[2,0]),([0,1,52,20,2,3,4,5],[146,104,160,7,28,46,86,23,40,155,172,162,18,145],[]),([62,0,1,2,3,4,5],[157,13,41,150,100,44,35,99,52,97,5],[]),([29,12,10,9,2,3,4,5],[7,3,9,40,28,183],[0]),([12,10,9,2,3,4,5,33],[13,5,184,132,7,18,9,6,40],[0]),([10,9,2,38,3,4,5],[185,3,18,57,7],[0]),([19,30,10,9,3,5],[23,3,13,9,5],[1,0,3]),([10,9,20,2,3,40,4,5],[119,6,137,27,14,57,23,28],[0]),([30,10,9,20,3,4,5],[104,3,5,14,6,27,28],[0]),([10,9,20,23,3,4,5],[106,14,23,3,6,28],[0]),([10,0,1,20,2,63,4,5],[5,45,135,88,156,3,7,40],[0,2]),([19,10,26,2,3,4,5],[104,23,44,46,9,7,6,5],[0,7,3]),([29,0,1,26,20,2,4,5],[175,186,104,46,28,187,14,188,40,23,30],[0]),([19,43,10,2,3,4,5],[23,50,44,41,46,5,7,14,3,113],[0,3]),([43,10,2,3,4,25,5],[23,3,5,44,50,115,41,7],[0,3]),([0,1,22,2,3,40,4,5],[7,23,88,156,6,33],[]),([43,10,64,2,3,4,5],[3,44,50,41,46,49,23,7,14],[0,5]),([48,0,1,20,2,3,4,5],[104,146,46,155,141,172,143,145,13,5,147,144],[]),([10,0,1,2,65,3,4,5],[13,52,30,189,155,134,135,5,165,93,7,86],[0]),([37,7,1,2,3,4,5],[44,154,157,156,13,5,180],[]),([66,0,1,2,3,4,5],[157,13,158,88,41,150,97,180,27],[]),([67,43,2,3,4,5],[3,44,46,23,7,14,9],[0,5]),([43,68,2,3,4,5],[46,44,50,3,23,7],[0,7,3,5,8,9]),([29,49,10,0,1,2,27,3],[86,13,176,88,135,5],[0]),([43,64,2,3,4,5],[3,44,50,46,9,23,7],[0,5]),([19,30,0,1,15,3,5],[23,153,13,142,9,93,5,33],[1]),([10,9,23,2,41,3,4,5],[190,14,9,57,117,38,191],[0]),([10,26,20,2,4,5],[46,104,14,27],[1,0,10,5]),([18,0,1,23,3,25,5],[23,13,142,9,5,30,93,33,27,139],[0]),([60,0,1,20,2,3,4,5],[46,154,104,155,44,172,13,5,146,52,45,174,40],[]),([19,30,14,0,1,3,5],[13,97,5,33,93],[0]),([29,12,8,17,2,3,4,5],[7,3,9,40,147,46,6,148,149,23,57,28],[0]),([10,9,2,46,3,4,5],[5,23,14,46,9,18,7],[0]),([19,43,2,3,4,5],[23,44,46,7,14,3,9],[0,3,7]),([44,0,13,2,3,4,5],[41,23,46,142,156,52,143,14,153,135],[]),([29,49,28,0,1,2,3],[88,13,52,156,5],[0]),([69,0,1,2,3,4,5],[157,13,150,41,152,34,44,99,35,52,192,135],[]),([10,26,23,2,3,4,5],[9,106,3,7,6,23,57],[1,0,7,3]),([24,10,0,1,2,3,40,4,5],[30,44,97,13],[0]),([10,9,23,2,3,4,5],[23,41,13,44,14,9,7,18],[0,3]),([10,0,1,2,3,4,31,5],[23,178,155,30,13,142,5,33,35,18,7,14],[]),([24,10,0,1,2,3,40,33],[30,133,23,7,13,5,18,89,52,17],[0]),([70,0,1,2,3,4,5],[41,82,158,153,34,35,99,143,57,193],[]),([0,1,26,20,2,4,5,33],[5,45,7,175,186,23,104,46,30,6,105,188,57,14,187,28],[0,2]),([71,0,1,2,3,4,5],[157,44,155,13,99,35,9,192,135],[]),([29,24,10,9,2,3,4,5],[7,44,97,86,112,14,104,40,183,57,23,13],[0]),([12,0,1,72,2,3,4,5],[13,7,52,23,100,194,142,80,195,57,45,46,28],[0,2]),([24,10,9,2,3,40,4,5],[137,118,13,119,44,18,97,32,57,72,14,86],[0]),([43,24,2,3,4,5],[44,104,23,7,14,3],[0,5]),([10,9,2,3,4,31,5],[23,13,196,14,9,5,44,18,6],[0,3]),([19,30,18,0,1,3,5],[5,27,93,33],[0]),([10,45,9,2,3,4,5],[41,44,97,46,27,7,18,57],[0]),([73,0,1,2,3,4,5],[157,13,41,99,155,5,88],[0]),([43,2,27,3,4,5],[3,44,104,23,7],[0,5]),([29,49,24,0,1,2,3],[88,82,7,23,156,91,13,95,52],[0]),([19,30,8,17,3,5],[23,3,9],[1,0,3]),([43,2,74,3,4,5],[44,3,50,46,23,7,27],[0,5]),([0,1,26,2,46,4,5],[178,23,155,14,9,18],[0]),([75,10,0,1,2,3,4,5],[41,33,44,93,157,14,77,7,23,197,198,192,136],[0]),([10,0,1,2,27,3,40,33],[13,52,133,88,135,5,17,18,89],[0]),([28,0,1,2,3,40,33],[13,52,88,156,5,33],[0]),([29,10,9,20,2,3,4,5],[104,40,46,28,27,14,183],[0]),([24,0,1,2,3,40,4,5],[23,7,13,88,156,91,33,3,52,153],[]),([10,26,2,3,4,25,5],[5,3,107,6,7],[0,3]),([12,43,2,3,4,5],[3,44,46,23,7],[0,5,7,3]),([76,0,1,2,3,4,5],[157,88,158,150,41,34,97,180,145],[]),([43,10,2,74,3,4,5],[3,44,50,41,27,23,7],[0,5]),([29,49,24,10,0,1,2,3],[86,13,30,176,5],[0]),([12,0,1,2,3,4,59,5],[13,44,52,5,170,173,57,142,199,156,45],[]),([10,42,2,3,4,5],[23,44,3,13,5],[3,0]),([39,10,9,2,3,4,5],[41,57,44,23,46,3,7,18,27],[0]),([10,9,2,27,3,40,4,5],[200,201,137,119,18,32,57,23,7,86,13],[0]),([24,10,9,2,3,4,5,33],[132,127,13,5,18,7,44,97,14,86],[0]),([10,0,1,77,27,3,4,5],[86,14,165,9,40,30,192,157,57],[0]),([12,10,9,23,3,4,5],[3,9,106,6,28],[0]),([43,23,2,3,4,5],[44,14,3,9,57,23,46,7],[0,3,1,6,7]),([14,0,1,23,3,25,5],[13,52,30,152,5,33,93,139],[0]),([10,9,2,47,3,4,5],[44,28,41,23,3,7,18],[0]),([8,17,2,38,3,4,5],[153,3,14,57,46,9,7,18],[0]),([29,10,9,2,27,3,4,5],[41,44,86,202,3,14,183,104,40,57,23,13],[0,5]),([0,1,72,20,2,3,4,5],[5,45,104,7,46,23,155,76,172,195,194,57,28],[0,2]),([78,43,2,3,4,5],[46,44,3,23,7],[0,7,3,5,8,9]),([39,0,1,26,2,4,5],[57,158,46,18,151,14,9,28,27],[0]),([10,0,1,2,27,3,40,4,5],[13,88,44,18,89,57],[0]),([10,9,2,27,3,4,5,33],[13,203,132,5,18,7,86],[0]),([79,43,2,3,4,5],[3,44,46,23,7,27],[0,5]),([30,8,17,20,3,4,5],[3,153,5,14,6,27,28],[0]),([80,0,1,2,3,4,5],[157,13,158,88,99,41,34,161,86,160,145],[]),([0,1,81,2,3,4,5],[23,157,178,152,14,100,192,99,35,9],[]),([43,20,2,3,4,5],[44,14,27,46,3,23,7],[0,7,3,1,10,5]),([0,1,82,2,3,4,5],[23,41,13,158,192,143,99,35,135],[]),([28,0,1,2,3,40,4,5],[13,52,88,156,5,33,152],[]),([43,10,23,2,3,4,5],[23,44,14,50,117,3,106,57,7],[0,3,6])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_51_8 : checkNodesBT W_51 G_51 fmask_51 P_51 autos_51 bk_51_7 8 nodes_51_8 = true := by decide +kernel
def bk_51_8 : BT (List (List Nat)) := buildBucketsBT W_51 nodes_51_8
set_option maxRecDepth 500000 in
lemma bk_51_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_51 8 xs.toFinset) bk_51_8 :=
  buildBucketsBT_sound (by decide) gp_51 W_51_ok P_51_ok autos_51_ok bk_51_7_ok chk_51_8
def nodes_51_9 : List NodeSpec := [([29,8,0,1,20,2,3,4,5],[46,146,145,147,175,7,14,193,148,6,28,135,88,40,204,23,5],[0,2]),([8,17,20,2,3,4,5],[46,104,3,14,23,27,7],[0,1,10,5,2]),([19,0,1,15,2,3,4,5],[157,23,186,46,143,81,141,6,13,142,9,161,33],[0]),([19,10,0,1,2,3,4,5],[205,41,23,44,157,46,5,7,100,155,33,161,3,14],[0]),([19,30,0,1,9,3,5],[23,3,142,33,9],[1,0,3]),([29,0,1,16,2,3,4,5],[157,141,3,153,155,142,206,7,160,23,57],[4,0]),([0,1,9,2,3,4,31,5],[178,23,155,30,6,205,35,33,7,14],[0,7]),([0,1,9,23,2,3,4,5],[3,23,152,30,155,9,33,7,18],[0,3]),([0,1,32,2,3,4,5],[23,205,158,3,178,152,34,35,99,14,9],[0,7,3]),([29,12,0,1,9,2,3,4,5],[7,3,9,28,46,104,146,207,86,23,30,206,208,40,148,156],[0]),([0,1,26,2,3,4,25,5],[3,23,107,93,33,6,7],[0,1,3]),([0,1,22,2,3,4,5,33],[7,23,88,156,91,155,3],[4]),([30,0,1,22,3,4,5],[3,150,142,23,153,57],[0]),([19,30,10,0,1,3,5],[209,210,23,3,13,142,5,33,52],[1,0,3,11]),([10,0,1,2,3,4,31,5],[23,178,155,13,30,211,212,213,192,33,44,41,7],[3,0]),([34,0,1,2,3,4,5],[150,44,152,100,34,35,99,135,212,23],[0,11,3]),([10,0,1,2,3,4,35,5],[23,3,210,213,209,33,44,41,13,52],[0]),([10,0,1,2,36,3,4,5],[23,3,142,13,97,41,5,154,44,33,145,157,46,27,214,7],[0,11,1,3]),([37,0,1,2,3,4,5],[150,23,158,3,44,41,34,99,35,27,209,210],[0,11,3]),([29,12,10,0,1,2,3,4,5],[7,3,139,40,104,146,175,213,206,30,13,168,57,148,215,28,5],[0]),([10,9,2,3,4,25,5],[23,3,13,5,41,44,158,46,7],[0,3]),([10,0,1,2,38,3,4,5],[153,3,142,97,30,44,163,216,217,165,185,157,180,23,9,7,214],[0]),([10,0,1,20,2,3,4,5,33],[5,45,218,88,156,104,175,186,46,189,40,212,27],[0,2]),([30,10,0,1,20,3,4,5],[100,104,3,82,97,175,5,27,212,213,153,215,165,219,28],[0]),([39,10,0,1,2,3,4,5],[41,152,57,44,82,27,157,163,7,214,154,94,219,151,5],[0]),([19,14,0,1,2,3,4,5],[205,41,13,46,139,86,213,52,100,33,161],[0]),([29,10,0,1,20,2,3,4,5],[104,146,145,40,186,175,27,212,213,148,135,88,168,57,23,28,5],[0]),([19,8,0,13,2,3,4,5],[150,23,186,175,46,41,81,141,6,52,145,3,5],[0,12]),([6,10,1,23,2,3,4,5],[81,3,220,221,157,44,139,215,151,178,222,5,106,7,213],[1]),([12,10,0,1,2,3,40,4,5],[30,13,223,119,7,198,139,213,57,6,215,224,5,186,28,40],[0,2]),([19,10,7,1,2,3,4,5],[157,178,13,46,104,139,160,213,145,23,27,45],[0]),([19,6,10,1,2,3,4,5],[158,3,175,178,44,104,139,7,213,5,145,27,45],[0]),([10,7,1,2,3,4,25,5],[13,142,3,157,145,23,186,180,5,104,46,27,213,160],[0,1]),([10,7,1,23,2,3,4,5],[13,142,221,23,9,44,225,215,222,226,104,81,27,139,160,213,28],[1]),([0,1,9,2,38,3,4,5],[3,153,142,100,30,9,152,217,165,7,18,57],[0]),([19,0,1,26,2,3,4,5],[175,23,158,46,9,7,6,152,161,33],[0,7,3]),([29,0,1,22,2,3,4,5],[7,150,141,3,155,142,206,205,152,57,23],[0]),([19,10,9,2,3,4,5],[41,23,44,46,7,13,3,14,9,5],[0,3,7]),([12,8,17,2,3,4,5],[150,46,158,104,3,23,7],[0,5,1,10,2]),([12,10,9,2,3,4,5],[41,104,46,3,23,7],[0,5]),([10,0,1,23,2,41,3,4,5],[14,227,190,44,30,9,139,57,117,97,134,228],[0,1]),([12,10,0,1,2,3,4,5,33],[30,13,91,5,52,23,189,7,40,139,104,175,186,46],[0,2]),([39,0,1,9,2,3,4,5],[157,57,158,152,23,46,3,7,18,151,155,172,28,219,94,14,27],[0]),([6,10,1,2,3,4,25,5],[3,5,158,175,44,145,104,27,213,7],[1]),([29,12,8,0,1,2,3,4,5],[7,3,81,148,146,104,6,206,30,86,204,23,57,28,40,5],[0,2]),([10,26,2,3,4,5],[46,104],[0,7,5,3,8,9]),([10,9,23,2,3,4,5],[220,41,14,44,190,3,9,106,23,57,7],[0,3,1,6,7]),([30,0,1,9,20,3,4,5],[175,3,104,100,159,14,6,153,155,172,28,219,165,27],[0]),([18,0,1,23,2,3,4,5],[23,5,142,221,3,9,44,104,30,139,190,152,229,106,33,225,27,40,213,28],[0]),([19,8,17,2,3,4,5],[150,23,178,46,7,14,3,9],[1,6,0,7,3]),([0,1,42,2,3,4,5],[3,23,34,35,99,230],[0,1,3]),([43,2,3,4,5],[46],[0,7,3,5,8,9]),([44,0,1,2,3,4,5],[41,23,158,150,152,34,99,35,13,153,178,14,135],[0,1,3]),([0,1,26,20,2,4,5],[186,46,100,14,187],[0,1,10,5,2]),([19,18,0,1,2,3,4,5],[205,44,13,104,192,5,139,40,213,3,161,33,52,45],[0]),([28,0,1,2,3,4,5,33],[13,52,88,156,5,41,99,157,231,232,155,210],[0]),([18,0,1,2,3,4,25,5],[23,13,142,5,3,44,104,93,33,157,52,97,27,213,40],[0]),([14,0,1,23,2,3,4,5],[81,9,41,30,190,152,221,33,229,157,186,13,97,139,86,213,28],[0]),([24,10,0,1,2,3,40,4,5],[30,198,23,7,13,52,119,44,18,97,89,57,233,72,14,86],[0]),([43,10,2,3,4,5],[158,44,104],[0,7,3,5,8,9]),([29,24,0,1,2,3,4,5],[99,155,88,3,157,153,41,210,142,206,7,141,205,152,86,112,160,82,234],[0]),([29,24,10,0,1,2,3,4,5],[7,44,97,86,157,212,104,40,30,168,23,141,57,160,82,235,13],[0]),([24,10,9,2,3,4,5],[3,44,41,46,104,23,7,14],[0,5]),([29,10,0,1,2,27,3,4,5],[41,165,44,86,157,3,168,104,40,160,88,30,192,57,23,13],[0,5]),([39,8,0,1,2,3,4,5],[150,152,14,82,143,57,157,23,153,7,236,27,193,94,219],[0]),([10,45,0,1,2,3,4,5],[41,152,44,97,46,27,7,214,57,13],[0]),([12,0,1,9,2,3,4,5,33],[13,7,52,23,30,184,91,5,237,238,57,18,9,207,45,104,46,215,28,6],[0,2]),([24,0,1,2,3,4,5,33],[23,13,7,88,156,91,155,127,157,44,52,41],[0]),([8,0,1,2,38,3,4,5],[153,185,30,152,81,165,217,3,157,180,7,236,57],[0]),([10,9,20,2,3,4,5],[104,46,3,14,23,27,7],[0,1,10,5]),([24,0,1,2,3,40,4,5],[23,88,7,118,239,240,233,241,200,242,156,223,33,152,82],[0]),([24,10,0,1,2,3,4,5,33],[30,189,23,7,13,5,86,44,97,157,14],[0]),([0,1,9,20,2,3,4,5,33],[5,45,7,175,186,23,104,46,88,177,218,238,215,156,243,237,57,14,187,28,6],[0,2]),([10,9,2,27,3,4,5],[41,3,104,23,7],[0,5]),([10,0,1,20,2,3,40,4,5],[6,224,200,88,135,119,242,213,154,13,5,186,198,27,212,57,28,40],[0,2]),([10,0,1,23,2,3,4,5],[23,3,41,152,13,30,44,163,155,97,139,33,7],[3,0,6,1]),([10,0,1,2,27,3,4,5,33],[13,52,189,88,135,5,165,93,41,44,157,86],[0]),([14,0,1,2,3,4,25,5],[13,52,100,155,5,205,152,41,33,93,157,186,46,97,213,86],[0]),([10,0,1,2,27,3,40,4,5],[244,201,200,198,242,135,119,44,72,163,89,209,214,245,86,13],[0]),([10,0,1,2,46,3,4,5],[23,178,155,13,172,5,41,142,44,33,145,52,163,46,212,27,214,7],[0]),([10,0,1,2,47,3,4,5],[153,3,210,41,152,44,30,246,247,163,46,248,7,214],[0]),([29,0,1,9,20,2,3,4,5],[175,186,104,46,146,28,187,14,243,40,148,23,88,135,156,208],[0]),([29,28,0,1,2,3,4,5],[99,41,13,88,3,153,142,206,160,86,205,152,35],[0]),([0,1,2,41,3,4,5],[44,205,100,30,34,35,99,167],[0,3]),([0,1,9,2,46,3,4,5],[178,23,155,172,192,142,9,215,205,145,33,18,7],[0]),([28,0,1,2,3,40,4,5],[200,240,242,156,223,33,152,88,13],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_51_9 : checkNodesBT W_51 G_51 fmask_51 P_51 autos_51 bk_51_8 9 nodes_51_9 = true := by decide +kernel
def bk_51_9 : BT (List (List Nat)) := buildBucketsBT W_51 nodes_51_9
set_option maxRecDepth 500000 in
lemma bk_51_9_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_51 9 xs.toFinset) bk_51_9 :=
  buildBucketsBT_sound (by decide) gp_51 W_51_ok P_51_ok autos_51_ok bk_51_8_ok chk_51_9
def nodes_51_10 : List NodeSpec := [([11,0,1,2,3,4,5],[34,41,158,100,155,205,152,99,35,157,186],[1,13,10,14,4,15]),([12,8,0,1,2,3,4,5],[150,100,46,142,157,175,153,23,141,154,215,146,156],[0,5,1,10,2]),([8,0,13,2,3,4,5],[150,41,46,142,215,156,158,175],[12,0,7,16,5,3,17,8,9]),([14,0,1,2,3,4,5],[41,157,100,155,104,205,152,99,35],[0,7,5,3,8,9]),([0,1,15,2,3,4,5],[150,41,157,34,46,186,155,100,152,205,35,99],[1,0,7,10,5,3,4,8,9]),([0,1,16,2,3,4,5],[150,41,157,158,155,142,249,205,152,99,35],[4,0,5]),([8,17,2,3,4,5],[150,158,46],[0,1,7,10,5,3,4,8,9]),([18,0,1,2,3,4,5],[150,157,34,46,104,155,100,152,205,35,99,186],[0,7,5,3,8,9]),([10,0,1,2,3,4,5],[150,158,41,100,155,34,104,205,152,99,35],[0,1,7,5,10,3,8,4,9]),([19,8,0,1,2,3,4,5],[150,205,23,158,157,46,141,100,155,142,33,178,13,14,153,5],[0,1,6,3]),([8,0,1,20,2,3,4,5],[46,104,172,155,154,215,146,156,186,157,175,153,14,23,193,141],[0,1,10,5,13,14,2]),([19,0,1,9,2,3,4,5],[157,23,158,205,46,7,178,155,100,142,33,14,3,9],[0,7,3]),([12,0,1,9,2,3,4,5],[157,186,41,46,100,142,3,23,7,215,154,156,146],[0,5,1,10,2]),([21,0,1,2,3,4,5],[158,41,100,155,34,104,205,152,99,35],[1,13,10,14,4,15]),([19,10,0,1,2,3,4,5],[205,41,23,209,44,157,46,245,178,155,13,100,210,212,142,5,33,52],[0,3,11,7]),([0,1,22,2,3,4,5],[158,150,155,34,142,205,152,99,35],[0,5,4]),([10,0,1,23,2,3,4,5],[226,220,41,152,190,44,30,163,155,210,212,142,221,106,209,250,157,225,139,245],[0,3,11,1,6,13]),([24,10,0,1,2,3,4,5],[100,44,41,46,104,209,245,212,97],[0,5]),([10,7,1,2,3,4,5],[157,34,158,142,215,156,150,104],[0,7,5,3,8,9]),([0,1,9,2,3,4,25,5],[3,23,142,158,205,33,46,251,7],[0,3,1,6]),([0,1,9,20,2,3,4,5],[186,46,155,172,215,154,156,146,3,14,23,187,7],[0,1,10,5,2]),([12,10,0,1,2,3,4,5],[100,41,104,142,157,175,210,209,245,154,215,146,156],[0,5,1,10]),([24,0,1,2,3,4,5],[150,157,158,155,34,142,205,152,99,35,44,41],[0,5]),([6,10,1,2,3,4,5],[158,46,157,142,104,215,156],[0,7,5,3,8,9]),([10,9,2,3,4,5],[158,41,46,104],[0,7,3,5,8,9]),([0,1,26,2,3,4,5],[158,150,155,46,100,152,205,35,99],[0,1,7,10,5,3,4,8,9]),([10,0,1,2,3,4,25,5],[23,3,155,13,97,142,5,152,41,209,44,33,157,158,150,27,210,46,245],[0,3,11,1]),([10,0,1,2,27,3,4,5],[41,157,44,155,104,210,209,245],[0,5]),([10,0,1,20,2,3,4,5],[46,104,172,155,154,215,146,156,186,157,175,210,212,209,27,245],[0,1,10,5]),([28,0,1,2,3,4,5],[41,157,155,34,142,205,152,99,35],[0,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_51_10 : checkNodesBT W_51 G_51 fmask_51 P_51 autos_51 bk_51_9 10 nodes_51_10 = true := by decide +kernel
def bk_51_10 : BT (List (List Nat)) := buildBucketsBT W_51 nodes_51_10
set_option maxRecDepth 500000 in
lemma bk_51_10_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_51 10 xs.toFinset) bk_51_10 :=
  buildBucketsBT_sound (by decide) gp_51 W_51_ok P_51_ok autos_51_ok bk_51_9_ok chk_51_10
def nodes_51_11 : List NodeSpec := [([6,0,1,2,3,4,5],[34,158,150,100,205,99],[0,18,19,20,21,22,23,24,25,26,1,13,10,14,4,15]),([7,0,1,2,3,4,5],[34,157,150,186,100,158,205,99],[0,18,19,20,11,27,28,29,21,22,23,24,25,26,1,13,10,14,4,15]),([8,0,1,2,3,4,5],[150,100,34,205,99,158,157,46],[0,7,3,1,10,4,9]),([0,1,9,2,3,4,5],[158,150,100,34,205,99,46],[0,7,3,1,10,5,4,8,9]),([10,0,1,2,3,4,5],[150,158,41,100,34,104,205,99,157],[0,7,3,11,5,8,9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_51_11 : checkNodesBT W_51 G_51 fmask_51 P_51 autos_51 bk_51_10 11 nodes_51_11 = true := by decide +kernel
def bk_51_11 : BT (List (List Nat)) := buildBucketsBT W_51 nodes_51_11
set_option maxRecDepth 500000 in
lemma bk_51_11_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_51 11 xs.toFinset) bk_51_11 :=
  buildBucketsBT_sound (by decide) gp_51 W_51_ok P_51_ok autos_51_ok bk_51_10_ok chk_51_11
def nodes_51_12 : List NodeSpec := [([0,1,2,3,4,5],[34],[0,11,18,27,19,28,20,29,21,22,23,24,25,26,1,13,10,14,4,15])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_51_12 : checkNodesBT W_51 G_51 fmask_51 P_51 autos_51 bk_51_11 12 nodes_51_12 = true := by decide +kernel
def bk_51_12 : BT (List (List Nat)) := buildBucketsBT W_51 nodes_51_12
set_option maxRecDepth 500000 in
lemma bk_51_12_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_51 12 xs.toFinset) bk_51_12 :=
  buildBucketsBT_sound (by decide) gp_51 W_51_ok P_51_ok autos_51_ok bk_51_11_ok chk_51_12
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_51_ok : forestRootCheck R_51 G_51 [(VAR 0,15,14),(VAR 1,15,13),(VAR 2,15,11),(VAR 3,15,7),(VAR 4,27,11),(VAR 5,43,11)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_51_in : bucketContainsBT bk_51_12 R_51 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_51 : Lower R_51 G_51 13 := lower_of_forestBT root_51_ok bk_51_12_ok root_51_in
def wit : List PEqualNP.CircuitLowerBounds.Gate := [
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 6]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 7]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 4]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 10]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 7]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 9]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 13]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 14]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 16]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 18]⟩
]
def wo : Nat := 19
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by intro g hg; simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4269860864 * 2 ^ 32 + 3892346880) ||| ((4269860864 * 2 ^ 32 + 3892346880) <<< 64)).testBit r.val := by decide +kernel
lemma root_eq : G_51 = ((4269860864 * 2 ^ 32 + 3892346880) ||| ((4269860864 * 2 ^ 32 + 3892346880) <<< 64)) := by decide
lemma low_root : Lower (varsOf 63) ((4269860864 * 2 ^ 32 + 3892346880) ||| ((4269860864 * 2 ^ 32 + 3892346880) <<< 64)) 13 := root_eq ▸ low_51
end PEqualNP.Outside.L_meta_12058
theorem PEqualNP.Outside.L_meta_12058 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269860864 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269860864 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_12058.table2_of_lower (4269860864 * 2 ^ 32 + 3892346880) (by decide) (by decide) (by decide) (by decide) 13 PEqualNP.Outside.L_meta_12058.low_root PEqualNP.Outside.L_meta_12058.wit PEqualNP.Outside.L_meta_12058.wo (by decide) PEqualNP.Outside.L_meta_12058.wit_mono PEqualNP.Outside.L_meta_12058.wit_eval s hcs
