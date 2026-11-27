import Mathlib.Tactic.Tauto
import Mathlib.Tactic.NormNum
import PEqualNP.Defs
-- The certificate checker is adapted from L_meta_9358.
namespace PEqualNP.Outside.L_meta_10117
namespace WordEngine
def unpack (packed width index : Nat) : Nat :=
  (packed >>> (width * index)) &&& ((1 <<< width) - 1)
def treeBlock (start count : Nat) (check : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ next i => check i && next (i + 1)) count) start
theorem treeBlock_at {start count i : Nat} {check : Nat → Bool}
    (h : treeBlock start count check = true) (lo : start ≤ i) (hi : i < start + count) :
    check i = true := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    change (check start && treeBlock (start + 1) count check) = true at h
    rcases Bool.and_eq_true_iff.mp h with ⟨here, rest⟩
    by_cases eq : i = start
    · simpa [eq] using here
    · exact ih rest (by omega) (by omega)
theorem treeBlock_merge {start left right : Nat} {check : Nat → Bool}
    (a : treeBlock start left check = true)
    (b : treeBlock (start + left) right check = true) :
    treeBlock start (left + right) check = true := by
  induction left generalizing start with
  | zero => simpa using b
  | succ left ih =>
    rw [Nat.succ_add]
    change (check start && treeBlock (start + 1) (left + right) check) = true
    change (check start && treeBlock (start + 1) left check) = true at a
    rcases Bool.and_eq_true_iff.mp a with ⟨here, rest⟩
    exact Bool.and_eq_true_iff.mpr ⟨here, ih rest (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using b)⟩
abbrev Word := Nat
abbrev RowState := Nat × List Word × List (Word × Word × Word)
def insertWord (w : Word) (ws : List Word) : List Word :=
  List.rec [w] (fun a tail next => if w ≤ a then w :: a :: tail else a :: next) ws
def childState (mask token : Nat) (state : RowState) : Option RowState :=
  let (fuel, ws, history) := state
  let keep := token % 4
  let op := (token / 4) % 3
  let a := token / (4 * 3 * 64)
  let b := (token / (4 * 3)) % 64
  if fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b) then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let w := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
    if w == 0 || w == mask || ws.contains w then none
    else
      let rest := if keep.testBit 0 then ws else ws.erase x
      let rest := if op == 2 || keep.testBit 1 then rest else rest.erase y
      some (fuel - 1, insertWord w rest, (w, x, y) :: history)
def gateToken (a b op keep : Nat) : Nat := ((a * 64 + b) * 3 + op) * 4 + keep
def maskFlat (mask word : Nat) : Bool :=
  let v := word &&& mask
  v == 0 || v == mask
def flatCount (mask : Nat) (words : List Word) : Nat :=
  List.rec 0 (fun word _ count => if maskFlat mask word then count + 1 else count) words
def availableB (mask : Nat) (bank : List Word) (w : Word) : Bool :=
  w == 0 || w == mask || bank.contains w
def AvailableWord (mask : Nat) (bank : List Word) (word : Word) : Prop :=
  word = 0 ∨ word = mask ∨ word ∈ bank
def GateWord (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  (∃ a, AvailableWord mask bank a ∧ out = mask ^^^ a) ∨
  (∃ a b, AvailableWord mask bank a ∧ AvailableWord mask bank b ∧
    (out = a &&& b ∨ out = a ||| b))
theorem restrictWord (mask : Nat) (word : Word) : word &&& mask &&& mask = word &&& mask := by
  simp
theorem projectGate {mask cut : Nat} (submask : mask &&& cut = cut)
    {roots : List Word} {out : Word} (gate : GateWord mask roots out) :
    GateWord cut (roots.map (· &&& cut)) (out &&& cut) := by
  have av {word : Word} (ha : AvailableWord mask roots word) :
      AvailableWord cut (roots.map (· &&& cut)) (word &&& cut) := by
    rcases ha with rfl | rfl | hm
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl submask)
    · exact Or.inr (Or.inr (List.mem_map_of_mem hm))
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq | eq⟩
  · refine Or.inl ⟨a &&& cut, av ha, ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    have cutAt := congrArg (fun n : Nat => n.testBit i) submask
    simp only [Nat.testBit_and, Nat.testBit_xor] at cutAt ⊢
    cases h : cut.testBit i
    · simp
    · simp [h] at cutAt
      simp [cutAt]
  · subst out
    refine Or.inr ⟨a &&& cut, b &&& cut, av ha, av hb, Or.inl ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and]
    cases cut.testBit i <;> simp
  · subst out
    refine Or.inr ⟨a &&& cut, b &&& cut, av ha, av hb, Or.inr ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases cut.testBit i <;> simp
theorem availableWeaken {mask : Nat} {small big : List Word} {w : Word}
    (sub : ∀ x ∈ small, AvailableWord mask big x)
    (av : AvailableWord mask small w) : AvailableWord mask big w := by
  rcases av with rfl | rfl | h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact sub w h
def properWord (mask word : Word) : Prop := word ≠ 0 ∧ word ≠ mask
def binWord (isOr : Bool) (a b : Word) : Word :=
  if isOr then a ||| b else a &&& b
theorem binWord_comm (d : Bool) (a b : Word) : binWord d a b = binWord d b a := by
  cases d <;> simp [binWord, Nat.land_comm, Nat.lor_comm]
variable {mask : Nat} {target : Word}
def LiveWord (mask : Nat) (target : Word) : Nat → Nat → Finset (Word) → Prop
  | 0,t,S => t=0 ∧ S={target} ∧ properWord mask target
  | k+1,t,S =>
    (∃ (u : Nat) (U : Finset (Word)) (a : Word), t=u+1 ∧ S=insert a U ∧ properWord mask a ∧
      (mask ^^^ a) ∉ insert a U ∧ LiveWord mask target k u (insert ((mask ^^^ a)) U)) ∨
    (∃ (U : Finset (Word)) (a b : Word) (d : Bool), S=insert a (insert b U) ∧ properWord mask a ∧ properWord mask b ∧ a ≠ b ∧
      binWord d a b ∉ insert a (insert b U) ∧ LiveWord mask target k t (insert (binWord d a b) U))
theorem LiveWord.stop {target : Word} (hp : properWord mask target) : LiveWord mask target 0 0 {target} := ⟨rfl,rfl,hp⟩
theorem LiveWord.unary {target : Word} {k t : Nat} {U : Finset (Word)} {a : Word} (ha : properWord mask a)
    (hfresh : (mask ^^^ a) ∉ insert a U) (tail : LiveWord mask target k t (insert ((mask ^^^ a)) U)) :
    LiveWord mask target (k+1) (t+1) (insert a U) :=
  Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
theorem LiveWord.binary {target : Word} {k t : Nat} {U : Finset (Word)} {a b : Word} {d : Bool}
    (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
    (hfresh : binWord d a b ∉ insert a (insert b U)) (tail : LiveWord mask target k t (insert (binWord d a b) U)) :
    LiveWord mask target (k+1) t (insert a (insert b U)) :=
  Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
theorem LiveWord.ind {target : Word} {motive : ∀ (k t : Nat) (S : Finset (Word)), LiveWord mask target k t S → Prop}
    (stop : ∀ (hp : properWord mask target), motive 0 0 {target} (LiveWord.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset (Word)} {a : Word} (ha : properWord mask a)
      (hfresh : (mask ^^^ a) ∉ insert a U) (tail : LiveWord mask target k t (insert ((mask ^^^ a)) U)),
      motive k t (insert ((mask ^^^ a)) U) tail → motive (k+1) (t+1) (insert a U) (LiveWord.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset (Word)} {a b : Word} {d : Bool}
      (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
      (hfresh : binWord d a b ∉ insert a (insert b U)) (tail : LiveWord mask target k t (insert (binWord d a b) U)),
      motive k t (insert (binWord d a b) U) tail →
      motive (k+1) t (insert a (insert b U)) (LiveWord.binary ha hb hab hfresh tail))
    {k t : Nat} {S : Finset (Word)} (h : LiveWord mask target k t S) : motive k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)
theorem liveWordProper {k t S} (h : LiveWord mask target k t S) : ∀ a ∈ S, properWord mask a := by
  induction h using LiveWord.ind with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
theorem liveWordSize {k t S} (h : LiveWord mask target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using LiveWord.ind with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : (mask ^^^ a) ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : binWord d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩
def wordRep (mask : Nat) (ws : List Word) (w : Word) : Prop :=
  w ∈ ws ∨ ¬properWord mask w
def Masked (mask word : Nat) : Prop := word &&& mask = word
theorem maskedAvailable {bank : List Word} {word : Word}
    (all : ∀ w ∈ bank, Masked mask w) (aw : AvailableWord mask bank word) :
    Masked mask word := by
  rcases aw with rfl | rfl | hw
  · simp [Masked]
  · simp [Masked]
  · exact all _ hw
theorem maskedGate {bank : List Word} {out : Word}
    (all : ∀ w ∈ bank, Masked mask w) (g : GateWord mask bank out) :
    Masked mask out := by
  rcases g with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, ea | ea⟩
  · have h := projectGate (mask := mask) (cut := mask) (by simp)
      (roots := bank) (out := mask ^^^ a) (Or.inl ⟨a, ha, rfl⟩)
    have ma := maskedAvailable all ha
    unfold Masked at ma ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have bit := congrArg (fun n : Nat => n.testBit i) ma
    simp only [Nat.testBit_and, Nat.testBit_xor] at bit ⊢
    cases hm : mask.testBit i <;> simp_all
  · subst out
    have ma := maskedAvailable all ha
    have mb := maskedAvailable all hb
    simp only [Masked] at ma mb ⊢
    rw [Nat.land_assoc, mb]
  · subst out
    have ma := maskedAvailable all ha
    have mb := maskedAvailable all hb
    unfold Masked at ma mb ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have bitA := congrArg (fun n : Nat => n.testBit i) ma
    have bitB := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and, Nat.testBit_or] at bitA bitB ⊢
    cases hm : mask.testBit i <;> simp_all
def binaryWitness (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  ∃ d a b, a ∈ bank ∧ b ∈ bank ∧ properWord mask a ∧ properWord mask b ∧
    a ≠ b ∧ out = binWord d a b
theorem classifyBinary {bank : List Word}
    (all : ∀ w ∈ bank, Masked mask w) (d : Bool) {a b : Word}
    (ha : AvailableWord mask bank a) (hb : AvailableWord mask bank b) :
    wordRep mask bank (binWord d a b) ∨ binaryWitness mask bank (binWord d a b) := by
  have c0 : wordRep mask bank 0 := Or.inr fun h => h.1 rfl
  have cm : wordRep mask bank mask := Or.inr fun h => h.2 rfl
  have classify {w : Word} (hw : AvailableWord mask bank w) :
      w = 0 ∨ w = mask ∨ w ∈ bank ∧ properWord mask w := by
    by_cases zh : w = 0
    · exact Or.inl zh
    by_cases mh : w = mask
    · exact Or.inr (Or.inl mh)
    exact Or.inr (Or.inr ⟨(hw.resolve_left zh).resolve_left mh, zh, mh⟩)
  have ma : a &&& mask = a := maskedAvailable all ha
  have mb : b &&& mask = b := maskedAvailable all hb
  have absorbA : a ||| mask = mask := by
    apply Nat.eq_of_testBit_eq
    intro i
    have h := congrArg (fun n : Nat => n.testBit i) ma
    simp only [Nat.testBit_and, Nat.testBit_or] at h ⊢
    cases hm : mask.testBit i <;> simp_all
  have absorbB : b ||| mask = mask := by
    apply Nat.eq_of_testBit_eq
    intro i
    have h := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and, Nat.testBit_or] at h ⊢
    cases hm : mask.testBit i <;> simp_all
  rcases classify ha with rfl | hma | ⟨ha', pa⟩
  · rw [binWord_comm]
    cases d
    · exact Or.inl (by simpa [binWord] using c0)
    · rcases hb with hz | hm | hv
      · exact Or.inl (by simpa [binWord, hz] using c0)
      · exact Or.inl (by simpa [binWord, hm] using cm)
      · exact Or.inl (by simpa [binWord, wordRep] using
          (Or.inl hv : wordRep mask bank b))
  · rw [hma, binWord_comm]
    cases d
    · rcases hb with hz | hm | hv
      · exact Or.inl (by simpa [binWord, hz] using c0)
      · exact Or.inl (by simpa [binWord, hm] using cm)
      · exact Or.inl (by simpa [binWord, mb, wordRep] using
          (Or.inl hv : wordRep mask bank b))
    · exact Or.inl (by simpa [binWord, absorbB] using cm)
  rcases classify hb with rfl | hmb | ⟨hb', pb⟩
  · cases d
    · exact Or.inl (by simpa [binWord] using c0)
    · exact Or.inl (by simpa [binWord, wordRep] using
        (Or.inl ha' : wordRep mask bank a))
  · rw [hmb]
    cases d
    · exact Or.inl (by simpa [binWord, ma, wordRep] using
        (Or.inl ha' : wordRep mask bank a))
    · exact Or.inl (by simpa [binWord, absorbA] using cm)
  by_cases eq : a = b
  · subst b
    cases d <;> exact Or.inl (by simpa [binWord, wordRep] using
      (Or.inl ha' : wordRep mask bank a))
  exact Or.inr ⟨d, a, b, ha', hb', pa, pb, eq, rfl⟩
theorem insertWordMem {x w : Word} {ws : List Word} :
    x ∈ insertWord w ws ↔ x = w ∨ x ∈ ws := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change x ∈ (if w ≤ a then w :: a :: tail else a :: insertWord w tail) ↔ _
    split <;> simp [ih, or_assoc, or_left_comm]
theorem insertWordNodup {w : Word} {ws : List Word} (nd : ws.Nodup) (fresh : w ∉ ws) :
    (insertWord w ws).Nodup := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change (if w ≤ a then w :: a :: tail else a :: insertWord w tail).Nodup
    split
    · exact List.nodup_cons.mpr ⟨fresh, nd⟩
    have hn := List.nodup_cons.mp nd
    have hnot : w ≠ a ∧ w ∉ tail := by simpa using fresh
    exact List.nodup_cons.mpr ⟨by simp [insertWordMem, hnot.1.symm, hn.1], ih hn.2 hnot.2⟩
theorem insertWordSet (w : Word) (ws : List Word) :
    (insertWord w ws).toFinset = insert w ws.toFinset := by
  ext x
  simp [insertWordMem]
theorem eraseWordSet {ws : List Word} (nd : ws.Nodup) (w : Word) :
    (ws.erase w).toFinset = ws.toFinset.erase w := by
  ext x
  simp [nd.mem_erase_iff, and_comm]
theorem gateTokenFields {a b op keep : Nat} (hb : b < 64) (ho : op < 3) (hk : keep < 4) :
    gateToken a b op keep % 4 = keep ∧
    gateToken a b op keep / 4 % 3 = op ∧
    gateToken a b op keep / (4 * 3 * 64) = a ∧
    gateToken a b op keep / (4 * 3) % 64 = b := by
  unfold gateToken
  omega
def keepWord (save : Bool) (w : Word) (ws : List Word) : List Word :=
  if save then ws else ws.erase w
theorem keepNodup {ws : List Word} (nd : ws.Nodup) (save : Bool) (w : Word) :
    (keepWord save w ws).Nodup := by
  cases save
  · exact nd.erase _
  · exact nd
theorem keepSubset (save : Bool) (w : Word) (ws : List Word) :
    ∀ v ∈ keepWord save w ws, v ∈ ws := by
  cases save
  · exact fun _ h => List.mem_of_mem_erase h
  · exact fun _ h => h
theorem keepSet {ws : List Word} (nd : ws.Nodup) {w : Word} {U : Finset Word}
    (eq : ws.toFinset = insert w U) :
    (keepWord (decide (w ∈ U)) w ws).toFinset = U := by
  by_cases hw : w ∈ U
  · simp [keepWord, hw, eq, Finset.insert_eq_of_mem hw]
  · simp [keepWord, hw, eraseWordSet nd, eq]
theorem keepPairSet {ws : List Word} (nd : ws.Nodup) {a b : Word} {U : Finset Word}
    (ab : a ≠ b) (eq : ws.toFinset = insert a (insert b U)) :
    (keepWord (decide (b ∈ U)) b (keepWord (decide (a ∈ U)) a ws)).toFinset = U := by
  have x : decide (a ∈ insert b U) = decide (a ∈ U) := by simp [ab]
  have h := keepSet nd eq
  rw [x] at h
  exact keepSet (keepNodup nd _ _) h
theorem getWord {ws : List Word} {x : Word} (h : x ∈ ws) :
    ws.getD (ws.idxOf x) 0 = x := by
  have inb := List.idxOf_lt_length_iff.mpr h
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inb] using
    List.getElem_idxOf inb
theorem binaryChild {mask fuel a b : Nat} {ws : List Word}
    {history : List (Word × Word × Word)} {x y : Word} {keep : Nat}
    (d : Bool) (hab : a < b) (hb : b < ws.length) (hb64 : b < 64)
    (hf : fuel ≠ 0) (hk : keep < 4)
    (hx : ws.getD a 0 = x) (hy : ws.getD b 0 = y)
    (p : properWord mask (binWord d x y)) (fresh : binWord d x y ∉ ws) :
    childState mask (gateToken a b (if d then 1 else 0) keep) (fuel, ws, history) =
      some (fuel - 1, insertWord (binWord d x y)
        (keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)),
        (binWord d x y, x, y) :: history) := by
  have oh : (if d then 1 else 0) < 3 := by cases d <;> decide
  obtain ⟨ke, op, aa, bb⟩ := gateTokenFields (a := a) hb64 oh hk
  simp only [childState, ke, op, aa, bb, hx, hy]
  cases d <;>
    simp_all [Nat.not_le_of_lt hab, Nat.not_le_of_lt hb, keepWord, binWord, properWord]
variable {rows : Nat}
def fullMask (rows : Nat) : Nat := 2 ^ rows - 1
theorem toNatAvailable (bank : List (BitVec rows)) (i : Nat) :
    AvailableWord (fullMask rows) (bank.map BitVec.toNat) (bank.getD i 0).toNat := by
  rw [List.getD_eq_getElem?_getD]
  cases h : bank[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (Or.inr (List.mem_map_of_mem (List.mem_of_getElem? h)))
abbrev maskedFlat (m a : Word) : Prop := a &&& m = 0 ∨ a &&& m = m
def flatSet (m : Word) (s : Finset (Word)) := s.filter (maskedFlat m)
def visibleWords (m : Word) (s : Finset (Word)) := s.image fun w => w &&& m
theorem flIns {m a : Word} {s : Finset (Word)} (ha : a ∉ s) :
    (flatSet m (insert a s)).card = (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases f : maskedFlat m a <;> simp [flatSet,Finset.filter_insert,f,ha]
theorem flLe (m a : Word) (s : Finset (Word)) :
    (flatSet m (insert a s)).card ≤ (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases old : a ∈ s
  · rw [Finset.insert_eq_of_mem old]
    omega
  · rw [flIns old]
theorem prIns (m a : Word) (s : Finset (Word)) :
    visibleWords m (insert a s) = insert (a &&& m) (visibleWords m s) := Finset.image_insert ..
theorem cofBinary (m a b : Word) (d : Bool) :
    binWord d a b &&& m = binWord d (a &&& m) (b &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases d <;> simp only [binWord, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and, Nat.testBit_or] <;>
    cases m.testBit i <;> simp
theorem flBoth {m a b : Word} {d : Bool} (ha : maskedFlat m a) (hb : maskedFlat m b) :
    maskedFlat m (binWord d a b) := by
  unfold maskedFlat at *
  rw [cofBinary]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> cases d <;>
    simp [binWord, ha, hb]
theorem simpleBin {m a b : Word} {d : Bool} (h : maskedFlat m a ∨ maskedFlat m b) :
    binWord d a b &&& m = 0 ∨ binWord d a b &&& m = m ∨
      binWord d a b &&& m = a &&& m ∨ binWord d a b &&& m = b &&& m := by
  rw [cofBinary]
  have top1 (x : Word) : m &&& (x &&& m) = x &&& m := by
    rw [Nat.land_comm x m, ← Nat.land_assoc]
    simp
  have top2 (x : Word) : m ||| (x &&& m) = m := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_or, Nat.testBit_and]
    cases x.testBit i <;> cases m.testBit i <;> rfl
  have right1 (x : Word) : (x &&& m) &&& m = x &&& m := restrictWord m x
  have right2 (x : Word) : (x &&& m) ||| m = m := by rw [Nat.lor_comm, top2]
  rcases h with (ha|ha)|(hb|hb) <;> cases d <;>
    simp [binWord, *, top1, top2, right1, right2]
def projectedStock (m : Word) (s : Finset (Word)) := insert 0 (insert m (visibleWords m s))
theorem availableB_spec {mask : Nat} {bank : List Word} {v : Word} :
    availableB mask bank v = true ↔ AvailableWord mask bank v := by
  simp [availableB, AvailableWord, or_assoc]
theorem flatCountCard (mask : Nat) {words : List Word} (nodup : words.Nodup) :
    flatCount mask words = (flatSet mask words.toFinset).card := by
  induction words with
  | nil => rfl
  | cons w ws ih =>
    have nd := List.nodup_cons.mp nodup
    have fresh : w ∉ ws.toFinset := by simpa using nd.1
    have bool : maskFlat mask w = true ↔ maskedFlat mask w := by
      simp [maskFlat, maskedFlat]
    change (if maskFlat mask w then flatCount mask ws + 1 else flatCount mask ws) = _
    rw [List.toFinset_cons, flIns fresh, ih nd.2]
    by_cases h : maskedFlat mask w
    · simp [h, bool.mpr h]
    · have no : maskFlat mask w = false := Bool.eq_false_iff.mpr (fun ht => h (bool.mp ht))
      simp [h, no]
abbrev PointWire (rows : Nat) := Fin rows → Bool
def encodePoint (f : PointWire rows) : BitVec rows :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
theorem encodeBit (f : PointWire rows) (i : Fin rows) :
    (encodePoint f).getLsbD i.val = f i := by
  simp only [encodePoint, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]
theorem encodeAnd (a b : PointWire rows) :
    encodePoint (fun i => a i && b i) = encodePoint a &&& encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
theorem encodeOr (a b : PointWire rows) :
    encodePoint (fun i => a i || b i) = encodePoint a ||| encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
def pointWord (f : PointWire rows) : Word := (encodePoint f).toNat
def relabel (sourceIndex : Fin rows → Fin rows) (word : Word) : Word :=
  pointWord fun i => word.testBit (sourceIndex i).val
theorem pointZero : pointWord (fun _ : Fin rows => false) = 0 := by
  have eq : encodePoint (fun _ : Fin rows => false) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i, hi⟩]
    simp
  simp [pointWord, eq]
theorem relabelZero (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex 0 = 0 := by
  simpa [relabel] using (pointZero (rows := rows))
theorem relabelAnd (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a &&& b) = relabel sourceIndex a &&& relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_and, pointWord, encodeAnd, BitVec.toNat_and]
theorem relabelOr (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a ||| b) = relabel sourceIndex a ||| relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_or, pointWord, encodeOr, BitVec.toNat_or]
theorem relabelXor (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a ^^^ b) = relabel sourceIndex a ^^^ relabel sourceIndex b := by
  have eq : encodePoint (fun i => (a ^^^ b).testBit (sourceIndex i).val) =
      encodePoint (fun i => a.testBit (sourceIndex i).val) ^^^
      encodePoint (fun i => b.testBit (sourceIndex i).val) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_xor, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
    exact Nat.testBit_xor ..
  simpa only [relabel, pointWord, BitVec.toNat_xor] using congrArg BitVec.toNat eq
theorem relabelBit (sourceIndex : Fin rows → Fin rows) (word : Word) (i : Fin rows) :
    (relabel sourceIndex word).testBit i.val = word.testBit (sourceIndex i).val :=
  encodeBit _ i
theorem relabelInj (sourceIndex : Fin rows → Fin rows) (onto : Function.Surjective sourceIndex)
    {a b : Word} (ba : Masked (fullMask rows) a) (bb : Masked (fullMask rows) b)
    (eq : relabel sourceIndex a = relabel sourceIndex b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · obtain ⟨j, h⟩ := onto ⟨i, inside⟩
    have bit := congrArg (fun w : Nat => w.testBit j.val) eq
    simpa only [relabelBit, h] using bit
  · have ea := congrArg (fun w : Nat => w.testBit i) ba
    have eb := congrArg (fun w : Nat => w.testBit i) bb
    simp only [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, inside, decide_false,
      Bool.and_false] at ea eb
    rw [← ea, ← eb]
theorem kw_step (goal : Word) (D D' : Finset Word) (u v w : ℕ) (c : ℕ → ℕ → Bool) (f : ℕ → ℕ → ℕ)
    (hu : u ∈ D) (hv : v ∈ D) (huv : u ≠ v) (huD : u ∉ D') (hvD : v ∉ D')
    (hsub : ∀ x ∈ D', x ≠ w → x ∈ D)
    (hf : ∀ e i, goal.testBit e = true → goal.testBit i = false →
      f e i ∈ D' ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false)
    (hr : ∀ e i e' i', goal.testBit e = true → goal.testBit e' = true → goal.testBit i = false → goal.testBit i' = false → f e i = f e' i' → f e i' = f e i)
    (hcu : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = true →
      u.testBit e = true ∧ u.testBit i = false)
    (hcv : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = false →
      v.testBit e = true ∧ v.testBit i = false)
    (hc : ∀ e i e' i', c e i = c e' i' → c e i' = c e i) :
    ∃ g : ℕ → ℕ → ℕ,
      (∀ e i, goal.testBit e = true → goal.testBit i = false →
        g e i ∈ D ∧ (g e i).testBit e = true ∧ (g e i).testBit i = false) ∧
      (∀ e i e' i', goal.testBit e = true → goal.testBit e' = true → goal.testBit i = false → goal.testBit i' = false → g e i = g e' i' → g e i' = g e i) := by
  have hg : ∀ e i, goal.testBit e = true → goal.testBit i = false → f e i = w →
      ((if f e i = w then (cond (c e i) u v) else f e i) = u ∧ c e i = true) ∨
      ((if f e i = w then (cond (c e i) u v) else f e i) = v ∧ c e i = false) := by
    intro e i _ _ h
    rw [ite_eq_left (h)]
    cases c e i
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  refine ⟨fun e i => if f e i = w then (cond (c e i) u v) else f e i, ?_, ?_⟩
  · intro e i he hi
    obtain ⟨h1, h2, h3⟩ := hf e i he hi
    show (if f e i = w then (cond (c e i) u v) else f e i) ∈ D ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit e = true ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit i = false
    by_cases hw : f e i = w
    · rw [hw] at h2 h3
      rcases hg e i he hi hw with ⟨hx, hcc⟩ | ⟨hx, hcc⟩
      · rw [hx]; exact ⟨hu, hcu e i h2 h3 hcc⟩
      · rw [hx]; exact ⟨hv, hcv e i h2 h3 hcc⟩
    · rw [ite_eq_right (hw)]; exact ⟨hsub _ h1 hw, h2, h3⟩
  · intro e i e' i' he he' hi hi' heq
    show (if f e i' = w then (cond (c e i') u v) else f e i') =
      (if f e i = w then (cond (c e i) u v) else f e i)
    have heq' : (if f e i = w then (cond (c e i) u v) else f e i) =
      (if f e' i' = w then (cond (c e' i') u v) else f e' i') := heq
    by_cases h1 : f e i = w
    · by_cases h2 : f e' i' = w
      · have h3 : f e i' = w := (hr e i e' i' he he' hi hi' (h1.trans h2.symm)).trans h1
        have hcc : c e i = c e' i' := by
          rcases hg e i he hi h1 with ⟨hx, hx'⟩ | ⟨hx, hx'⟩ <;>
            rcases hg e' i' he' hi' h2 with ⟨hy, hy'⟩ | ⟨hy, hy'⟩
          · rw [hx', hy']
          · exact absurd (hx.symm.trans (heq'.trans hy)) huv
          · exact absurd (hy.symm.trans (heq'.symm.trans hx)) huv
          · rw [hx', hy']
        rw [ite_eq_left (h3), ite_eq_left (h1), hc e i e' i' hcc]
      · exfalso
        rw [ite_eq_right (h2)] at heq'
        have hm := (hf e' i' he' hi').1
        rcases hg e i he hi h1 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, heq']; exact hm)
        · exact hvD (by rw [← hx, heq']; exact hm)
    · by_cases h2 : f e' i' = w
      · exfalso
        rw [ite_eq_right (h1)] at heq'
        have hm := (hf e i he hi).1
        rcases hg e' i' he' hi' h2 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, ← heq']; exact hm)
        · exact hvD (by rw [← hx, ← heq']; exact hm)
      · have h1n : (if f e i = w then (cond (c e i) u v) else f e i) = f e i := ite_eq_right h1
        have h2n : (if f e' i' = w then (cond (c e' i') u v) else f e' i') = f e' i' := ite_eq_right h2
        rw [h1n, h2n] at heq'
        have h3 := hr e i e' i' he he' hi hi' heq'
        have h3n : ¬ f e i' = w := by rw [h3]; exact h1
        rw [h1n, ite_eq_right (h3n)]
        exact h3
theorem and_cu (u v e i : ℕ) (h1 : (u &&& v).testBit e = true) (_h2 : (u &&& v).testBit i = false)
    (h3 : (!(u.testBit i)) = true) : u.testBit e = true ∧ u.testBit i = false := by
  rw [Nat.testBit_and] at h1
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem and_cv (u v e i : ℕ) (h1 : (u &&& v).testBit e = true) (h2 : (u &&& v).testBit i = false)
    (h3 : (!(u.testBit i)) = false) : v.testBit e = true ∧ v.testBit i = false := by
  rw [Nat.testBit_and] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem or_cu (u v e i : ℕ) (_h1 : (u ||| v).testBit e = true) (h2 : (u ||| v).testBit i = false)
    (h3 : u.testBit e = true) : u.testBit e = true ∧ u.testBit i = false := by
  rw [Nat.testBit_or] at h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem or_cv (u v e i : ℕ) (h1 : (u ||| v).testBit e = true) (h2 : (u ||| v).testBit i = false)
    (h3 : u.testBit e = false) : v.testBit e = true ∧ v.testBit i = false := by
  rw [Nat.testBit_or] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
def KWPartition (goal : Word) (ws : Finset Word) : Prop :=
  ∃ f : Nat → Nat → Word,
    (∀ e i, goal.testBit e = true → goal.testBit i = false →
      f e i ∈ ws ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false) ∧
    (∀ e i e' i', goal.testBit e = true → goal.testBit e' = true →
      goal.testBit i = false → goal.testBit i' = false → f e i = f e' i' → f e i' = f e i)
theorem kwFromLive {mask goal : Word} {k : Nat} {S : Finset Word}
    (live : LiveWord mask goal k 0 S) (tight : S.card = k + 1) : KWPartition goal S := by
  induction k generalizing S with
  | zero =>
    obtain ⟨_, eq, _⟩ := live
    subst S
    exact ⟨fun _ _ => goal, fun _ _ hp hn => ⟨by simp, hp, hn⟩, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  | succ k ih =>
    rcases live with ⟨u, U, a, eq, _⟩ | ⟨U, a, b, op, rfl, pa, pb, ab, fresh, tail⟩
    · omega
    let w := binWord op a b
    have wU : w ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have wA : w ≠ a := fun eq => fresh (Finset.mem_insert.mpr (Or.inl eq))
    have wB : w ≠ b := fun eq => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl eq)))
    have tailSize := (liveWordSize tail).2
    change (insert w U).card + 0 ≤ k + 1 at tailSize
    rw [Finset.card_insert_of_notMem wU] at tailSize
    have paCard := Finset.card_insert_le a (insert b U)
    have pbCard := Finset.card_insert_le b U
    have aU : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h)] at tight
      omega
    have bU : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      have := Finset.card_insert_le a U
      omega
    obtain ⟨f, hf, hr⟩ := ih tail (by
      change (insert w U).card = k + 1
      rw [Finset.card_insert_of_notMem wU]
      omega)
    have keepA : a ∉ insert w U := by simp [wA.symm, aU]
    have keepB : b ∉ insert w U := by simp [wB.symm, bU]
    have other : ∀ x ∈ insert w U, x ≠ w → x ∈ insert a (insert b U) := by
      intro x hx hn
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((Finset.mem_insert.mp hx).resolve_left hn))
    have ha : a ∈ insert a (insert b U) := Finset.mem_insert_self ..
    have hb : b ∈ insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    cases op
    · exact kw_step goal _ _ a b w (fun _ i => !(a.testBit i)) f ha hb ab keepA keepB other hf hr
        (fun e i h1 h2 h3 => and_cu a b e i h1 h2 h3) (fun e i h1 h2 h3 => and_cv a b e i h1 h2 h3)
        (fun _ _ _ _ h => h.symm)
    · exact kw_step goal _ _ a b w (fun e _ => a.testBit e) f ha hb ab keepA keepB other hf hr
        (fun e i h1 h2 h3 => or_cu a b e i h1 h2 h3) (fun e i h1 h2 h3 => or_cv a b e i h1 h2 h3)
        (fun _ _ _ _ _ => rfl)
theorem liveDirected {mask goal : Word} {k : Nat} {S : Finset Word}
    (live : LiveWord mask goal k 0 S) {p n : Nat}
    (hp : goal.testBit p = true) (hn : goal.testBit n = false) :
    ∃ w ∈ S, w.testBit p = true ∧ w.testBit n = false := by
  induction k generalizing S with
  | zero =>
    obtain ⟨_,rfl,_⟩ := live
    exact ⟨goal, by simp, hp, hn⟩
  | succ k ih =>
    rcases live with ⟨u, U, a, ueq, _⟩ | ⟨U,a,b,op,rfl,pa,pb,ab,fresh,tail⟩
    · omega
    obtain ⟨w, hw, wp, wn⟩ := ih tail
    rcases Finset.mem_insert.mp hw with eq | hU
    · subst w
      cases op
      · by_cases ha : a.testBit n = false
        · exact ⟨a, Finset.mem_insert_self .., and_cu a b p n wp wn (by simp [ha])⟩
        · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
            and_cv a b p n wp wn (by cases h : a.testBit n <;> simp_all)⟩
      · by_cases ha : a.testBit p = true
        · exact ⟨a, Finset.mem_insert_self .., or_cu a b p n wp wn ha⟩
        · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
            or_cv a b p n wp wn (by cases h : a.testBit p <;> simp_all)⟩
    · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),wp,wn⟩
namespace PackedRect
end PackedRect
def DagAuto (mask goal : Word) (select : Fin rows → Fin rows) : Prop :=
  Function.Surjective select ∧ relabel select mask = mask ∧ relabel select goal = goal
abbrev WordMoveStep := List (Word × Nat) × List (Word × Nat)
abbrev WordMove := List WordMoveStep
def mixStep (m : WordMoveStep) (w : Word) : Word :=
  let left := List.rec 0 (fun (part,n) _ acc => ((w &&& part) <<< n) ||| acc) m.1
  let right := List.rec 0 (fun (part,n) _ acc => ((w &&& part) >>> n) ||| acc) m.2
  left ||| right
def mixMove (move : WordMove) (w : Word) : Word :=
  (List.rec (motive := fun _ => Word → Word) id
    (fun step _ next w => next (mixStep step w)) move) w
theorem maskedBelow {mask w : Word} (bm : Masked (fullMask rows) mask)
    (bw : Masked mask w) : Masked (fullMask rows) w := by
  unfold Masked at *
  rw [← bw, Nat.land_assoc, bm, bw]
theorem liveMaskedImage {mask goal : Word} {select : Fin rows → Fin rows}
    (auto : DagAuto mask goal select) (maskBounds : Masked (fullMask rows) mask)
    {k t : Nat} {S : Finset Word} (live : LiveWord mask goal k t S)
    (masked : ∀ w ∈ S, Masked mask w) :
    LiveWord mask goal k t (S.image (relabel select)) := by
  let f := relabel select
  have hmask : f mask = mask := auto.2.1
  have inj {a b : Word} (ma : Masked mask a) (mb : Masked mask b) :
      f a = f b → a = b :=
    relabelInj select auto.1 (maskedBelow maskBounds ma) (maskedBelow maskBounds mb)
  have proper {a : Word} (ma : Masked mask a) (ha : properWord mask a) :
      properWord mask (f a) := by
    exact ⟨fun eq => ha.1 (inj ma (by simp [Masked]) (eq.trans (relabelZero select).symm)),
      fun eq => ha.2 (inj ma (by simp [Masked]) (eq.trans hmask.symm))⟩
  have freshImage {S : Finset Word} {v : Word} (hv : v ∉ S) (mv : Masked mask v)
      (ms : ∀ w ∈ S, Masked mask w) : f v ∉ S.image f := by
    intro hw
    obtain ⟨w,hs,eq⟩ := Finset.mem_image.mp hw
    exact hv (inj (ms w hs) mv eq ▸ hs)
  induction live using LiveWord.ind with
  | stop hp =>
    rw [Finset.image_singleton, auto.2.2]
    exact LiveWord.stop hp
  | @unary k t U a ha fresh tail ih =>
    let v := mask ^^^ a
    have ma := masked a (Finset.mem_insert_self ..)
    have mv : Masked mask v := by
      apply maskedGate (bank := [a]) (by simpa using ma)
      exact Or.inl ⟨a, Or.inr (Or.inr (by simp)), rfl⟩
    have hnew : ∀ w ∈ insert v U, Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem hU)
    have fve : f v = mask ^^^ f a := by
      change relabel select (mask ^^^ a) = _
      rw [relabelXor, auto.2.1]
    have ht := ih hnew
    have hf := freshImage fresh mv masked
    change LiveWord mask goal (k+1) (t+1) ((insert a U).image f)
    rw [Finset.image_insert] at ht hf
    change LiveWord mask goal k t (insert (f v) (U.image f)) at ht
    rw [fve] at ht hf
    rw [Finset.image_insert]
    exact LiveWord.unary (proper ma ha) hf ht
  | @binary k t U a b op pa pb ab fresh tail ih =>
    let v := binWord op a b
    have ma := masked a (Finset.mem_insert_self ..)
    have mb := masked b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have mv : Masked mask v := by
      apply maskedGate (bank := [a,b]) (by simpa using And.intro ma mb)
      exact Or.inr ⟨a,b,Or.inr (Or.inr (by simp)),Or.inr (Or.inr (by simp)),by
        cases op <;> simp [v, binWord]⟩
    have hnew : ∀ w ∈ insert v U, Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU))
    have fve : f v = binWord op (f a) (f b) := by
      cases op
      · exact relabelAnd ..
      · exact relabelOr ..
    have ht := ih hnew
    have hf := freshImage fresh mv masked
    change LiveWord mask goal (k+1) t ((insert a (insert b U)).image f)
    rw [Finset.image_insert] at ht
    change LiveWord mask goal k t (insert (f v) (U.image f)) at ht
    rw [fve] at ht
    rw [Finset.image_insert, Finset.image_insert, fve] at hf
    rw [Finset.image_insert, Finset.image_insert]
    exact LiveWord.binary (proper ma pa) (proper mb pb) (fun h => ab (inj ma mb h)) hf ht
def dagMoveWords (m : WordMove) (ws : List Word) : List Word :=
  List.rec [] (fun w _ next => insertWord (mixMove m w) next) ws
theorem dagMoveSet {m : WordMove} {ws : List Word} {select : Fin rows → Fin rows}
    (agree : ∀ w ∈ ws, mixMove m w = relabel select w) :
    (dagMoveWords m ws).toFinset = ws.toFinset.image (relabel select) := by
  induction ws with
  | nil => simp [dagMoveWords]
  | cons w ws ih =>
    change (insertWord (mixMove m w) (dagMoveWords m ws)).toFinset = _
    rw [insertWordSet, ih (fun w hw => agree _ (List.mem_cons_of_mem _ hw)),
      agree _ List.mem_cons_self, List.toFinset_cons, Finset.image_insert]
abbrev DagLink := Nat × Nat
abbrev DagLinks := Nat → Nat → Option DagLink
def dagRef (count : Nat) (states : Nat → Option RowState)
    (moves : Array WordMove) (links : DagLinks) (parent token : Nat) (state : RowState) : Bool :=
  match links parent token with
  | none => false
  | some (destination, auto) =>
    Nat.blt destination count &&
      match states destination with
      | none => false
      | some saved =>
        saved.1 == state.1 &&
          if auto == 0 then saved.2.1 == state.2.1
          else match moves[auto-1]? with
               | none => false
               | some m => saved.2.1 == dagMoveWords m state.2.1
def dagStateOK (mask : Word) (ws : List Word) : Bool :=
  (ws.dedup.length == ws.length) && ws.all (fun w => w &&& mask == w)
theorem dagStateOKSpec {mask : Word} {ws : List Word} (ok : dagStateOK mask ws = true) :
    ws.Nodup ∧ ∀ w ∈ ws, Masked mask w := by
  simp only [dagStateOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  exact ⟨List.nodup_iff_length_dedup_eq.mpr ok.1, ok.2⟩
theorem childStateData {mask token : Nat} {state child : RowState}
    (eval : childState mask token state = some child)
    (masked : ∀ w ∈ state.2.1, Masked mask w) :
    child.1 < state.1 ∧ ∀ w ∈ child.2.1, Masked mask w := by
  obtain ⟨fuel,ws,history⟩ := state
  let keep := token % 4
  let op := token / 4 % 3
  let a := token / (4 * 3 * 64)
  let b := token / (4 * 3) % 64
  let x := ws.getD a 0
  let y := ws.getD b 0
  let z := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
  let rest := keepWord (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
  let bad : Bool := fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b)
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z,x,y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb,hs] at eval
  have eq : (fuel-1, insertWord z rest, (z,x,y) :: history) = child := by simpa [hb,hs] using eval
  subst child
  have pos : 0 < fuel := by
    by_contra! h
    have he : fuel = 0 := by omega
    simp [bad, he] at hb
  refine ⟨by dsimp; omega,?_⟩
  have read (i : Nat) : AvailableWord mask ws (ws.getD i 0) := by
    simp only [List.getD_eq_getElem?_getD]
    cases h : ws[i]? with
    | none => exact Or.inl rfl
    | some a => exact Or.inr (Or.inr (List.mem_of_getElem? h))
  have hm : Masked mask z := by
    apply maskedGate masked
    unfold z
    split
    · exact Or.inr ⟨x,y,read _,read _,Or.inl rfl⟩
    split
    · exact Or.inr ⟨x,y,read _,read _,Or.inr rfl⟩
    · exact Or.inl ⟨x,read _,rfl⟩
  intro w hw
  rcases insertWordMem.mp hw with rfl | other
  · exact hm
  · apply masked w
    apply keepSubset (keep.testBit 0) x ws w
    exact keepSubset (op == 2 || keep.testBit 1) y _ w other
def DagMovesOK (mask goal : Word) (width : Nat) (moves : Array WordMove) : Prop :=
  ∀ (i : Nat) (m : WordMove), moves[i]? = some m →
    ∃ select : Fin width → Fin width, DagAuto mask goal select ∧
      ∀ w, Masked mask w → mixMove m w = relabel select w
theorem dagLinked {mask goal : Word} {width count : Nat} {states : Nat → Option RowState}
    {moves : Array WordMove} {links : DagLinks} {parent token : Nat} {state : RowState}
    (bounds : Masked (fullMask width) mask)
    (valid : DagMovesOK mask goal width moves)
    (masked : ∀ w ∈ state.2.1, Masked mask w)
    (ok : dagRef count states moves links parent token state = true)
    {k t : Nat} (live : LiveWord mask goal k t state.2.1.toFinset) :
    ∃ i saved, i < count ∧ states i = some saved ∧ saved.1 = state.1 ∧
      LiveWord mask goal k t saved.2.1.toFinset := by
  unfold dagRef at ok
  split at ok
  · contradiction
  next destination auto h =>
    have hd := Nat.blt_eq.mp (Bool.and_eq_true_iff.mp ok).1
    have finish := (Bool.and_eq_true_iff.mp ok).2
    cases eq : states destination with
    | none => simp [eq] at finish
    | some saved =>
      simp only [eq, Bool.and_eq_true, beq_iff_eq] at finish
      refine ⟨destination,saved,hd,eq,finish.1,?_⟩
      have last := finish.2
      split at last
      · have same : saved.2.1 = state.2.1 := beq_iff_eq.mp last
        rwa [same]
      · split at last
        · contradiction
        next m hm =>
          obtain ⟨select,auto,agree⟩ := valid _ _ hm
          have same : saved.2.1 = dagMoveWords m state.2.1 := beq_iff_eq.mp last
          rw [same, dagMoveSet (fun w hw => agree w (masked w hw))]
          exact liveMaskedImage auto bounds live (fun w hw => masked _ (List.mem_toFinset.mp hw))
theorem stockMaskedOfCheck {mask : Word} {stock : List Word}
    (h : stock.all (fun w => w &&& mask == w) = true) :
    ∀ w ∈ stock, Masked mask w := by
  intro w hw
  exact beq_iff_eq.mp (List.all_eq_true.mp h w hw)
def hcsGateVal {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or => args.foldr (· ||| ·) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
  | _ => 0
def hcsStep {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List (BitVec rows) :=
  bank ++ [hcsGateVal bank g]
theorem hcsGetDBit {rows : Nat} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp
theorem hcsAndBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]
theorem hcsOrBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]
theorem hcsGateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, BitVec.getLsbD_not, i.isLt,
      decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, hcsGetDBit]
theorem hcsFoldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [hcsStep, List.map_append, List.map_cons, List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]
end WordEngine
open WordEngine PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Plane
abbrev AO (m : Nat) (stock : List Word) (out : Word) :=
  ∃ a b, AvailableWord m stock a ∧ AvailableWord m stock b ∧ (out = a &&& b ∨ out = a ||| b)
def AOBuild (m : Nat) (stock : List Word) : List Word → Prop
  | [] => True
  | w::ws => AO m stock w ∧ AOBuild m (w::stock) ws
def AOLower (m : Nat) (stock : List Word) (target : Word) (bound : Nat) : Prop :=
  ∀ vs, AOBuild m stock vs → AvailableWord m (vs++stock) target → bound ≤ vs.length
theorem aoOfAvailable {m stock w} (av : AvailableWord m stock w) : AO m stock w :=
  ⟨w,0,av,Or.inl rfl,Or.inr (by simp)⟩
theorem aoWeaken {m small big vs} (sub : ∀ w ∈ small, AvailableWord m big w)
    (h : AOBuild m small vs) : AOBuild m big vs := by
  induction vs generalizing small big with
  | nil => trivial
  | cons w ws ih =>
    obtain ⟨⟨a,b,ha,hb,ev⟩,tail⟩ := h
    refine ⟨⟨a,b,availableWeaken sub ha,availableWeaken sub hb,ev⟩,ih ?_ tail⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Or.inr (Or.inr List.mem_cons_self)
    · exact availableWeaken (fun v hv => Or.inr (Or.inr (List.mem_cons_of_mem _ hv))) (sub _ ha)
variable {mask target : Word}
theorem pullAO {w : List (Word)} {z : Word} {k S} (h : LiveWord mask target k 0 S)
    (hz : wordRep mask w z ∨ binaryWitness mask w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+1 ∧ LiveWord mask target k' 0 S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := liveWordProper h z hm
      rcases hz with hr | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (binWord d a b)
        have ht : LiveWord mask target k 0 (insert (binWord d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : binWord d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,LiveWord.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
theorem extractAO {roots values : List Word}
    (all : ∀ w ∈ roots, Masked mask w) (builds : AOBuild mask roots values)
    (hit : AvailableWord mask (values ++ roots) target) (p : properWord mask target) :
    ∃ k S, k ≤ values.length ∧ LiveWord mask target k 0 S ∧ ∀ w ∈ S, w ∈ roots := by
  have hm := (hit.resolve_left p.1).resolve_left p.2
  induction values generalizing roots with
  | nil =>
    exact ⟨0, {target}, Nat.zero_le _, LiveWord.stop p, by simpa using hm⟩
  | cons w ws ih =>
    have next : ∀ v ∈ w :: roots, Masked mask v := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact maskedGate all (Or.inr builds.1)
      · exact all _ hv
    have ht : AvailableWord mask (ws ++ w :: roots) target := by
      exact Or.inr (Or.inr (by simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hm))
    obtain ⟨k, S, hk, live, sub⟩ :=
      ih next builds.2 ht ((ht.resolve_left p.1).resolve_left p.2)
    have available : ∀ v ∈ S, v ∈ roots ++ [w] := by
      intro v h
      simpa [or_comm] using sub v h
    have gate : wordRep mask roots w ∨ binaryWitness mask roots w := by
      obtain ⟨a,b,ha,hb,eq|eq⟩ := builds.1
      · subst w; exact classifyBinary all false ha hb
      · subst w; exact classifyBinary all true ha hb
    obtain ⟨k', S', hk', hl, hsub⟩ := pullAO live gate available
    exact ⟨k', S', by simp only [List.length_cons]; omega, hl, hsub⟩
theorem aoGateWord {rows : Nat} (bank : List (BitVec rows))
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp))
    (hlen : g.inputs.length ≤ 2) :
    AO (fullMask rows) (bank.map BitVec.toNat) (hcsGateVal bank g).toNat := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have zeroAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) 0 := Or.inl rfl
  have maskAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) (fullMask rows) :=
    Or.inr (Or.inl rfl)
  rcases hop with rfl | rfl
  · cases ins with
    | nil => exact aoOfAvailable (by simpa [hcsGateVal, fullMask] using maskAv)
    | cons a t =>
      cases t with
      | nil => exact aoOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inl (by simp [hcsGateVal, BitVec.toNat_and])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact aoOfAvailable (by simpa [hcsGateVal] using zeroAv)
    | cons a t =>
      cases t with
      | nil => exact aoOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inr (by simp [hcsGateVal, BitVec.toNat_or])⟩
        | cons c t => simp at hlen
theorem aoBuilds {rows : Nat} (bank : List (BitVec rows))
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    ∃ vs, vs.length = gs.length ∧ AOBuild (fullMask rows) (bank.map BitVec.toNat) vs ∧
      ∀ v ∈ gs.foldl hcsStep bank, v.toNat ∈ vs ++ bank.map BitVec.toNat := by
  induction gs generalizing bank with
  | nil => exact ⟨[], rfl, trivial, fun _ h => List.mem_map_of_mem h⟩
  | cons g gs ih =>
    let v := hcsGateVal bank g
    have hg := hfan g List.mem_cons_self
    obtain ⟨xs, len, build, sub⟩ := ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
    have eq : (hcsStep bank g).map BitVec.toNat = bank.map BitVec.toNat ++ [v.toNat] := by
      simp [hcsStep, v]
    rw [eq] at build
    refine ⟨v.toNat :: xs, by simp [len], ⟨aoGateWord bank g hg.1 hg.2, aoWeaken ?_ build⟩, ?_⟩
    · intro u hu; exact Or.inr (Or.inr (by simpa [or_comm] using hu))
    · intro u hu; have m := sub u hu; rw [eq] at m
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using m
theorem monoFan {C : Circuit} (legal : Monotone2 C) : FanInTwo C := by
  intro g hg
  obtain ⟨op,sz⟩ := legal g hg
  refine ⟨?_,sz⟩
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
  tauto
end Plane
open WordEngine PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
namespace Plane
set_option maxHeartbeats 0 in
def posted (u v : Fin 5) : Bool := (8151129 : Nat).testBit (5*u.val+v.val)
set_option maxHeartbeats 0 in
def raw : List (BitVec 25) := [0x1f, 0x3e0, 0x7c00, 0xf8000, 0x1f00000, 0x108421, 0x210842, 0x421084, 0x842108, 0x1084210]
set_option maxHeartbeats 0 in
def stock : List Word := raw.map BitVec.toNat
set_option maxHeartbeats 0 in
def target25 : BitVec 25 := 8151129
set_option maxHeartbeats 0 in
abbrev T : Word := target25.toNat
set_option maxHeartbeats 0 in
def point (r : Fin 25) := oneEach (Fin.ofNat 5 (r.val / 5)) (Fin.ofNat 5 (r.val % 5))
set_option maxHeartbeats 0 in
theorem representation_live (C : Circuit) (legal : Monotone2 C) (right : Represents posted C) :
    ∃ k ≤ C.size, LiveWord (fullMask 25) T k 0 stock.toFinset := by
  have rawBits : ∀ r : Fin 25, (raw.map fun w => w.getLsbD r.val) = point r := by decide +kernel
  have goalBits : ∀ r : Fin 25, target25.getLsbD r.val =
      posted (Fin.ofNat 5 (r.val / 5)) (Fin.ofNat 5 (r.val % 5)) := by decide +kernel
  let eb := C.gates.foldl hcsStep raw
  have eq : eb.getD C.output 0 = target25 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Fin 25 := ⟨j,hj⟩
    have bits := hcsFoldBits raw r C.gates (monoFan legal)
    have ack := right (Fin.ofNat 5 (r.val / 5)) (Fin.ofNat 5 (r.val % 5))
    change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (point r)).getD C.output false = _ at ack
    rw [← rawBits r,← bits] at ack
    exact (hcsGetDBit eb j C.output).trans (ack.trans (goalBits r).symm)
  obtain ⟨ws,len,built,sub⟩ := aoBuilds raw C.gates legal
  have hit : AvailableWord (fullMask 25) (ws++stock) T := by
    change AvailableWord _ _ target25.toNat
    rw [←eq,List.getD_eq_getElem?_getD]
    cases h : eb[C.output]? with
    | none => exact Or.inl rfl
    | some w => exact Or.inr (Or.inr (sub w (List.mem_of_getElem? h)))
  obtain ⟨k,S,budget,run,subset⟩ := extractAO (stockMaskedOfCheck (by decide +kernel : stock.all (fun w => w &&& fullMask 25 == w) = true)) built hit
      (by unfold properWord; decide +kernel)
  have witnesses : ∀ w ∈ stock, ∃ p n : Fin 25, T.testBit p.val = true ∧ T.testBit n.val = false ∧
      ∀ u ∈ stock, u.testBit p.val = true → u.testBit n.val = false → u = w := by decide +kernel
  have same : S = stock.toFinset := by
    ext w; constructor
    · exact fun h => List.mem_toFinset.mpr (subset w h)
    · intro h
      obtain ⟨p,n,yes,no,unique⟩ := witnesses w (List.mem_toFinset.mp h)
      obtain ⟨u,mem,a,b⟩ := liveDirected run yes no
      exact (unique u (subset u mem) a b) ▸ mem
  exact ⟨k,budget.trans (Nat.le_of_eq len),same ▸ run⟩
end Plane
open WordEngine PEqualNP.Represents
namespace Plane.Orbit
set_option maxHeartbeats 0 in
def MonoViable (mask goal : Word) (s : RowState) : Prop :=
  s.2.1.Nodup ∧ ∃ k ≤ s.1, LiveWord mask goal k 0 s.2.1.toFinset
set_option maxHeartbeats 0 in
def AOChild (mask : Word) (s c : RowState) : Prop :=
  ∃ a b op keep, a < s.2.1.length ∧ a < b ∧ b < s.2.1.length ∧ op < 2 ∧ keep < 4 ∧
    childState mask (gateToken a b op keep) s = some c
set_option maxHeartbeats 0 in
theorem binaryMonoProgress {mask fuel k : Nat} {x y target : Word} {d : Bool} {U : Finset Word}
    {ws : List Word} {history : List (Word × Word × Word)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel)
    (he : ws.toFinset = insert x (insert y U)) (xy : x ≠ y)
    (ordered : ws.idxOf x < ws.idxOf y) (fresh : binWord d x y ∉ insert x (insert y U))
    (tail : LiveWord mask target k 0 (insert (binWord d x y) U)) :
    ∃ child, AOChild mask (fuel, ws, history) child ∧ MonoViable mask target child := by
  let a := ws.idxOf x
  let b := ws.idxOf y
  have xm : x ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ym : y ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ha : a < ws.length := List.idxOf_lt_length_iff.mpr xm
  have hb : b < ws.length := List.idxOf_lt_length_iff.mpr ym
  have hab : a < b := ordered
  have hx : ws.getD a 0 = x := getWord xm
  have hy : ws.getD b 0 = y := getWord ym
  let v := binWord d x y
  have p := liveWordProper tail v (Finset.mem_insert_self _ _)
  let saveX := decide (x ∈ U)
  let saveY := decide (y ∈ U)
  let keep := (if saveX then 1 else 0) + (if saveY then 2 else 0)
  have fields : keep < 4 ∧ keep.testBit 0 = saveX ∧ keep.testBit 1 = saveY := by
    unfold keep
    cases saveX <;> cases saveY <;> decide
  obtain ⟨keepLt, bx, by'⟩ := fields
  have fn : v ∉ ws := by simpa [← List.mem_toFinset, he] using fresh
  let rest := keepWord saveY y (keepWord saveX x ws)
  let child : RowState := (fuel - 1, insertWord v rest, (v, x, y) :: history)
  refine ⟨child, ⟨a, b, if d then 1 else 0, keep, ha, hab, hb, ?_, keepLt, ?_⟩, ?_⟩
  · cases d <;> decide
  · have eq := binaryChild (fuel := fuel) (history := history) d hab hb (by omega) (by omega) keepLt hx hy p fn
    rw [bx, by'] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup (keepNodup nd saveX x) saveY y)
      (fun h => fn (keepSubset saveX x ws _ (keepSubset saveY y _ _ h))), k, by change k ≤ fuel - 1; omega, ?_⟩
    change LiveWord mask target k 0 (insertWord v rest).toFinset
    rw [insertWordSet, keepPairSet nd xy he]
    exact tail
set_option maxHeartbeats 0 in
theorem monoProgress {mask : Nat} {target : Word} {state : RowState}
    (width : state.2.1.length ≤ 64) (h : MonoViable mask target state) :
    target ∈ state.2.1 ∨ ∃ child, AOChild mask state child ∧ MonoViable mask target child := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨nd, k, cap, live⟩ := h
  cases k with
  | zero =>
    obtain ⟨_, eq, _⟩ := live
    left
    change ws.toFinset = {target} at eq
    rw [← List.mem_toFinset, eq]
    simp
  | succ k =>
    right
    rcases live with ⟨u,U,x,impossible,eq,px,fresh,tail⟩ | ⟨U,x,y,d,eq,px,py,xy,fresh,tail⟩
    · omega
    have xm : x ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have ym : y ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have diff : ws.idxOf x ≠ ws.idxOf y := by
      intro same
      apply xy
      rw [← getWord xm, same, getWord ym]
    by_cases h : ws.idxOf x < ws.idxOf y
    · exact binaryMonoProgress nd width cap eq xy h fresh tail
    · have eq' : ws.toFinset = insert y (insert x U) := by rw [eq, Finset.insert_comm]
      have fresh' : binWord d y x ∉ insert y (insert x U) := by
        rw [binWord_comm d y x, Finset.insert_comm]; exact fresh
      have tail' : LiveWord mask target k 0 (insert (binWord d y x) U) := by
        rw [binWord_comm d y x]; exact tail
      exact binaryMonoProgress nd width cap eq' xy.symm (by omega) fresh' tail'
set_option maxHeartbeats 0 in
def coverAt (n : Nat) (ws : List Word) : Word :=
  List.rec 0 (fun w _ acc => if w.testBit n then acc else w ||| acc) ws
set_option maxHeartbeats 0 in
theorem coverAt_bit {w : Word} {ws : List Word} {p n : Nat}
    (member : w ∈ ws) (pos : w.testBit p = true) (neg : w.testBit n = false) :
    (coverAt n ws).testBit p = true := by
  induction ws with
  | nil => simp at member
  | cons x xs ih =>
    change (if x.testBit n then coverAt n xs else x ||| coverAt n xs).testBit p = true
    rcases List.mem_cons.mp member with rfl | tail
    · simp [neg, Nat.testBit_or, pos]
    · cases x.testBit n <;> simp [Nat.testBit_or, ih tail]
set_option maxHeartbeats 0 in
theorem coverAt_live {mask goal : Word} {ws : List Word} {k n : Nat}
    (live : LiveWord mask goal k 0 ws.toFinset) (neg : goal.testBit n = false) :
    goal &&& coverAt n ws = goal := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_and]
  cases h : goal.testBit p with
  | false => rfl
  | true =>
    obtain ⟨w,mem,one,zero⟩ := liveDirected live h neg
    simp [coverAt_bit (List.mem_toFinset.mp mem) one zero]
set_option maxHeartbeats 0 in
def basicCut (goal : Word) (neg : List Nat) (s : RowState) : Bool :=
  decide (s.1+1 < s.2.1.length) ||
    neg.any (fun n => (goal &&& coverAt n s.2.1) != goal)
set_option maxHeartbeats 0 in
theorem basicOpen {mask goal : Word} {neg : List Nat} {s : RowState}
    (negative : ∀ n ∈ neg, goal.testBit n = false) (v : MonoViable mask goal s) :
    basicCut goal neg s = false := by
  obtain ⟨nd,k,cap,live⟩ := v
  have size := (liveWordSize live).2
  rw [List.toFinset_card_of_nodup nd] at size
  simp only [basicCut, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    List.any_eq_false, bne_iff_ne, ne_eq]
  constructor
  · omega
  · intro n mem
    simp [coverAt_live live (negative n mem)]
set_option maxHeartbeats 0 in
abbrev Table := Nat → Option RowState
set_option maxHeartbeats 0 in
abbrev EdgeCut := Nat → Nat → RowState → Bool
set_option maxHeartbeats 0 in
def pass (m g : Word) (neg : List Nat) (states : Table) (count : Nat)
    (moves : Array WordMove) (links : DagLinks) (cut : EdgeCut) (i : Nat)
    (s : RowState) (a b op keep : Nat) : Bool :=
  let tok := gateToken a b op keep
  match childState m tok s with
  | none => true
  | some c => basicCut g neg c || cut i tok c || dagRef count states moves links i tok c
set_option maxHeartbeats 0 in
def scan (m g : Word) (neg : List Nat) (states : Table) (count : Nat)
    (moves : Array WordMove) (links : DagLinks) (cut : EdgeCut) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some s =>
    let n := s.2.1.length
    dagStateOK m s.2.1 && decide (n ≤ 64) && !(s.2.1.contains g) &&
    treeBlock 0 n (fun a => treeBlock (a+1) (n-(a+1)) (fun b =>
      treeBlock 0 2 (fun op => treeBlock 0 4 (pass m g neg states count moves links cut i s a b op))))
set_option maxHeartbeats 0 in
theorem tableSound {m g : Word} {width count : Nat} {neg : List Nat} {states : Table}
    {moves : Array WordMove} {links : DagLinks} {cut : EdgeCut}
    (mb : Masked (fullMask width) m) (autos : DagMovesOK m g width moves)
    (negative : ∀ n ∈ neg, g.testBit n = false)
    (cutOpen : ∀ i tok s, MonoViable m g s → cut i tok s = false)
    (checked : ∀ i < count, scan m g neg states count moves links cut i = true) :
    ∀ fuel i s, i < count → states i = some s → s.1 = fuel →
      ∀ k ≤ fuel, ¬ LiveWord m g k 0 s.2.1.toFinset := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | ind fuel ih =>
    intro i s hi row cap k fit live
    have h := checked i hi
    simp only [scan, row, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    obtain ⟨nd,masked⟩ := dagStateOKSpec h.1.1.1
    rcases monoProgress h.1.1.2 ⟨nd,k,cap ▸ fit,live⟩ with hit | ⟨c,edge,v⟩
    · simpa [hit] using h.1.2
    obtain ⟨a,b,op,keep,ha,hab,hb,hop,hkeep,ev⟩ := edge
    have aa := treeBlock_at h.2 (i := a) (Nat.zero_le _) (by simpa using ha)
    have bb := treeBlock_at aa (i := b) (by omega) (by omega)
    have oo := treeBlock_at bb (i := op) (Nat.zero_le _) (by simpa using hop)
    have kk := treeBlock_at oo (i := keep) (Nat.zero_le _) (by simpa using hkeep)
    simp only [pass, ev, basicOpen negative v, cutOpen _ _ _ v, Bool.false_or] at kk
    obtain ⟨less,cm⟩ := childStateData ev masked
    obtain ⟨_,j,fit',plan⟩ := v
    obtain ⟨dest,saved,inRange,lookup,eq,tail⟩ := dagLinked mb autos cm kk plan
    exact ih c.1 (cap ▸ less) dest saved inRange lookup eq j fit' tail
end Plane.Orbit
open WordEngine
namespace Plane.Geometry
open Plane.Orbit
set_option maxHeartbeats 0 in
def forcesAt (goal : Word) (ws : List Word) (w : Word) (p n : Nat) : Bool :=
  goal.testBit p && !goal.testBit n &&
    ws.all (fun v => v == w || !v.testBit p || v.testBit n)
set_option maxHeartbeats 0 in
theorem forcedAnswer {g : Word} {ws : List Word} {w : Word} {p n : Nat}
    {f : Nat → Nat → Word}
    (legal : ∀ p n, g.testBit p = true → g.testBit n = false →
      f p n ∈ ws.toFinset ∧ (f p n).testBit p = true ∧ (f p n).testBit n = false)
    (h : forcesAt g ws w p n = true) :
    g.testBit p = true ∧ g.testBit n = false ∧ f p n = w := by
  simp only [forcesAt, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨mem,on,off⟩ := legal _ _ h.1.1 h.1.2
  have v := List.all_eq_true.mp h.2 _ (List.mem_toFinset.mp mem)
  exact ⟨h.1.1,h.1.2,by simpa [on,off] using v⟩
set_option maxHeartbeats 0 in
def overlap (g : Word) (ws : List Word) (x y : Word) (p n px nx py ny : Nat) : Bool :=
  x != y && forcesAt g ws x p nx && forcesAt g ws x px n &&
  forcesAt g ws y p ny && forcesAt g ws y py n
set_option maxHeartbeats 0 in
theorem overlapImpossible {g : Word} {ws : List Word} {x y p n px nx py ny : Nat}
    (kw : KWPartition g ws.toFinset) : overlap g ws x y p n px nx py ny = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨f,legal,box⟩ := kw
  simp only [overlap, Bool.and_eq_true, bne_iff_ne] at h
  obtain ⟨⟨⟨⟨ne,a⟩,b⟩,c⟩,d⟩ := h
  obtain ⟨pos,nnx,xa⟩ := forcedAnswer legal a
  obtain ⟨ppx,neg,xb⟩ := forcedAnswer legal b
  obtain ⟨_,nny,ya⟩ := forcedAnswer legal c
  obtain ⟨ppy,_,yb⟩ := forcedAnswer legal d
  have X := box p nx px n pos ppx nnx neg (xa.trans xb.symm)
  have Y := box p ny py n pos ppy nny neg (ya.trans yb.symm)
  exact ne ((X.trans xa).symm.trans (Y.trans ya))
set_option maxHeartbeats 0 in
theorem tightPartition {m g : Word} {s : RowState} (live : MonoViable m g s)
    (tight : s.2.1.length = s.1+1) : KWPartition g s.2.1.toFinset := by
  obtain ⟨nd,k,fit,run⟩ := live
  have sz := (liveWordSize run).2
  have card := List.toFinset_card_of_nodup nd
  apply kwFromLive run
  omega
set_option maxHeartbeats 0 in
def rectangleReject (g : Word) (s : RowState) (code : Nat) : Bool :=
  let field := unpack code 5
  (s.2.1.length == s.1+1) &&
  overlap g s.2.1 (s.2.1.getD (field 0) 0) (s.2.1.getD (field 1) 0)
    (field 2) (field 3) (field 4) (field 5) (field 6) (field 7)
set_option maxHeartbeats 0 in
theorem rectangleOpen {m g : Word} {s : RowState} (code : Nat)
    (live : MonoViable m g s) : rectangleReject g s code = false := by
  unfold rectangleReject
  by_cases t : s.2.1.length = s.1+1
  · simp [t,overlapImpossible (tightPartition live t)]
  · simp [t]
end Plane.Geometry
open WordEngine
namespace Plane.Project
def Pool (g : Word) : Nat → Finset Word → Prop
  | 0, s => g ∈ s
  | n+1, s => Pool g n s ∨ ∃ a ∈ s, ∃ b ∈ s, ∃ d, Pool g n (insert (binWord d a b) s)
theorem weakenPool {g : Word} {n s q} (sub : s ⊆ q) (h : Pool g n s) : Pool g n q := by
  induction n generalizing s q with
  | zero => exact sub h
  | succ n ih =>
    rcases h with h | ⟨a,ha,b,hb,d,run⟩
    · exact Or.inl (ih sub h)
    · exact Or.inr ⟨a,sub ha,b,sub hb,d,ih (Finset.insert_subset_insert _ sub) run⟩
theorem maskedAO {mask goal : Word} {k s} (run : LiveWord mask goal k 0 s) (m : Word) (properGoal : ¬ maskedFlat m goal) :
    ∃ n, n+(flatSet m s).card ≤ k ∧ Pool (goal &&& m) n (projectedStock m s) := by
  induction k generalizing s with
  | zero =>
    have es := run.2.1
    subst s
    refine ⟨0,?_,?_⟩
    · simp only [flatSet, Finset.filter_singleton, properGoal, ite_false, Finset.card_empty,
        Nat.add_zero, Nat.le_refl]
    · change goal &&& m ∈ projectedStock m {goal}
      simp [projectedStock,visibleWords]
  | succ k ih =>
    rcases run with ⟨v,u,a,impossible,_⟩ | ⟨u,a,b,d,eq,pa,pb,ab,fresh,tail⟩
    · omega
    subst s
    let v := binWord d a b
    obtain ⟨n,cap,built⟩ := ih tail
    have nn : v ∉ u := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    change n+(flatSet m (insert v u)).card ≤ k at cap
    rw [flIns nn] at cap
    have ca := flLe m a (insert b u)
    have cb := flLe m b u
    by_cases simple : maskedFlat m a ∨ maskedFlat m b
    · have budget : n + (flatSet m (insert a (insert b u))).card ≤ k+1 := by
        by_cases fa : maskedFlat m a <;> by_cases fb : maskedFlat m b <;>
          simp only [fa,fb,ite_true,ite_false] at ca cb simple
        all_goals first | have vf : maskedFlat m v := flBoth fa fb; simp only [vf,ite_true] at cap; omega | omega | tauto
      refine ⟨n,budget,weakenPool ?_ built⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rcases hw with e|e|e|e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · subst w
        have cases := simpleBin (d := d) simple
        tauto
      · tauto
    · have fa : ¬maskedFlat m a := fun h => simple (Or.inl h)
      have fb : ¬maskedFlat m b := fun h => simple (Or.inr h)
      simp only [fa,fb,ite_false] at ca cb
      refine ⟨n+1,by omega,Or.inr ⟨a &&& m,?_,b &&& m,?_,d,weakenPool ?_ built⟩⟩
      · simp [projectedStock,prIns]
      · simp [projectedStock,prIns]
      · intro w hw
        simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
        rw [cofBinary] at hw
        tauto
theorem toBuild {m g : Word} {n s} {stock : List Word}
    (sources : ∀ x ∈ s, AvailableWord m stock x) (h : Pool g n s) :
    ∃ vs, vs.length ≤ n ∧ AOBuild m stock vs ∧ AvailableWord m (vs ++ stock) g := by
  induction n generalizing s stock with
  | zero => exact ⟨[],by simp,True.intro,sources g h⟩
  | succ n ih =>
    rcases h with h | ⟨a,ha,b,hb,d,h⟩
    · obtain ⟨vs,len,built,hit⟩ := ih sources h; exact ⟨vs,by omega,built,hit⟩
    · let z := binWord d a b
      have sub : ∀ x ∈ insert z s, AvailableWord m (z::stock) x := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Or.inr (Or.inr List.mem_cons_self)
        · exact availableWeaken (fun v hv => Or.inr (Or.inr (List.mem_cons_of_mem _ hv))) (sources _ hx)
      obtain ⟨vs,len,built,hit⟩ := ih sub h
      refine ⟨z::vs,by simp; omega,⟨⟨a,b,sources _ ha,sources _ hb,?_⟩,built⟩,?_⟩
      · cases d <;> simp [z,binWord]
      · rcases hit with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (by simpa [List.mem_append,List.mem_cons,or_left_comm,or_assoc] using h))
theorem appendAO {mask : Word} {stock xs ys : List Word} (left : AOBuild mask stock xs)
    (right : AOBuild mask (xs ++ stock) ys) : AOBuild mask stock (xs ++ ys) := by
  induction xs generalizing stock with
  | nil => exact right
  | cons x xs ih =>
    refine ⟨left.1, ih left.2 (aoWeaken ?_ right)⟩
    intro w hw
    exact Or.inr (Or.inr (by simpa [List.mem_append,List.mem_cons,or_assoc,or_left_comm] using hw))
theorem cut {mask goal m k S stock prep floor} (run : LiveWord mask goal k 0 S)
    (proper : ¬ maskedFlat m goal) (built : AOBuild m stock prep)
    (supply : ∀ x ∈ projectedStock m S, AvailableWord m (prep ++ stock) x)
    (lower : AOLower m stock (goal &&& m) floor) :
    floor + (flatSet m S).card ≤ prep.length + k := by
  obtain ⟨n,len,red⟩ := maskedAO run m proper
  obtain ⟨vs,cap,prog,hit⟩ := toBuild supply red
  have total := appendAO built prog
  have hit' : AvailableWord m ((prep++vs)++stock) (goal &&& m) := by
    rcases hit with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by simpa [List.mem_append,or_left_comm,or_comm,or_assoc] using h))
  have bound := lower _ total hit'
  simp only [List.length_append] at bound
  omega
end Plane.Project
open WordEngine
namespace Plane.Project
def oneAO (stock : List Word) (w : Word) : Bool :=
  stock.any fun a => stock.any fun b => (a &&& b == w) || (a ||| b == w)
theorem oneAO_spec {m : Word} {stock w} (h : oneAO stock w) : AO m stock w := by
  obtain ⟨a,ha,ok⟩ := List.any_eq_true.mp h
  obtain ⟨b,hb,ok⟩ := List.any_eq_true.mp ok
  have eq := Bool.or_eq_true_iff.mp ok
  exact ⟨a,b,Or.inr (Or.inr ha),Or.inr (Or.inr hb),eq.elim (fun e => Or.inl (eq_of_beq e).symm)
    (fun e => Or.inr (eq_of_beq e).symm)⟩
def cheapPrep (m : Word) (stock : List Word) : List Word → Option (List Word)
  | [] => some []
  | w::ws =>
    if availableB m stock w then cheapPrep m stock ws
    else if oneAO stock w then (cheapPrep m (w::stock) ws).map (w::·)
    else none
theorem inLarger {m w : Word} {xs raw : List Word} (h : AvailableWord m raw w) :
    AvailableWord m (xs ++ raw) w :=
  availableWeaken (fun _ hw => Or.inr (Or.inr (List.mem_append_right _ hw))) h
theorem cheapPrep_spec {m : Word} {stock needed vs}
    (h : cheapPrep m stock needed = some vs) :
    AOBuild m stock vs ∧ ∀ w ∈ needed, AvailableWord m (vs++stock) w := by
  induction needed generalizing stock vs with
  | nil =>
    obtain rfl := Option.some.inj h
    exact ⟨True.intro,by simp⟩
  | cons w ws ih =>
    simp only [cheapPrep] at h
    split at h
    · rename_i present
      obtain ⟨built,covered⟩ := ih h
      refine ⟨built,?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact inLarger (availableB_spec.mp present)
      · exact covered _ hv
    · split at h
      · rename_i step
        cases he : cheapPrep m (w::stock) ws with
        | none => simp [he] at h
        | some more =>
          simp [he] at h
          subst vs
          obtain ⟨built,covered⟩ := ih he
          refine ⟨⟨oneAO_spec step,built⟩,?_⟩
          intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact Or.inr (Or.inr (by simp))
          · apply availableWeaken (small := more++w::stock) (big := (w::more)++stock) _ (covered v hv)
            intro x hx
            exact Or.inr (Or.inr (by simpa [List.mem_append,List.mem_cons,or_assoc,or_left_comm] using hx))
      · contradiction
def cheapCut (m : Word) (low fuel : Nat) (stock ws : List Word) : Bool :=
  let needed := ws.map (· &&& m)
  match cheapPrep m stock needed with
  | none => false
  | some vs => decide (vs.length + fuel < low + flatCount m ws)
theorem cheapCut_sound {m mask goal low fuel stock ws k}
    (lower : AOLower m stock (goal &&& m) low) (proper : ¬ maskedFlat m goal)
    (nd : ws.Nodup) (hk : k ≤ fuel) (close : cheapCut m low fuel stock ws = true) :
    ¬ LiveWord mask goal k 0 ws.toFinset := by
  intro run
  unfold cheapCut at close
  cases he : cheapPrep m stock (ws.map (· &&& m)) with
  | none => simp [he] at close
  | some vs =>
    simp [he] at close
    obtain ⟨built,covered⟩ := cheapPrep_spec he
    have source : ∀ w ∈ projectedStock m ws.toFinset, AvailableWord m (vs++stock) w := by
      intro w hw
      simp only [projectedStock,visibleWords,Finset.mem_insert,Finset.mem_image,List.mem_toFinset] at hw
      rcases hw with rfl | rfl | ⟨v,hv,rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact covered _ (List.mem_map_of_mem hv)
    have bound := cut run proper built source lower
    rw [flatCountCard m nd] at close
    omega
end Plane.Project
open WordEngine
namespace Plane.Project
end Plane.Project
open WordEngine
namespace Plane.Project
end Plane.Project
open WordEngine
namespace Plane.Orbit
abbrev requiredTests (width : Nat) (goal : Word) (ws : List Word) : Prop :=
  ∀ w ∈ ws, ∃ p n : Fin width, goal.testBit p.val = true ∧ goal.testBit n.val = false ∧
    ∀ v ∈ ws, v.testBit p.val = true → v.testBit n.val = false → v = w
theorem lowerStock {m goal width fuel root count raw} {states : Table} {row : RowState}
    {neg : List Nat} {moves : Array WordMove} {links : DagLinks} {cut : EdgeCut}
    (all : ∀ w ∈ raw, Masked m w) (proper : properWord m goal) (needs : requiredTests width goal raw)
    (mb : Masked (fullMask width) m) (autos : DagMovesOK m goal width moves)
    (negative : ∀ n ∈ neg, goal.testBit n = false)
    (cutOpen : ∀ i tok s, MonoViable m goal s → cut i tok s = false)
    (checked : ∀ i < count, scan m goal neg states count moves links cut i = true)
    (index : root < count) (look : states root = some row) (rFuel : row.1 = fuel)
    (exactStock : row.2.1.toFinset = raw.toFinset) : AOLower m raw goal (fuel+1) := by
  intro vs builds hit
  by_contra! h
  obtain ⟨k,S,budget,live,sub⟩ := extractAO all builds hit proper
  have eq : S = raw.toFinset := by
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub _ hw)
    · intro hw
      obtain ⟨p,n,yes,no,only⟩ := needs _ (List.mem_toFinset.mp hw)
      obtain ⟨v,hv,a,b⟩ := liveDirected live yes no
      exact (only v (sub v hv) a b) ▸ hv
  rw [eq,←exactStock] at live
  exact tableSound mb autos negative cutOpen checked fuel root row index look rFuel k (by omega) live
end Plane.Orbit

open WordEngine PEqualNP.Represents
namespace Plane.Certificate
open Orbit Geometry Project

def minorMask : Word := 11534699
def minorGoal : Word := T &&& minorMask
def minorStock : List Word := [11, 352, 1048609, 2097218, 8388872, 11534336]
def negatives : List Nat := [1, 5, 8, 23]
def rows : Array RowState := #[
  (6, [11, 352, 1048609, 2097218, 8388872, 11534336], []),
  (5, [352, 1048609, 2097227, 8388872, 11534336], []),
  (4, [1048929, 2097227, 8388872, 11534336], []),
  (4, [1048609, 2097227, 8388968, 11534336], []),
  (4, [352, 1048609, 2097227, 11534600], []),
  (5, [11, 1048929, 2097218, 8388872, 11534336], []),
  (5, [11, 1048609, 2097218, 8388968, 11534336], []),
  (5, [11, 352, 1048609, 2097218, 11534600], [])
]
def states : Table := fun i => rows[i]?
def advice0 (tok : Nat) : Nat := (if Nat.blt tok 820 then (if Nat.blt tok 796 then (if Nat.blt tok 42 then (if Nat.blt tok 41 then (if tok == 40 then 2 else 0) else (if tok == 41 then 390238150981 else 0)) else (if Nat.blt tok 49 then (if tok == 42 then 350150394051 else 0) else (if tok == 49 then 390238150983 else 0))) else (if Nat.blt tok 798 then (if Nat.blt tok 797 then (if tok == 796 then 10 else 0) else (if tok == 797 then 112213819521 else 0)) else (if Nat.blt tok 806 then (if tok == 798 then 113225607495 else 0) else (if tok == 806 then 112012492929 else 0)))) else (if Nat.blt tok 1589 then (if Nat.blt tok 822 then (if Nat.blt tok 821 then (if tok == 820 then 12 else 0) else (if tok == 821 then 112012492929 else 0)) else (if Nat.blt tok 834 then (if tok == 822 then 112012492865 else 0) else (if tok == 834 then 112012492865 else 0))) else (if Nat.blt tok 3137 then (if Nat.blt tok 3136 then (if tok == 1589 then 113225607495 else 0) else (if tok == 3136 then 14 else 0)) else (if Nat.blt tok 3138 then (if tok == 3137 then 112011509889 else 0) else (if tok == 3138 then 112012492929 else 0)))))
def advice1 (tok : Nat) : Nat := (if Nat.blt tok 42 then (if Nat.blt tok 26 then (if Nat.blt tok 17 then (if tok == 16 then 4 else 0) else (if Nat.blt tok 18 then (if tok == 17 then 594963529859 else 0) else (if tok == 18 then 113225607429 else 0))) else (if Nat.blt tok 40 then (if tok == 26 then 388805099651 else 0) else (if Nat.blt tok 41 then (if tok == 40 then 6 else 0) else (if tok == 41 then 388805099651 else 0)))) else (if Nat.blt tok 1573 then (if Nat.blt tok 54 then (if tok == 42 then 388805099585 else 0) else (if Nat.blt tok 809 then (if tok == 54 then 388805099585 else 0) else (if tok == 809 then 113225607429 else 0))) else (if Nat.blt tok 2357 then (if Nat.blt tok 2356 then (if tok == 1573 then 388805099717 else 0) else (if tok == 2356 then 8 else 0)) else (if Nat.blt tok 2358 then (if tok == 2357 then 388804116611 else 0) else (if tok == 2358 then 388805099651 else 0)))))
def advice2 (tok : Nat) : Nat := (if Nat.blt tok 793 then (if tok == 29 then 113225607363 else 0) else (if Nat.blt tok 1578 then (if tok == 793 then 594963529859 else 0) else (if tok == 1578 then 594963529793 else 0)))
def advice3 (tok : Nat) : Nat := (if Nat.blt tok 793 then (if tok == 29 then 113225607363 else 0) else (if Nat.blt tok 1578 then (if tok == 793 then 388805099651 else 0) else (if tok == 1578 then 388805099585 else 0)))
def advice4 (tok : Nat) : Nat := (if Nat.blt tok 26 then (if tok == 18 then 113225570501 else 0) else (if Nat.blt tok 42 then (if tok == 26 then 388804116611 else 0) else (if tok == 42 then 388804116545 else 0)))
def advice5 (tok : Nat) : Nat := (if Nat.blt tok 37 then (if Nat.blt tok 29 then (if tok == 28 then 4 else 0) else (if Nat.blt tok 30 then (if tok == 29 then 594963542147 else 0) else (if tok == 30 then 556308824193 else 0))) else (if Nat.blt tok 809 then (if tok == 37 then 594963542213 else 0) else (if Nat.blt tok 2358 then (if tok == 809 then 113225607429 else 0) else (if tok == 2358 then 112213819457 else 0))))
def advice6 (tok : Nat) : Nat := (if Nat.blt tok 30 then (if Nat.blt tok 29 then (if tok == 28 then 6 else 0) else (if tok == 29 then 390238150915 else 0)) else (if Nat.blt tok 809 then (if tok == 30 then 350150393985 else 0) else (if Nat.blt tok 2358 then (if tok == 809 then 113225607429 else 0) else (if tok == 2358 then 112012492865 else 0))))
def advice7 (tok : Nat) : Nat := (if Nat.blt tok 798 then (if Nat.blt tok 41 then (if tok == 40 then 8 else 0) else (if Nat.blt tok 42 then (if tok == 41 then 390238150917 else 0) else (if tok == 42 then 350149411011 else 0))) else (if Nat.blt tok 806 then (if tok == 798 then 113212987649 else 0) else (if Nat.blt tok 822 then (if tok == 806 then 112011509889 else 0) else (if tok == 822 then 112011509825 else 0))))
def advice (i tok : Nat) : Nat := match i with
  | 0 => advice0 tok
  | 1 => advice1 tok
  | 2 => advice2 tok
  | 3 => advice3 tok
  | 4 => advice4 tok
  | 5 => advice5 tok
  | 6 => advice6 tok
  | 7 => advice7 tok
  | _ => 0
def links : DagLinks := fun i tok =>
  let a := advice i tok
  if a % 2 = 0 then some (a / 2, 0) else none
def cuts : EdgeCut := fun i tok s => rectangleReject minorGoal s (advice i tok / 2)
def check := scan minorMask minorGoal negatives states rows.size #[] links cuts

-- Links carry the destination index. A rectangle witness names two conflicting mandatory rectangles.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked : treeBlock 0 rows.size check = true := by decide +kernel

theorem minorLower : AOLower minorMask minorStock minorGoal 7 := by
  apply lowerStock (root := 0) (fuel := 6) (width := 25)
    (row := (6,minorStock,[])) (moves := #[]) (links := links) (cut := cuts)
    (states := states) (count := rows.size) (neg := negatives)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold properWord
    decide +kernel
  · unfold requiredTests
    decide +kernel
  · unfold Masked
    decide +kernel
  · intro i w hw
    simp at hw
  · decide +kernel
  · intro i tok s h
    exact rectangleOpen _ h
  · intro i hi
    exact treeBlock_at checked (Nat.zero_le _) (by simpa using hi)
  · decide +kernel
  · rfl
  · rfl
  · rfl

theorem lower : ¬ RepSizeAtMost posted 10 := by
  rintro ⟨c,legal,cap,right⟩
  obtain ⟨k,fit,live⟩ := representation_live c legal right
  exact cheapCut_sound (m := minorMask) (goal := T) (low := 7) (fuel := 10)
    (stock := minorStock) (ws := stock) minorLower (by unfold maskedFlat; decide +kernel)
    (by decide +kernel) (fit.trans cap) (by decide +kernel) live
end Plane.Certificate
end PEqualNP.Outside.L_meta_10117

theorem PEqualNP.Outside.L_meta_10117 :
    ¬ (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (8151129 : ℕ).testBit (5 * u.val + v.val)) 10) :=
  PEqualNP.Outside.L_meta_10117.Plane.Certificate.lower
