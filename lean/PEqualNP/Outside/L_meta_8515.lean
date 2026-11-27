import Mathlib
import PEqualNP.Defs

-- The lowerDag verifier engine is adapted from lean/PEqualNP/Outside/L_meta_8503.lean
-- in this repository, with the namespace renamed; the subproblem DAG and certificates
-- for L-meta-8515 are new.

namespace PEqualNP.Outside.L_meta_8515

abbrev Forest := Nat → Nat × Nat

def unpack (packed width index : Nat) : Nat :=
  (packed >>> (width * index)) &&& ((1 <<< width) - 1)

def decodeNode (parentWidth width packed index : Nat) : Nat × Nat :=
  let entry := unpack packed width index
  (entry &&& ((1 <<< parentWidth) - 1), entry >>> parentWidth)

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
abbrev CutCheck := RowState → Bool

def rootWords (base : List Word) (token : Nat) : List Word :=
  List.rec (motive := fun _ => Nat → List Word) (fun _ => [])
    (fun word _ next bits =>
      let tail := next (bits >>> 1)
      if bits &&& 1 == 0 then tail else word :: tail) base token

def rootState (base : List Word) (fuel token : Nat) : RowState :=
  (fuel, rootWords base token, [])

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

abbrev Bound := Nat × List Word × Nat × Word

def stockWord (mask : Nat) (stock : List Word) (needed : List Word) (word : Word) : List Word :=
  let v := word &&& mask
  if v == 0 || v == mask || stock.contains v || needed.contains v then needed
  else v :: needed

def recipeStart (mask : Nat) (stock words : List Word) : List Word :=
  (List.rec (motive := fun _ => List Word → List Word) id
    (fun word _ next seen => next (stockWord mask stock seen word)) words) []

def recipeClosure (mask : Nat) (stock : List Word) (history : List (Word × Word × Word))
    (start : List Word) : List Word :=
  List.rec (motive := fun _ => List Word → List Word) id
    (fun (out, a, b) _ next seen =>
      next (if seen.contains (out &&& mask) then stockWord mask stock (stockWord mask stock seen a) b else seen))
    history start

def recipeNeeded (mask : Nat) (stock words : List Word) (history : List (Word × Word × Word)) :
    List Word :=
  recipeClosure mask stock history (recipeStart mask stock words)

def maskFlat (mask word : Nat) : Bool :=
  let v := word &&& mask
  v == 0 || v == mask

def flatCount (mask : Nat) (words : List Word) : Nat :=
  List.rec 0 (fun word _ count => if maskFlat mask word then count + 1 else count) words

def availableB (mask : Nat) (bank : List Word) (w : Word) : Bool :=
  w == 0 || w == mask || bank.contains w

def recipeGate (mask : Nat) (bank : List Word) (w a b : Word) : Bool :=
  availableB mask bank a &&
    ((w == mask ^^^ a) || (availableB mask bank b && (w == a &&& b || w == a ||| b)))

def replayRecipes (mask : Nat) (needed : List Word) (recipes : List (Word × Word × Word))
    (bank : List Word) : List Word :=
  List.rec (motive := fun _ => List Word → List Word) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := w &&& mask
      if needed.contains v && !availableB mask bank v &&
          recipeGate mask bank v (a &&& mask) (b &&& mask) then
        v :: next (v :: bank)
      else next bank) recipes bank

def boundCloses (target : Word) (state : RowState) (bound : Bound) : Bool :=
  let (mask, stock, lower, goal) := bound
  let (fuel, ws, history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    (let remaining := fuel - flatCount mask ws
     if remaining < lower then
       let start := recipeStart mask stock ws
       if start.length + remaining < lower then
         let needed := recipeClosure mask stock history start
         if needed.length + remaining < lower then
           let replay := replayRecipes mask needed history.reverse stock
           (replay.length + remaining < lower) &&
             ws.all (fun w => availableB mask (replay ++ stock) (w &&& mask))
         else false
       else false
     else false)

def knownCloses (target : Word) (bounds : List Bound) (state : RowState) : Bool :=
  List.rec false (fun bound _ later => boundCloses target state bound || later) bounds

def AvailableWord (mask : Nat) (bank : List Word) (word : Word) : Prop :=
  word = 0 ∨ word = mask ∨ word ∈ bank

def GateWord (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  (∃ a, AvailableWord mask bank a ∧ out = mask ^^^ a) ∨
  (∃ a b, AvailableWord mask bank a ∧ AvailableWord mask bank b ∧
    (out = a &&& b ∨ out = a ||| b))

def WordBuilds (mask : Nat) (roots : List Word) : List Word → Prop
  | [] => True
  | w :: ws => GateWord mask roots w ∧ WordBuilds mask (w :: roots) ws

def Lower (mask : Nat) (roots : List Word) (target : Word) (minimum : Nat) : Prop :=
  ∀ values, WordBuilds mask roots values →
    AvailableWord mask (values ++ roots) target → minimum ≤ values.length

def Known (bounds : List Bound) : Prop :=
  ∀ bound ∈ bounds, Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1

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

theorem projectBuilds {mask cut : Nat} (submask : mask &&& cut = cut)
    {roots values : List Word} (builds : WordBuilds mask roots values) :
    WordBuilds cut (roots.map (· &&& cut)) (values.map (· &&& cut)) := by
  induction values generalizing roots with
  | nil => trivial
  | cons w ws ih =>
    exact ⟨projectGate submask builds.1, ih builds.2⟩

theorem availableWeaken {mask : Nat} {small big : List Word} {w : Word}
    (sub : ∀ x ∈ small, AvailableWord mask big x)
    (av : AvailableWord mask small w) : AvailableWord mask big w := by
  rcases av with rfl | rfl | h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact sub w h

theorem gateWeaken {mask : Nat} {small big : List Word} {out : Word}
    (sub : ∀ x ∈ small, AvailableWord mask big x)
    (gate : GateWord mask small out) : GateWord mask big out := by
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq⟩
  · exact Or.inl ⟨a, availableWeaken sub ha, rfl⟩
  · exact Or.inr ⟨a, b, availableWeaken sub ha, availableWeaken sub hb, eq⟩

theorem extendKnown {bound : Bound} {bounds : List Bound}
    (old : Known bounds)
    (new : Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1) :
    Known (bound :: bounds) := by
  intro x h
  rcases List.mem_cons.mp h with rfl | h
  · exact new
  · exact old _ h

def AgreesAt (i j : Nat) (word : Word) : Prop :=
  word.testBit i = word.testBit j

theorem agreesAvailable {i j mask : Nat} {bank : List Word} {word : Word}
    (m : AgreesAt i j mask) (all : ∀ w ∈ bank, AgreesAt i j w)
    (av : AvailableWord mask bank word) : AgreesAt i j word := by
  rcases av with rfl | rfl | h
  · simp [AgreesAt]
  · exact m
  · exact all _ h

theorem agreesGate {i j mask : Nat} {bank : List Word} {word : Word}
    (m : AgreesAt i j mask) (all : ∀ w ∈ bank, AgreesAt i j w)
    (gate : GateWord mask bank word) : AgreesAt i j word := by
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq | eq⟩
  · simp only [AgreesAt, Nat.testBit_xor] at m ⊢
    rw [m, show a.testBit i = a.testBit j from agreesAvailable m all ha]
  · subst word
    simp only [AgreesAt, Nat.testBit_and]
    rw [show a.testBit i = a.testBit j from agreesAvailable m all ha,
      show b.testBit i = b.testBit j from agreesAvailable m all hb]
  · subst word
    simp only [AgreesAt, Nat.testBit_or]
    rw [show a.testBit i = a.testBit j from agreesAvailable m all ha,
      show b.testBit i = b.testBit j from agreesAvailable m all hb]

theorem agreesBuilds {i j mask : Nat} {roots values : List Word} {word : Word}
    (m : AgreesAt i j mask) (all : ∀ w ∈ roots, AgreesAt i j w)
    (builds : WordBuilds mask roots values)
    (av : AvailableWord mask (values ++ roots) word) : AgreesAt i j word := by
  induction values generalizing roots with
  | nil => exact agreesAvailable m all av
  | cons v vs ih =>
    have vg := agreesGate m all builds.1
    have hc : ∀ w ∈ v :: roots, AgreesAt i j w := by
      intro w h
      rcases List.mem_cons.mp h with rfl | mem
      · exact vg
      · exact all _ mem
    apply ih hc builds.2
    rcases av with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by
        simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using h))

theorem buildsMap {m n : Nat} (f : Word → Word)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a, f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b, f (a &&& b) = f a &&& f b)
    (join : ∀ a b, f (a ||| b) = f a ||| f b)
    {roots : List Word} {bank : List Word}
    (supply : ∀ v ∈ roots, AvailableWord n bank (f v))
    {values : List Word} (h : WordBuilds m roots values) :
    WordBuilds n bank (values.map f) := by
  have av {bank roots : List Word} {v : Word}
      (src : ∀ v ∈ roots, AvailableWord n bank (f v))
      (h : AvailableWord m roots v) : AvailableWord n bank (f v) := by
    rcases h with rfl | rfl | hv
    · exact Or.inl zero
    · exact Or.inr (Or.inl ones)
    · exact src _ hv
  induction values generalizing roots bank with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨?_, ih ?_ h.2⟩
    · rcases h.1 with ⟨a, ha, eq⟩ | ⟨a, b, ha, hb, eq | eq⟩
      · exact Or.inl ⟨f a, av supply ha, eq ▸ invert a⟩
      · exact Or.inr ⟨f a, f b, av supply ha, av supply hb, Or.inl (eq ▸ meet a b)⟩
      · exact Or.inr ⟨f a, f b, av supply ha, av supply hb, Or.inr (eq ▸ join a b)⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Or.inr (Or.inr List.mem_cons_self)
      · exact availableWeaken (fun x hx => Or.inr (Or.inr (List.mem_cons_of_mem _ hx))) (supply _ hw)

theorem lowerMap {m n : Nat} (f : Word → Word)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a, f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b, f (a &&& b) = f a &&& f b)
    (join : ∀ a b, f (a ||| b) = f a ||| f b)
    {roots bank : List Word} {goal : Word} {minimum : Nat}
    (supply : ∀ v ∈ roots, AvailableWord n bank (f v))
    (bound : Lower n bank (f goal) minimum) :
    Lower m roots goal minimum := by
  intro values build hit
  suffices AvailableWord n (values.map f ++ bank) (f goal) by
    simpa using bound (values.map f) (buildsMap f zero ones invert meet join supply build) this
  rcases hit with rfl | rfl | mem
  · exact Or.inl zero
  · exact Or.inr (Or.inl ones)
  · rcases List.mem_append.mp mem with hv | hr
    · exact Or.inr (Or.inr (List.mem_append_left _ (List.mem_map_of_mem hv)))
    · exact availableWeaken (fun w hw => Or.inr (Or.inr (List.mem_append_right _ hw))) (supply _ hr)

theorem buildsWeaken {mask : Nat} {small big values : List Word}
    (supply : ∀ w ∈ small, AvailableWord mask big w) (build : WordBuilds mask small values) :
    WordBuilds mask big values := by
  induction values generalizing small big with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gateWeaken supply build.1, ih ?_ build.2⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inr (Or.inr List.mem_cons_self)
    · exact availableWeaken (fun x hx => Or.inr (Or.inr (List.mem_cons_of_mem _ hx))) (supply _ hw)

theorem gateBuildsIndex {mask : Nat} (bank values : List Word)
    (legal : ∀ i, i < values.length →
      GateWord mask (bank ++ values.take i) (values.getD i 0)) :
    WordBuilds mask bank values := by
  induction values generalizing bank with
  | nil => trivial
  | cons v vs ih =>
    have first := legal 0 (by simp)
    have tail : ∀ i, i < vs.length →
        GateWord mask ((bank ++ [v]) ++ vs.take i) (vs.getD i 0) := by
      intro i hi
      simpa [List.take_succ_cons, List.append_assoc] using
        legal (i + 1) (by simpa using hi)
    refine ⟨by simpa using first, buildsWeaken ?_ (ih (bank ++ [v]) tail)⟩
    intro w mem
    exact Or.inr (Or.inr (by simpa [or_comm] using mem))

theorem lowerWeaken {mask goal minimum : Nat} {old new : List Word}
    (lower : Lower mask old goal minimum) (supply : ∀ w ∈ new, AvailableWord mask old w) :
    Lower mask new goal minimum := by
  apply lowerMap id rfl rfl (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) supply
  exact lower

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

def wordWitness (mask : Nat) (ws : List Word) (w : Word) : Prop :=
  (∃ a ∈ ws, properWord mask a ∧ w = mask ^^^ a) ∨
  ∃ d a b, a ∈ ws ∧ b ∈ ws ∧ properWord mask a ∧ properWord mask b ∧
    a ≠ b ∧ w = binWord d a b

theorem pullWord {w : List (Word)} {z : Word} {k t S} (h : LiveWord mask target k t S)
    (hz : wordRep mask w z ∨ wordWitness mask w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ LiveWord mask target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := liveWordProper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase ((mask ^^^ a))
        have ht : LiveWord mask target k t (insert ((mask ^^^ a)) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : (mask ^^^ a) ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,LiveWord.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (binWord d a b)
        have ht : LiveWord mask target k t (insert (binWord d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,_,Nat.le_refl _,LiveWord.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha



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

theorem classifyWord {bank : List Word} {out : Word}
    (all : ∀ w ∈ bank, Masked mask w) (gate : GateWord mask bank out) :
    wordRep mask bank out ∨ wordWitness mask bank out := by
  have c0 : wordRep mask bank 0 := Or.inr fun h => h.1 rfl
  have cm : wordRep mask bank mask := Or.inr fun h => h.2 rfl
  have classify {w : Word} (hw : AvailableWord mask bank w) :
      w = 0 ∨ w = mask ∨ w ∈ bank ∧ properWord mask w := by
    by_cases zh : w = 0
    · exact Or.inl zh
    by_cases mh : w = mask
    · exact Or.inr (Or.inl mh)
    exact Or.inr (Or.inr ⟨(hw.resolve_left zh).resolve_left mh, zh, mh⟩)
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, h | h⟩
  · rcases classify ha with rfl | hma | ⟨hm, hp⟩
    · exact Or.inl (by simpa using cm)
    · exact Or.inl (by simpa [hma] using c0)
    · exact Or.inr (Or.inl ⟨a, hm, hp, rfl⟩)
  · subst out; exact (classifyBinary all false ha hb).imp id Or.inr
  · subst out; exact (classifyBinary all true ha hb).imp id Or.inr

theorem extractWordLive {roots values : List Word}
    (all : ∀ w ∈ roots, Masked mask w) (builds : WordBuilds mask roots values)
    (hit : AvailableWord mask (values ++ roots) target) (p : properWord mask target) :
    ∃ k t S, k ≤ values.length ∧ LiveWord mask target k t S ∧ ∀ w ∈ S, w ∈ roots := by
  have hm := (hit.resolve_left p.1).resolve_left p.2
  induction values generalizing roots with
  | nil =>
    exact ⟨0, 0, {target}, Nat.zero_le _, LiveWord.stop p, by simpa using hm⟩
  | cons w ws ih =>
    have next : ∀ v ∈ w :: roots, Masked mask v := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact maskedGate all builds.1
      · exact all _ hv
    have ht : AvailableWord mask (ws ++ w :: roots) target := by
      exact Or.inr (Or.inr (by simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hm))
    obtain ⟨k, t, S, hk, live, sub⟩ :=
      ih next builds.2 ht ((ht.resolve_left p.1).resolve_left p.2)
    have available : ∀ v ∈ S, v ∈ roots ++ [w] := by
      intro v h
      simpa [or_comm] using sub v h
    obtain ⟨k', t', S', hk', hl, hsub⟩ := pullWord live (classifyWord all builds.1) available
    exact ⟨k', t', S', by simp only [List.length_cons]; omega, hl, hsub⟩

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

theorem unaryChild {mask fuel a : Nat} {ws : List Word}
    {history : List (Word × Word × Word)} {x : Word} {keep : Nat}
    (ha : a < ws.length) (ha64 : a < 64) (hf : fuel ≠ 0) (hk : keep < 2)
    (hx : ws.getD a 0 = x) (p : properWord mask (mask ^^^ x)) (fresh : mask ^^^ x ∉ ws) :
    childState mask (gateToken a a 2 keep) (fuel, ws, history) =
      some (fuel - 1, insertWord (mask ^^^ x) (keepWord (keep.testBit 0) x ws),
        (mask ^^^ x, x, x) :: history) := by
  obtain ⟨ke, op, aa, bb⟩ := gateTokenFields (a := a) ha64 (by decide : 2 < 3) (by omega : keep < 4)
  simp only [childState, ke, op, aa, bb, hx]
  simp [hf, Nat.not_le_of_lt ha, Nat.not_le_of_lt hk, p.1, p.2, fresh, keepWord]

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

def WordViable (mask : Nat) (target : Word) (state : RowState) : Prop :=
  state.2.1.Nodup ∧ ∃ k t, k ≤ state.1 ∧ LiveWord mask target k t state.2.1.toFinset

def HasChild (mask : Nat) (state child : RowState) : Prop :=
  ∃ a b op keep, a < state.2.1.length ∧
    ((a = b ∧ op = 2 ∧ keep < 2) ∨
      (a < b ∧ b < state.2.1.length ∧ op < 2 ∧ keep < 4)) ∧
    childState mask (gateToken a b op keep) state = some child

theorem unaryProgress {mask fuel k t : Nat} {x target : Word} {U : Finset Word} {ws : List Word}
    {history : List (Word × Word × Word)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel)
    (he : ws.toFinset = insert x U) (fresh : mask ^^^ x ∉ insert x U)
    (tail : LiveWord mask target k t (insert (mask ^^^ x) U)) :
    ∃ child, HasChild mask (fuel, ws, history) child ∧ WordViable mask target child := by
  let a := ws.idxOf x
  have xm : x ∈ ws := by
    rw [← List.mem_toFinset, he]
    simp
  have ha : a < ws.length := List.idxOf_lt_length_iff.mpr xm
  have hx : ws.getD a 0 = x := getWord xm
  have p := liveWordProper tail (mask ^^^ x) (Finset.mem_insert_self _ _)
  let save := decide (x ∈ U)
  let keep := if save then 1 else 0
  have keepLt : keep < 2 := by dsimp [keep]; split <;> decide
  have keepBit : keep.testBit 0 = save := by
    unfold keep
    cases save <;> decide
  have fn : mask ^^^ x ∉ ws := by simpa [← List.mem_toFinset, he] using fresh
  let rest := keepWord save x ws
  let child : RowState := (fuel - 1, insertWord (mask ^^^ x) rest, (mask ^^^ x, x, x) :: history)
  refine ⟨child, ⟨a, a, 2, keep, ha, Or.inl ⟨rfl, rfl, keepLt⟩, ?_⟩, ?_⟩
  · have eq := unaryChild (fuel := fuel) (history := history) ha (by omega) (by omega) keepLt hx p fn
    rw [keepBit] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup nd save x) (fun h => fn (keepSubset save x ws _ h)),
      k, t, by change k ≤ fuel - 1; omega, ?_⟩
    change LiveWord mask target k t (insertWord (mask ^^^ x) rest).toFinset
    rw [insertWordSet, keepSet nd he]
    exact tail

theorem binaryProgress {mask fuel k t : Nat} {x y target : Word} {d : Bool} {U : Finset Word}
    {ws : List Word} {history : List (Word × Word × Word)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel)
    (he : ws.toFinset = insert x (insert y U)) (xy : x ≠ y)
    (ordered : ws.idxOf x < ws.idxOf y) (fresh : binWord d x y ∉ insert x (insert y U))
    (tail : LiveWord mask target k t (insert (binWord d x y) U)) :
    ∃ child, HasChild mask (fuel, ws, history) child ∧ WordViable mask target child := by
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
  refine ⟨child, ⟨a, b, if d then 1 else 0, keep, ha, Or.inr ⟨hab, hb, ?_, keepLt⟩, ?_⟩, ?_⟩
  · cases d <;> decide
  · have eq := binaryChild (fuel := fuel) (history := history) d hab hb (by omega) (by omega) keepLt hx hy p fn
    rw [bx, by'] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup (keepNodup nd saveX x) saveY y)
      (fun h => fn (keepSubset saveX x ws _ (keepSubset saveY y _ _ h))), k, t, by change k ≤ fuel - 1; omega, ?_⟩
    change LiveWord mask target k t (insertWord v rest).toFinset
    rw [insertWordSet, keepPairSet nd xy he]
    exact tail

theorem wordProgress {mask : Nat} {target : Word} {state : RowState}
    (width : state.2.1.length ≤ 64) (h : WordViable mask target state) :
    target ∈ state.2.1 ∨ ∃ child, HasChild mask state child ∧ WordViable mask target child := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨nd, k, t, cap, live⟩ := h
  cases k with
  | zero =>
    obtain ⟨_, eq, _⟩ := live
    left
    change ws.toFinset = {target} at eq
    rw [← List.mem_toFinset, eq]
    simp
  | succ k =>
    right
    rcases live with ⟨u,U,x,_,eq,px,fresh,tail⟩ | ⟨U,x,y,d,eq,px,py,xy,fresh,tail⟩
    · exact unaryProgress nd width cap eq fresh tail
    have xm : x ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have ym : y ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have diff : ws.idxOf x ≠ ws.idxOf y := by
      intro same
      apply xy
      rw [← getWord xm, same, getWord ym]
    by_cases h : ws.idxOf x < ws.idxOf y
    · exact binaryProgress nd width cap eq xy h fresh tail
    · have eq' : ws.toFinset = insert y (insert x U) := by rw [eq, Finset.insert_comm]
      have fresh' : binWord d y x ∉ insert y (insert x U) := by
        rw [binWord_comm d y x, Finset.insert_comm]; exact fresh
      have tail' : LiveWord mask target k t (insert (binWord d y x) U) := by
        rw [binWord_comm d y x]; exact tail
      exact binaryProgress nd width cap eq' xy.symm (by omega) fresh' tail'

theorem rootWordSublist (base : List Word) (token : Nat) : (rootWords base token).Sublist base := by
  induction base generalizing token with
  | nil => exact List.Sublist.slnil
  | cons w ws ih =>
    change (if token &&& 1 == 0 then rootWords ws (token >>> 1)
      else w :: rootWords ws (token >>> 1)).Sublist (w :: ws)
    split
    · exact (ih _).cons _
    · exact (ih _).cons₂ _

theorem rootToken (base : List Word) (S : Finset Word) :
    ∃ token < 2 ^ base.length, (rootWords base token).toFinset = base.toFinset ∩ S := by
  induction base with
  | nil => exact ⟨0, by simp, by simp [rootWords]⟩
  | cons w ws ih =>
    obtain ⟨token, htoken, ih⟩ := ih
    let bit : Nat := if w ∈ S then 1 else 0
    have hbit : bit < 2 := by dsimp [bit]; split <;> decide
    let code := 2 * token + bit
    have low : code &&& 1 = bit := by
      rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      dsimp [code]
      omega
    have high : code >>> 1 = token := by
      rw [Nat.shiftRight_eq_div_pow]
      change code / 2 = token
      dsimp [code]
      omega
    refine ⟨code, ?_, ?_⟩
    · simp only [List.length_cons, pow_succ]
      dsimp [code]
      omega
    · change (if code &&& 1 == 0 then rootWords ws (code >>> 1)
        else w :: rootWords ws (code >>> 1)).toFinset = _
      rw [low, high]
      by_cases hw : w ∈ S
      · simp [bit, hw, ih]
      · simp [bit, hw, ih]

theorem liveAgrees {i j k t : Nat} {S : Finset Word}
    (h : LiveWord mask target k t S) (m : AgreesAt i j mask)
    (all : ∀ w ∈ S, AgreesAt i j w) : AgreesAt i j target := by
  induction h using LiveWord.ind with
  | stop => exact all _ (Finset.mem_singleton_self _)
  | @unary k t U a pa fresh tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp only [AgreesAt, Nat.testBit_xor]
      rw [show mask.testBit i = mask.testBit j from m,
        show a.testBit i = a.testBit j from all a (Finset.mem_insert_self _ _)]
    · exact all _ (Finset.mem_insert_of_mem hw)
  | @binary k t U a b d pa pb ab fresh tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have aa : a.testBit i = a.testBit j := all a (Finset.mem_insert_self _ _)
      have bb : b.testBit i = b.testBit j := all b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      cases d <;> simp [AgreesAt, binWord, Nat.testBit_and, Nat.testBit_or, aa, bb]
    · exact all _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))

theorem positiveInMask {i : Nat} (mt : Masked mask target) (ht : target.testBit i = true) :
    mask.testBit i = true := by
  have h := congrArg (fun n : Nat => n.testBit i) mt
  simpa [Nat.testBit_and, ht] using h

variable {rows : Nat}

def fullMask (rows : Nat) : Nat := 2 ^ rows - 1

theorem toNatMasked (v : BitVec rows) : Masked (fullMask rows) v.toNat := by
  unfold Masked fullMask
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt v.isLt]

theorem notNat (v : BitVec rows) : (~~~v).toNat = fullMask rows ^^^ v.toNat := by
  rw [← BitVec.xor_allOnes, BitVec.toNat_xor, Nat.xor_comm, BitVec.toNat_allOnes]
  rfl

theorem gateOfAvailable {bank : List Word} {w : Word}
    (av : AvailableWord mask bank w) : GateWord mask bank w :=
  Or.inr ⟨w, 0, av, Or.inl rfl, Or.inr (by simp)⟩

theorem toNatAvailable (bank : List (BitVec rows)) (i : Nat) :
    AvailableWord (fullMask rows) (bank.map BitVec.toNat) (bank.getD i 0).toNat := by
  rw [List.getD_eq_getElem?_getD]
  cases h : bank[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (Or.inr (List.mem_map_of_mem (List.mem_of_getElem? h)))

def buildable (m g : Word) : Nat → Finset (Word) → Prop
  | 0, s => g ∈ s
  | n+1, s => buildable m g n s ∨
    (∃ a ∈ s, buildable m g n (insert (m ^^^ a) s)) ∨
    (∃ a ∈ s, ∃ b ∈ s, ∃ d, buildable m g n (insert (binWord d a b) s))

theorem supplyPool {m g : Word} {n s q} (sub : s ⊆ q) (h : buildable m g n s) : buildable m g n q := by
  induction n generalizing s q with
  | zero => exact sub h
  | succ n ih =>
    rcases h with h | ⟨a,ha,h⟩ | ⟨a,ha,b,hb,d,h⟩
    · exact Or.inl (ih sub h)
    · exact Or.inr (Or.inl ⟨a,sub ha,ih (Finset.insert_subset_insert _ sub) h⟩)
    · exact Or.inr (Or.inr ⟨a,sub ha,b,sub hb,d,ih (Finset.insert_subset_insert _ sub) h⟩)

theorem supplyMore {m g : Word} {n l s} (le : n ≤ l) (h : buildable m g n s) : buildable m g l s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

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

theorem cofNot {mask m : Nat} (sub : mask &&& m = m) (a : Word) :
    (mask ^^^ a) &&& m = m ^^^ (a &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h := congrArg (fun w : Nat => w.testBit i) sub
  simp only [Nat.testBit_and, Nat.testBit_xor] at h ⊢
  cases he : m.testBit i
  · simp
  · have hm : mask.testBit i = true := by simpa [he] using h
    simp [hm]

theorem cofBinary (m a b : Word) (d : Bool) :
    binWord d a b &&& m = binWord d (a &&& m) (b &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases d <;> simp only [binWord, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and, Nat.testBit_or] <;>
    cases m.testBit i <;> simp

theorem flNot {mask m : Nat} (sub : mask &&& m = m) (a : Word) :
    maskedFlat m (mask ^^^ a) ↔ maskedFlat m a := by
  unfold maskedFlat
  rw [cofNot sub]
  constructor <;> intro h
  · rcases h with h | h
    · right
      have hh := congrArg (fun v => m ^^^ v) h
      simpa [← Nat.xor_assoc] using hh
    · left
      have hh := congrArg (fun v => m ^^^ v) h
      simpa [← Nat.xor_assoc] using hh
  · rcases h with h | h <;> simp [h]

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

theorem maskedBuild {goal : Word} {k t s} (run : LiveWord mask goal k t s) (m : Word) (submask : mask &&& m = m) (properGoal : ¬ maskedFlat m goal) :
    ∃ n, n+(flatSet m s).card ≤ k ∧ buildable m (goal &&& m) n (projectedStock m s) := by
  induction run using LiveWord.ind with
  | stop =>
    refine ⟨0,?_,?_⟩
    · simp only [flatSet, Finset.filter_singleton, properGoal, ite_false, Finset.card_empty,
        Nat.add_zero, Nat.le_refl]
    · change goal &&& m ∈ projectedStock m {goal}
      simp [projectedStock,visibleWords]
  | @unary k t u a pa fresh tail ih =>
    obtain ⟨n,cap,built⟩ := ih
    have nn : (mask ^^^ a) ∉ u := fun h => fresh (Finset.mem_insert_of_mem h)
    rw [flIns nn] at cap
    have card := flLe m a u
    have old : a &&& m ∈ projectedStock m (insert a u) := by simp [projectedStock,prIns]
    have sub : projectedStock m u ⊆ projectedStock m (insert a u) := by
      exact Finset.insert_subset_insert _ (Finset.insert_subset_insert _ (Finset.image_subset_image (Finset.subset_insert ..)))
    by_cases f : maskedFlat m a
    · have ff := (flNot submask a).mpr f
      simp only [f,ff,ite_true] at cap card
      refine ⟨n,by omega,supplyPool ?_ built⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rcases hw with rfl|rfl|rfl|h
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · rcases ff with e|e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inr h))
    · have nf := mt (flNot submask a).mp f
      simp only [f,nf,ite_false] at cap card
      refine ⟨n+1,by omega,Or.inr (Or.inl ⟨_,old,supplyPool ?_ built⟩)⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rw [cofNot submask] at hw
      tauto
  | @binary k t u a b d pa pb ab fresh tail ih =>
    let v := binWord d a b
    obtain ⟨n,cap,built⟩ := ih
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
      refine ⟨n,budget,supplyPool ?_ built⟩
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
      refine ⟨n+1,by omega,Or.inr (Or.inr ⟨a &&& m,?_,b &&& m,?_,d,supplyPool ?_ built⟩)⟩
      · simp [projectedStock,prIns]
      · simp [projectedStock,prIns]
      · intro w hw
        simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
        rw [cofBinary] at hw
        tauto

theorem availableB_spec {mask : Nat} {bank : List Word} {v : Word} :
    availableB mask bank v = true ↔ AvailableWord mask bank v := by
  simp [availableB, AvailableWord, or_assoc]

theorem recipeGate_spec {mask : Nat} {bank : List Word} {v a b : Word}
    (h : recipeGate mask bank v a b = true) : GateWord mask bank v := by
  simp only [recipeGate, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, availableB_spec] at h
  rcases h with ⟨ha, first | ⟨hb, second⟩⟩
  · exact Or.inl ⟨a, ha, first⟩
  · exact Or.inr ⟨a, b, ha, hb, second⟩

theorem replayRecipesBuilds (mask : Nat) (needed : List Word) (recipes : List (Word × Word × Word))
    (bank : List Word) : WordBuilds mask bank (replayRecipes mask needed recipes bank) := by
  induction recipes generalizing bank with
  | nil => trivial
  | cons recipe recipes ih =>
    obtain ⟨w, a, b⟩ := recipe
    change WordBuilds mask bank
      (if needed.contains (w &&& mask) && !availableB mask bank (w &&& mask) &&
          recipeGate mask bank (w &&& mask) (a &&& mask) (b &&& mask) then
        (w &&& mask) :: replayRecipes mask needed recipes ((w &&& mask) :: bank)
      else replayRecipes mask needed recipes bank)
    split
    · rename_i yes
      exact ⟨recipeGate_spec (Bool.and_eq_true_iff.mp yes).2, ih _⟩
    · exact ih _

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

theorem buildsAppend {mask : Nat} {roots first second : List Word}
    (left : WordBuilds mask roots first)
    (right : WordBuilds mask (first ++ roots) second) :
    WordBuilds mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact right
  | cons w ws ih =>
    refine ⟨left.1, ih left.2 ?_⟩
    have same (bank other vals : List Word) (perm : bank.Perm other)
        (h : WordBuilds mask bank vals) : WordBuilds mask other vals := by
      induction vals generalizing bank other with
      | nil => trivial
      | cons v vs ih =>
        exact ⟨gateWeaken (fun x hx => Or.inr (Or.inr (perm.mem_iff.mp hx))) h.1,
          ih _ _ (perm.cons v) h.2⟩
    exact same _ _ _ (List.perm_middle (a := w) (l₁ := ws) (l₂ := roots)).symm right

theorem buildableWords {mask goal n : Nat} {pool : Finset Word} {bank : List Word}
    (h : buildable mask goal n pool) (supply : ∀ w ∈ pool, AvailableWord mask bank w) :
    ∃ values, values.length ≤ n ∧ WordBuilds mask bank values ∧
      AvailableWord mask (values ++ bank) goal := by
  induction n generalizing pool bank with
  | zero => exact ⟨[], Nat.le_refl _, trivial, supply _ h⟩
  | succ n ih =>
    have add {w : Word} (g : GateWord mask bank w)
        (tail : buildable mask goal n (insert w pool)) :
        ∃ values, values.length ≤ n+1 ∧ WordBuilds mask bank values ∧
          AvailableWord mask (values ++ bank) goal := by
      have growing : ∀ v ∈ insert w pool, AvailableWord mask (w :: bank) v := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Or.inr (Or.inr List.mem_cons_self)
        · exact availableWeaken (fun _ hh => Or.inr (Or.inr (List.mem_cons_of_mem _ hh))) (supply _ hv)
      obtain ⟨values, budget, build, hit⟩ := ih tail growing
      refine ⟨w :: values, by simp only [List.length_cons]; omega, ⟨g, build⟩, ?_⟩
      rcases hit with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by simp only [List.mem_append, List.mem_cons] at *; tauto))
    rcases h with h | ⟨a, ha, h⟩ | ⟨a, ha, b, hb, d, h⟩
    · obtain ⟨values, cap, build, hit⟩ := ih h supply
      exact ⟨values, by omega, build, hit⟩
    · exact add (Or.inl ⟨a, supply a ha, rfl⟩) h
    · apply add (w := binWord d a b) ?_ h
      exact Or.inr ⟨a, b, supply a ha, supply b hb, by cases d <;> simp [binWord]⟩

theorem boundClosesSound {state : RowState} {bound : Bound}
    (known : Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (submask : mask &&& bound.1 = bound.1)
    (viable : WordViable mask target state) :
    boundCloses target state bound = false := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨cut, stock, minimum, goal⟩ := bound
  obtain ⟨nd, k, t, steps, live⟩ := viable
  change k ≤ fuel at steps
  change LiveWord mask target k t ws.toFinset at live
  apply Bool.eq_false_iff.mpr
  intro hc
  let replay := replayRecipes cut (recipeNeeded cut stock ws history) history.reverse stock
  change ((target &&& cut) == goal && goal != 0 && goal != cut &&
    (if fuel - flatCount cut ws < minimum then
      if (recipeStart cut stock ws).length + (fuel - flatCount cut ws) < minimum then
        if (recipeNeeded cut stock ws history).length + (fuel - flatCount cut ws) < minimum then
          (replay.length + (fuel - flatCount cut ws) < minimum) &&
            ws.all (fun w => availableB cut (replay ++ stock) (w &&& cut))
        else false
      else false
    else false)) = true at hc
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hc
  obtain ⟨⟨⟨goalEq, nonzero⟩, nonflat⟩, scan⟩ := hc
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  rcases Bool.and_eq_true_iff.mp scan with ⟨length, sources⟩
  simp only [decide_eq_true_eq] at length
  have pn : ¬maskedFlat cut target := by simpa [maskedFlat, goalEq] using And.intro nonzero nonflat
  obtain ⟨n, hn, build⟩ := maskedBuild live cut submask pn
  rw [← flatCountCard cut nd] at hn
  change n + flatCount cut ws ≤ k at hn
  have supply : ∀ w ∈ projectedStock cut ws.toFinset, AvailableWord cut (replay ++ stock) w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image,
      List.mem_toFinset] at hw
    rcases hw with rfl | rfl | ⟨v, hv, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact availableB_spec.mp (List.all_eq_true.mp sources v hv)
  obtain ⟨ys, hy, built, avail⟩ := buildableWords build supply
  have both := buildsAppend (replayRecipesBuilds cut _ history.reverse stock) built
  have hit : AvailableWord cut ((replay ++ ys) ++ stock) goal := by
    rw [← goalEq]
    exact availableWeaken (fun v hv => Or.inr (Or.inr (by
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using hv))) avail
  have enough := known (replay ++ ys) both hit
  simp only [List.length_append] at enough
  omega

theorem knownClosesSound {bounds : List Bound} {state : RowState}
    (known : Known bounds) (submask : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (viable : WordViable mask target state) :
    knownCloses target bounds state = false := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (boundCloses target state bound || knownCloses target bounds state) = false
    rw [boundClosesSound (known _ List.mem_cons_self) (submask _ List.mem_cons_self) viable]
    exact ih (fun b hb => known b (List.mem_cons_of_mem _ hb))
      (fun b hb => submask b (List.mem_cons_of_mem _ hb))

abbrev PointWire (rows : Nat) := Fin rows → Bool

def encodePoint (f : PointWire rows) : BitVec rows :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem encodeBit (f : PointWire rows) (i : Fin rows) :
    (encodePoint f).getLsbD i.val = f i := by
  simp only [encodePoint, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

theorem encodeNot (f : PointWire rows) : encodePoint (fun j => !f j) = ~~~encodePoint f := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_not, encodeBit f ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
  simp [hi]

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

theorem maskBit {i : Nat} (hi : i < rows) : (fullMask rows).testBit i = true := by
  simp [fullMask, Nat.testBit_two_pow_sub_one, hi]

theorem pointZero : pointWord (fun _ : Fin rows => false) = 0 := by
  have eq : encodePoint (fun _ : Fin rows => false) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i, hi⟩]
    simp
  simp [pointWord, eq]

theorem relabelZero (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex 0 = 0 := by
  simpa [relabel] using (pointZero (rows := rows))

theorem relabelMask (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex (fullMask rows) = fullMask rows := by
  have all : (fun i => (fullMask rows).testBit (sourceIndex i).val) = fun _ => true := by
    funext i
    exact maskBit (sourceIndex i).isLt
  have bits : encodePoint (fun _ : Fin rows => true) = BitVec.allOnes rows := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i, hi⟩]
    simp [hi]
  simp [relabel, all, pointWord, bits, fullMask]

theorem relabelNot (sourceIndex : Fin rows → Fin rows) (a : Word) :
    relabel sourceIndex (fullMask rows ^^^ a) = fullMask rows ^^^ relabel sourceIndex a := by
  have eq : (fun i => (fullMask rows ^^^ a).testBit (sourceIndex i).val) =
      fun i => !a.testBit (sourceIndex i).val := by
    funext i
    simp [Nat.testBit_xor, maskBit (sourceIndex i).isLt]
  simp only [relabel, eq, pointWord, encodeNot, notNat]

theorem relabelAnd (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a &&& b) = relabel sourceIndex a &&& relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_and, pointWord, encodeAnd, BitVec.toNat_and]

theorem relabelOr (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a ||| b) = relabel sourceIndex a ||| relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_or, pointWord, encodeOr, BitVec.toNat_or]

theorem lowerRelabel (sourceIndex : Fin rows → Fin rows) {bank roots : List Word}
    {src dst : Word} {minimum : Nat}
    (old : Lower (fullMask rows) bank src minimum)
    (goal : relabel sourceIndex dst = src)
    (supply : ∀ w ∈ roots, AvailableWord (fullMask rows) bank (relabel sourceIndex w)) :
    Lower (fullMask rows) roots dst minimum := by
  apply lowerMap (relabel sourceIndex) (relabelZero sourceIndex) (relabelMask sourceIndex)
    (relabelNot sourceIndex) (relabelAnd sourceIndex) (relabelOr sourceIndex) supply
  rw [goal]
  exact old

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

theorem lowerRelabelMasked (sourceIndex : Fin rows → Fin rows)
    {oldMask newMask : Nat} {bank roots : List Word} {src dst : Word} {minimum : Nat}
    (old : Lower oldMask bank src minimum)
    (masks : relabel sourceIndex newMask = oldMask)
    (goal : relabel sourceIndex dst = src)
    (supply : ∀ w ∈ roots, AvailableWord oldMask bank (relabel sourceIndex w)) :
    Lower newMask roots dst minimum := by
  apply lowerMap (relabel sourceIndex) (relabelZero sourceIndex) masks
    (fun w => by rw [relabelXor, masks]) (relabelAnd sourceIndex) (relabelOr sourceIndex) supply
  rwa [goal]

theorem extendKnownRelabel (sourceIndex : Fin rows → Fin rows) {bounds : List Bound}
    {source destination : Bound} (old : Known bounds) (mem : source ∈ bounds)
    (budget : destination.2.2.1 = source.2.2.1)
    (masks : relabel sourceIndex destination.1 = source.1)
    (goal : relabel sourceIndex destination.2.2.2 = source.2.2.2)
    (supply : ∀ w ∈ destination.2.1,
      AvailableWord source.1 source.2.1 (relabel sourceIndex w)) :
    Known (destination :: bounds) := by
  apply extendKnown old
  rw [budget]
  exact lowerRelabelMasked sourceIndex (old _ mem) masks goal supply

theorem relabelToNatBound (sourceIndex : Fin rows → Fin rows) (word : Word) :
    Masked (fullMask rows) (relabel sourceIndex word) := toNatMasked _

theorem relabelBit (sourceIndex : Fin rows → Fin rows) (word : Word) (i : Fin rows) :
    (relabel sourceIndex word).testBit i.val = word.testBit (sourceIndex i).val :=
  encodeBit _ i

theorem relabelOutside (sourceIndex : Fin rows → Fin rows) (word i : Word) (h : rows ≤ i) :
    (relabel sourceIndex word).testBit i = false := by
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le (show (encodePoint _).toNat < 2 ^ rows from BitVec.isLt _)
    (Nat.pow_le_pow_right (by decide) h)

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

theorem tb4095 (i : ℕ) : (4095 : ℕ).testBit i = decide (i < 12) := by
  have e : (4095 : ℕ) = 2 ^ 12 - 1 := by norm_num
  rw [e, Nat.testBit_two_pow_sub_one]

def tb (w e : ℕ) : Bool := !(Nat.beq (Nat.land (Nat.shiftRight w e) 1) 0)

theorem tb_eq (w e : ℕ) : tb w e = w.testBit e := by
  have h : Nat.land (Nat.shiftRight w e) 1 = 1 &&& (w >>> e) := Nat.and_comm _ _
  unfold tb Nat.testBit
  rw [h]
  generalize (1 &&& w >>> e) = X
  cases X <;> rfl

def rect (x J : ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 => Nat.lor (cond (tb x e) (Nat.shiftLeft J (Nat.mul 12 e)) 0) (rect x J e)

def rectW (x : ℕ) : ℕ := rect x (Nat.xor (Nat.shiftRight x 12) 4095) 12

theorem rect_tb (x J i : ℕ) (hJ : J.testBit i = true) : ∀ n e : ℕ, e < n → x.testBit e = true →
    (rect x J n).testBit (12 * e + i) = true := by
  intro n
  induction n with
  | zero => intro e he; omega
  | succ n ih =>
    intro e he hx
    show ((cond (tb x n) (J <<< (12 * n)) 0) ||| rect x J n).testBit (12 * e + i) = true
    rw [Nat.testBit_or]
    by_cases hen : e = n
    · subst hen
      rw [tb_eq, hx]
      simp [Nat.testBit_shiftLeft, hJ]
    · rw [ih e (by omega) hx]
      simp

theorem rectW_tb (x e i : ℕ) (he : e < 12) (hi : i < 12) (h1 : x.testBit e = true)
    (h2 : x.testBit (12 + i) = false) : (rectW x).testBit (12 * e + i) = true := by
  apply rect_tb _ _ _ _ 12 e he h1
  show ((x >>> 12) ^^^ 4095).testBit i = true
  rw [Nat.testBit_xor, Nat.testBit_shiftRight, h2, tb4095]
  simp [hi]

def full : ℕ := 22300745198530623141535718272648361505980415

theorem full_eq : full = 2 ^ 144 - 1 := by norm_num [full]

theorem tb_land (a b q : ℕ) : (Nat.land a b).testBit q = (a.testBit q && b.testBit q) :=
  Nat.testBit_and a b q

theorem tb_lor (a b q : ℕ) : (Nat.lor a b).testBit q = (a.testBit q || b.testBit q) :=
  Nat.testBit_or a b q

theorem tb_xor (a b q : ℕ) : (Nat.xor a b).testBit q = Bool.xor (a.testBit q) (b.testBit q) :=
  Nat.testBit_xor a b q

theorem full_tb (q : ℕ) : full.testBit q = decide (q < 144) := by
  rw [full_eq, Nat.testBit_two_pow_sub_one]

theorem land_sub (h a : ℕ) (H : ∀ q, h.testBit q = true → a.testBit q = true) :
    Nat.land h a = h := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [tb_land]
  cases hh : h.testBit q
  · rfl
  · rw [H q hh]; rfl

theorem land_disj (a h : ℕ) (H : ∀ q, a.testBit q = true → h.testBit q = true → False) :
    Nat.land a h = 0 := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [tb_land, Nat.zero_testBit]
  cases ha : a.testBit q
  · rfl
  · cases hh : h.testBit q
    · rfl
    · exact (H q ha hh).elim

def orS (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftRight x s)

def orSL (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftLeft x s)

theorem orS_tb (x s q : ℕ) : (orS x s).testBit q = (x.testBit q || x.testBit (s + q)) := by
  show (x ||| x >>> s).testBit q = _
  rw [Nat.testBit_or, Nat.testBit_shiftRight]

theorem orSL_tb (x s q : ℕ) :
    (orSL x s).testBit q = (x.testBit q || (decide (s ≤ q) && x.testBit (q - s))) := by
  show (x ||| x <<< s).testBit q = _
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, ge_iff_le]

theorem orS_ex (k p x n s : ℕ)
    (hx : ∀ q, x.testBit q = true → ∃ j, j < n ∧ p.testBit (k * j + q) = true) (q : ℕ)
    (h : (orS x (k * s)).testBit q = true) : ∃ j, j < n + s ∧ p.testBit (k * j + q) = true := by
  rw [orS_tb, Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨j, hj, hp⟩ := hx q h
    exact ⟨j, by omega, hp⟩
  · obtain ⟨j, hj, hp⟩ := hx _ h
    refine ⟨j + s, by omega, ?_⟩
    rw [Nat.mul_add, Nat.add_assoc]; exact hp

theorem orSL_ex (k p x n s : ℕ)
    (hx : ∀ q, x.testBit q = true → ∃ j, j < n ∧ k * j ≤ q ∧ p.testBit (q - k * j) = true)
    (q : ℕ) (h : (orSL x (k * s)).testBit q = true) :
    ∃ j, j < n + s ∧ k * j ≤ q ∧ p.testBit (q - k * j) = true := by
  rw [orSL_tb, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨hs, h⟩
  · obtain ⟨j, hj, hq, hp⟩ := hx q h
    exact ⟨j, by omega, hq, hp⟩
  · obtain ⟨j, hj, hq, hp⟩ := hx _ h
    have e : q - k * (j + s) = q - k * s - k * j := by rw [Nat.mul_add]; omega
    refine ⟨j + s, by omega, ?_, ?_⟩
    · rw [Nat.mul_add]; omega
    · rw [e]; exact hp

def rowM : ℕ := 5445847423328601499764522166702896582657

theorem rowM_tb (q : ℕ) (h : rowM.testBit q = true) : q < 144 ∧ q % 12 = 0 := by
  have hlt : q < 144 := by
    by_contra hq
    have h0 : rowM.testBit q = false := by
      apply Nat.testBit_lt_two_pow
      have h1 : rowM < 2 ^ 144 := by norm_num [rowM]
      have h2 : (2 : ℕ) ^ 144 ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [h0] at h
    exact Bool.noConfusion h
  have hall : ∀ q : ℕ, q < 144 → rowM.testBit q = true → q % 12 = 0 := by decide +kernel
  exact ⟨hlt, hall q hlt h⟩

def rowsOf (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 6) 3) 1) 1) rowM

def colsOf (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 96) 48) 24) 12) 4095

def hullC (p : ℕ) : ℕ :=
  Nat.land (orSL (orSL (orSL (orSL (rowsOf p) 6) 3) 1) 1)
    (orSL (orSL (orSL (orSL (colsOf p) 96) 48) 24) 12)

def hull (p : ℕ) : ℕ := hullC (Nat.land p full)

theorem rowsOf_tb (p q : ℕ) (h : (rowsOf p).testBit q = true) :
    (q < 144 ∧ q % 12 = 0) ∧ ∃ j, j < 12 ∧ p.testBit (j + q) = true := by
  unfold rowsOf at h
  rw [tb_land, Bool.and_eq_true] at h
  refine ⟨rowM_tb q h.2, ?_⟩
  have h0 : ∀ q, p.testBit q = true → ∃ j, j < 1 ∧ p.testBit (1 * j + q) = true :=
    fun q hq => ⟨0, by norm_num, by simpa using hq⟩
  have h1 := orS_ex 1 p _ 1 6 h0
  have h2 := orS_ex 1 p _ _ 3 h1
  have h3 := orS_ex 1 p _ _ 1 h2
  have h4 := orS_ex 1 p _ _ 1 h3
  obtain ⟨j, hj, hp⟩ := h4 q h.1
  exact ⟨j, by omega, by simpa using hp⟩

theorem colsOf_tb (p q : ℕ) (h : (colsOf p).testBit q = true) :
    q < 12 ∧ ∃ j, j < 16 ∧ p.testBit (12 * j + q) = true := by
  unfold colsOf at h
  rw [tb_land, Bool.and_eq_true, tb4095, decide_eq_true_eq] at h
  refine ⟨h.2, ?_⟩
  have h0 : ∀ q, p.testBit q = true → ∃ j, j < 1 ∧ p.testBit (12 * j + q) = true :=
    fun q hq => ⟨0, by norm_num, by simpa using hq⟩
  have h1 := orS_ex 12 p _ 1 8 h0
  have h2 := orS_ex 12 p _ _ 4 h1
  have h3 := orS_ex 12 p _ _ 2 h2
  have h4 := orS_ex 12 p _ _ 1 h3
  obtain ⟨j, hj, hp⟩ := h4 q h.1
  exact ⟨j, by omega, hp⟩

theorem hullC_spec (p : ℕ) (hp : ∀ q, p.testBit q = true → q < 144) (q : ℕ)
    (h : (hullC p).testBit q = true) :
    q < 144 ∧ ∃ i e', i < 12 ∧ e' < 12 ∧ p.testBit (12 * (q / 12) + i) = true ∧
      p.testBit (12 * e' + q % 12) = true := by
  unfold hullC at h
  rw [tb_land, Bool.and_eq_true] at h
  obtain ⟨hR, hC⟩ := h
  have r0 : ∀ q, (rowsOf p).testBit q = true →
      ∃ j, j < 1 ∧ 1 * j ≤ q ∧ (rowsOf p).testBit (q - 1 * j) = true :=
    fun q hq => ⟨0, by norm_num, by omega, by simpa using hq⟩
  have r1 := orSL_ex 1 (rowsOf p) _ 1 6 r0
  have r2 := orSL_ex 1 (rowsOf p) _ _ 3 r1
  have r3 := orSL_ex 1 (rowsOf p) _ _ 1 r2
  have r4 := orSL_ex 1 (rowsOf p) _ _ 1 r3
  obtain ⟨j, hj, hjq, hr⟩ := r4 q hR
  obtain ⟨⟨hb, hm⟩, i, hi, hpi⟩ := rowsOf_tb p _ hr
  have c0 : ∀ q, (colsOf p).testBit q = true →
      ∃ j, j < 1 ∧ 12 * j ≤ q ∧ (colsOf p).testBit (q - 12 * j) = true :=
    fun q hq => ⟨0, by norm_num, by omega, by simpa using hq⟩
  have c1 := orSL_ex 12 (colsOf p) _ 1 8 c0
  have c2 := orSL_ex 12 (colsOf p) _ _ 4 c1
  have c3 := orSL_ex 12 (colsOf p) _ _ 2 c2
  have c4 := orSL_ex 12 (colsOf p) _ _ 1 c3
  obtain ⟨j', hj', hjq', hc⟩ := c4 q hC
  obtain ⟨hlt, e', he', hpe⟩ := colsOf_tb p _ hc
  have e1 : i + (q - 1 * j) = 12 * (q / 12) + i := by omega
  have e2 : q - 12 * j' = q % 12 := by omega
  rw [e1] at hpi
  rw [e2] at hpe
  have hb' := hp _ hpe
  exact ⟨by omega, i, e', hi, by omega, hpi, hpe⟩

theorem hull_spec (p q : ℕ) (h : (hull p).testBit q = true) :
    q < 144 ∧ ∃ i e', i < 12 ∧ e' < 12 ∧ p.testBit (12 * (q / 12) + i) = true ∧
      p.testBit (12 * e' + q % 12) = true := by
  have hp : ∀ q, (Nat.land p full).testBit q = true → q < 144 := by
    intro q hq
    rw [tb_land, full_tb, Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.2
  obtain ⟨h1, i, e', hi, he, ha, hb⟩ := hullC_spec _ hp q h
  rw [tb_land, Bool.and_eq_true] at ha hb
  exact ⟨h1, i, e', hi, he, ha.1, hb.1⟩

def tw : List ℕ → ℕ → ℕ → ℕ
  | [], _, t => t
  | a :: l, o, t => tw l (Nat.lor o a) (Nat.lor t (Nat.land o a))

def priv (t a : ℕ) : ℕ := hull (Nat.land a (Nat.xor t full))

def hullsOK (t : ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | a :: l, acc => Nat.beq (Nat.land (priv t a) a) (priv t a) &&
      (Nat.beq (Nat.land acc (priv t a)) 0 && hullsOK t l (Nat.lor acc (priv t a)))

def avOK1 (as : List ℕ) : Bool := hullsOK (tw as 0 0) as 0

def orL : List ℕ → ℕ
  | [] => 0
  | a :: l => Nat.lor a (orL l)

def rectOK1 (l : List ℕ) : Bool := avOK1 (l.map rectW)

def IsRect (R : ℕ → Prop) : Prop :=
  ∀ e i e' i' : ℕ, e < 12 → i < 12 → e' < 12 → i' < 12 →
    R (12 * e + i) → R (12 * e' + i') → R (12 * e + i')

def Part (zs : List ((ℕ → Prop) × ℕ)) : Prop :=
  (∀ z ∈ zs, IsRect z.1) ∧
  (∀ z ∈ zs, ∀ q, z.1 q → q < 144) ∧
  (zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False)) ∧
  (∀ q, q < 144 → ∃ z ∈ zs, z.1 q) ∧
  (∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true)

theorem Part.rect {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, IsRect z.1 := h.1

theorem Part.bnd {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, ∀ q, z.1 q → q < 144 := h.2.1

theorem Part.disj {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False) := h.2.2.1

theorem Part.cov {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ q, q < 144 → ∃ z ∈ zs, z.1 q := h.2.2.2.1

theorem Part.sub {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true := h.2.2.2.2


theorem pw_forall {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) :
    ∀ l : List α, l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons x l ih =>
    intro h a ha b hb hab
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with ha' | ha'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · exact absurd (ha'.trans hb'.symm) hab
      · rw [ha']; exact h.1 b hb'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · rw [hb']; exact hs _ _ (h.1 a ha')
      · exact ih h.2 a ha' b hb' hab

theorem tw_spec (q : ℕ) : ∀ (as : List ℕ) (o t : ℕ), (tw as o t).testBit q = false →
    t.testBit q = false ∧ (o.testBit q = true → ∀ a ∈ as, a.testBit q = false) ∧
    as.Pairwise (fun a b => ¬ (a.testBit q = true ∧ b.testBit q = true)) := by
  intro as
  induction as with
  | nil => intro o t h; exact ⟨h, fun _ a ha => by simp at ha, List.Pairwise.nil⟩
  | cons a l ih =>
    intro o t h
    obtain ⟨h1, h2, h3⟩ := ih (Nat.lor o a) (Nat.lor t (Nat.land o a)) h
    rw [tb_lor, Bool.or_eq_false_iff, tb_land] at h1
    refine ⟨h1.1, ?_, ?_⟩
    · intro ho b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · have h4 := h1.2
        rw [ho] at h4
        simpa using h4
      · exact h2 (by rw [tb_lor, ho]; rfl) b hb
    · refine List.pairwise_cons.mpr ⟨?_, h3⟩
      intro b hb hab
      have h4 := h2 (by rw [tb_lor, hab.1]; simp) b hb
      rw [h4] at hab
      exact Bool.noConfusion hab.2

theorem priv_in {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) : ∀ z ∈ zs, ∀ q,
    (priv (tw (zs.map Prod.snd) 0 0) z.2).testBit q = true → z.1 q := by
  intro z hz q hq
  obtain ⟨hq144, i, e', hi, he', ha, hb⟩ := hull_spec _ q hq
  have key : ∀ x, x < 144 →
      (Nat.land z.2 (Nat.xor (tw (zs.map Prod.snd) 0 0) full)).testBit x = true → z.1 x := by
    intro x hx hbit
    rw [tb_land, tb_xor, full_tb, Bool.and_eq_true] at hbit
    obtain ⟨hzx, ht⟩ := hbit
    have ht' : (tw (zs.map Prod.snd) 0 0).testBit x = false := by simpa [hx] using ht
    obtain ⟨_, _, hpw⟩ := tw_spec x _ 0 0 ht'
    rw [List.pairwise_map] at hpw
    obtain ⟨z', hz', hzq⟩ := hP.cov x hx
    by_cases hzz : z' = z
    · rw [← hzz]; exact hzq
    · exfalso
      exact pw_forall (fun a b h h' => h ⟨h'.2, h'.1⟩) zs hpw z' hz' z hz hzz
        ⟨hP.sub z' hz' x hzq, hzx⟩
  have h1 := key _ (by omega) ha
  have h2 := key _ (by omega) hb
  have h3 := hP.rect z hz (q / 12) i e' (q % 12) (by omega) hi he' (Nat.mod_lt _ (by norm_num))
    h1 h2
  rwa [Nat.div_add_mod] at h3

theorem hullsOK_sound (t : ℕ) : ∀ (zs : List ((ℕ → Prop) × ℕ)) (acc : ℕ),
    (∀ z ∈ zs, ∀ q, (priv t z.2).testBit q = true → z.1 q) →
    (∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true) →
    zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False) →
    (∀ q, acc.testBit q = true → ∀ z ∈ zs, ¬ z.1 q) →
    hullsOK t (zs.map Prod.snd) acc = true := by
  intro zs
  induction zs with
  | nil => intros; rfl
  | cons z zs ih =>
    intro acc hh hs hd ha
    rw [List.pairwise_cons] at hd
    have hz := hh z List.mem_cons_self
    have e1 := land_sub _ _ (fun q hq => hs z List.mem_cons_self q (hz q hq))
    have e2 := land_disj acc (priv t z.2) (fun q h1 h2 => ha q h1 z List.mem_cons_self (hz q h2))
    have e3 := ih (Nat.lor acc (priv t z.2)) (fun z' hz' => hh z' (List.mem_cons_of_mem _ hz'))
      (fun z' hz' => hs z' (List.mem_cons_of_mem _ hz')) hd.2 (fun q hq z' hz' hz'q => by
        rw [tb_lor, Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · exact ha q hq z' (List.mem_cons_of_mem _ hz') hz'q
        · exact hd.1 z' hz' q (hz q hq) hz'q)
    show (Nat.beq (Nat.land (priv t z.2) z.2) (priv t z.2) &&
      (Nat.beq (Nat.land acc (priv t z.2)) 0 &&
        hullsOK t (zs.map Prod.snd) (Nat.lor acc (priv t z.2)))) = true
    rw [e1, e2, e3, Nat.beq_refl]
    rfl

theorem avOK1_sound {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) :
    avOK1 (zs.map Prod.snd) = true :=
  hullsOK_sound _ zs 0 (priv_in hP) hP.sub hP.disj (fun q hq => by simp at hq)

end PackedRect

abbrev Witness := Word × Nat × Nat

def witnessWord (w : Witness) : Word := w.1

def essentialB (mask target : Word) (stock : List Word) (entry : Witness) : Bool :=
  let (w,p,n) := entry
  mask.testBit p && mask.testBit n && target.testBit p && !target.testBit n &&
    (w.testBit p != w.testBit n) &&
    stock.all (fun x => x == w || x.testBit p == x.testBit n)

theorem essentialRequired {stock : List Word} {entry : Witness} {S : Finset Word} {k t : Nat}
    (ok : essentialB mask target stock entry = true)
    (sub : ∀ w ∈ S, w ∈ stock) (live : LiveWord mask target k t S) :
    witnessWord entry ∈ S := by
  obtain ⟨w,p,n⟩ := entry
  simp only [essentialB, Bool.and_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨mp,mn⟩,tp⟩,tn⟩,unequal⟩,rest⟩ := ok
  by_contra no
  have all : ∀ x ∈ S, AgreesAt p n x := by
    intro x hx
    have h := List.all_eq_true.mp rest x (sub x hx)
    have hw : x ≠ w := fun e => no (by simpa [witnessWord, e] using hx)
    simpa [hw, AgreesAt] using h
  have agree := liveAgrees live (mp.trans mn.symm) all
  have falseBit : target.testBit n = false := by simpa using tn
  simp [AgreesAt, tp, falseBit] at agree

theorem essentialWordsIn {stock : List Word} {witnesses : List Witness} {S : Finset Word} {k t : Nat}
    (ok : witnesses.all (essentialB mask target stock) = true)
    (sub : ∀ w ∈ S, w ∈ stock) (live : LiveWord mask target k t S) :
    (witnesses.map witnessWord).toFinset ⊆ S := by
  intro w hw
  obtain ⟨entry, mem, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
  exact essentialRequired (List.all_eq_true.mp ok entry mem) sub live

theorem essentialLower {stock : List Word} {witnesses : List Witness} {minimum : Nat}
    (proper : properWord mask target)
    (masked : ∀ w ∈ stock, Masked mask w)
    (ok : witnesses.all (essentialB mask target stock) = true)
    (bound : minimum ≤ (witnesses.map witnessWord).toFinset.card - 1) :
    Lower mask stock target minimum := by
  intro values build hit
  obtain ⟨k,t,S,hk,live,sub⟩ := extractWordLive masked build hit proper
  have card := Finset.card_le_card (essentialWordsIn ok sub live)
  have size := (liveWordSize live).2
  omega

theorem essentialLift {stock cutStock : List Word} {witnesses : List Witness} {minimum cut prior : Nat}
    (proper : properWord mask target)
    (masked : ∀ w ∈ stock, Masked mask w)
    (ok : witnesses.all (essentialB mask target stock) = true)
    (submask : mask &&& cut = cut)
    (cutProper : properWord cut (target &&& cut))
    (supplies : ∀ w ∈ stock, AvailableWord cut cutStock (w &&& cut))
    (known : Lower cut cutStock (target &&& cut) prior)
    (bound : minimum ≤ prior + (flatSet cut (witnesses.map witnessWord).toFinset).card) :
    Lower mask stock target minimum := by
  intro values build hit
  obtain ⟨k,t,S,hk,live,sub⟩ := extractWordLive masked build hit proper
  have subW := essentialWordsIn ok sub live
  have subFlat : flatSet cut (witnesses.map witnessWord).toFinset ⊆ flatSet cut S :=
    Finset.filter_subset_filter _ subW
  have card := Finset.card_le_card subFlat
  have pf : ¬maskedFlat cut target := by simpa [maskedFlat, properWord] using cutProper
  obtain ⟨n, budget, built⟩ := maskedBuild live cut submask pf
  have starts : ∀ w ∈ projectedStock cut S, AvailableWord cut cutStock w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image] at hw
    rcases hw with rfl | rfl | ⟨x,hx,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact supplies _ (sub _ hx)
  obtain ⟨ys,len,built',out⟩ := buildableWords built starts
  have lower := known ys built' out
  omega

def unpackWitnesses (stock : List Word) (codes : List Nat) : List Witness :=
  List.rec [] (fun code _ rest =>
    (stock.getD (code >>> 18) 0, (code >>> 9) &&& 511, code &&& 511) :: rest) codes

def DagAuto (mask goal : Word) (select : Fin rows → Fin rows) : Prop :=
  Function.Surjective select ∧ relabel select mask = mask ∧ relabel select goal = goal

abbrev WordMoveStep := List (Word × Nat) × List (Word × Nat)
abbrev WordMove := List WordMoveStep

def mixStep (m : WordMoveStep) (w : Word) : Word :=
  let left := List.rec 0 (fun (part,n) _ acc => ((w &&& part) <<< n) ||| acc) m.1
  let right := List.rec 0 (fun (part,n) _ acc => ((w &&& part) >>> n) ||| acc) m.2
  left ||| right

def BitLinear (f : Word → Word) : Prop :=
  ∀ w i, (f w).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (2 ^ j)).testBit i = true

theorem bitLinearZero : BitLinear (fun _ => 0) := by
  simp [BitLinear]

theorem bitLinearOr {f g : Word → Word} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f w ||| g w) := by
  intro w i
  change ((f w ||| g w).testBit i = true) ↔ _
  simp only [Nat.testBit_or, Bool.or_eq_true]
  rw [hf w i, hg w i]
  constructor
  · rintro (⟨j,hw,hj⟩ | ⟨j,hw,hj⟩)
    · exact ⟨j,hw,Or.inl hj⟩
    · exact ⟨j,hw,Or.inr hj⟩
  · rintro ⟨j,hw,hj | hj⟩
    · exact Or.inl ⟨j,hw,hj⟩
    · exact Or.inr ⟨j,hw,hj⟩

theorem bitLinearLeft (mask n : Nat) : BitLinear (fun w => (w &&& mask) <<< n) := by
  intro w i
  simp only [Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hw, hm⟩
    exact ⟨i-n,hw,h,rfl,hm⟩
  · rintro ⟨j,hw,h,rfl,hm⟩
    exact ⟨h,hw,hm⟩

theorem bitLinearRight (mask n : Nat) : BitLinear (fun w => (w &&& mask) >>> n) := by
  intro w i
  simp only [Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hw,hm⟩
    exact ⟨n+i,hw,rfl,hm⟩
  · rintro ⟨j,hw,rfl,hm⟩
    exact ⟨hw,hm⟩

theorem mixStepLinear (move : WordMoveStep) : BitLinear (mixStep move) := by
  obtain ⟨left, right⟩ := move
  unfold mixStep
  apply bitLinearOr
  · induction left with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearLeft part count) ih
  · induction right with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearRight part count) ih

def mixMove (move : WordMove) (w : Word) : Word :=
  (List.rec (motive := fun _ => Word → Word) id
    (fun step _ next w => next (mixStep step w)) move) w

theorem bitLinearId : BitLinear id := by
  intro w i
  change w.testBit i = true ↔ ∃ j, w.testBit j = true ∧ (2 ^ j).testBit i = true
  simp [Nat.testBit_two_pow]

theorem bitLinearComp {f g : Word → Word} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f (g w)) := by
  intro w i
  change (f (g w)).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (g (2 ^ j))).testBit i = true
  rw [hf]
  constructor
  · rintro ⟨j,gj,fj⟩
    obtain ⟨k,wk,gk⟩ := (hg w j).mp gj
    exact ⟨k,wk,(hf (g (2^k)) i).mpr ⟨j,gk,fj⟩⟩
  · rintro ⟨j,wj,h⟩
    obtain ⟨k,gk,fk⟩ := (hf (g (2^j)) i).mp h
    exact ⟨k,(hg w k).mpr ⟨j,wj,gk⟩,fk⟩

theorem mixMoveLinear (move : WordMove) : BitLinear (mixMove move) := by
  induction move with
  | nil => exact bitLinearId
  | cons op ops ih =>
    change BitLinear (fun w => mixMove ops (mixStep op w))
    exact bitLinearComp ih (mixStepLinear op)

def permuteAxes (axes : List Nat) (offset row : Nat) : Nat :=
  offset ^^^ (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun j _ next i => (if row.testBit i then 1 <<< j else 0) ||| next (i + 1)) axes) 0

theorem relabelLinear (select : Fin rows → Fin rows) : BitLinear (relabel select) := by
  intro w i
  by_cases inside : i < rows
  · let ii : Fin rows := ⟨i,inside⟩
    change (relabel select w).testBit ii.val = true ↔ _
    rw [relabelBit]
    constructor
    · intro h
      refine ⟨(select ii).val,h,?_⟩
      change (relabel select (2 ^ (select ii).val)).testBit ii.val = true
      rw [relabelBit, Nat.testBit_two_pow]
      simp
    · rintro ⟨j,h,bit⟩
      change (relabel select (2^j)).testBit ii.val = true at bit
      rw [relabelBit, Nat.testBit_two_pow, decide_eq_true_eq] at bit
      exact bit ▸ h
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]
    simp [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]

theorem wordMoveAgreement {select : Fin rows → Fin rows} {mask : Word} {move : WordMove}
    (bounded : Masked (fullMask rows) mask)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = relabel select (2 ^ i.val))
    {w : Word} (masked : Masked mask w) : mixMove move w = relabel select w := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [mixMoveLinear, relabelLinear]
  have source {j : Nat} (bit : w.testBit j = true) :
      mixMove move (2^j) = relabel select (2^j) := by
    have m : mask.testBit j = true := by
      have eq := congrArg (fun x : Nat => x.testBit j) masked
      simpa [Nat.testBit_and, bit] using eq
    have within : j < rows := by
      have eq := congrArg (fun x : Nat => x.testBit j) bounded
      simpa [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, m] using eq
    exact basis ⟨j,within⟩ m
  constructor <;> rintro ⟨j,hj,hi⟩
  · exact ⟨j,hj,by rwa [← source hj]⟩
  · exact ⟨j,hj,by rwa [source hj]⟩

theorem relabelBasis {select inverse : Fin rows → Fin rows}
    (left : ∀ i, inverse (select i) = i) :
    ∀ j : Fin rows, select (inverse j) = j →
      relabel select (2 ^ j.val) = 2 ^ (inverse j).val := by
  intro j right
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · let pos : Fin rows := ⟨i,inside⟩
    change (relabel select (2 ^ j.val)).testBit pos.val = _
    rw [relabelBit, Nat.testBit_two_pow, Nat.testBit_two_pow]
    apply (Bool.eq_iff_iff).mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro eq
      have e : j = select pos := Fin.ext eq
      rw [e,left]
    · intro eq
      have hp : inverse j = pos := Fin.ext eq
      rw [← hp, right]
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside), Nat.testBit_two_pow]
    have ne : (inverse j).val ≠ i := by have := (inverse j).isLt; omega
    simp [ne]

theorem dagAutoFromMove {select inverse : Fin rows → Fin rows} {mask goal : Word} {move : WordMove}
    (left : ∀ i, inverse (select i) = i)
    (right : ∀ i, select (inverse i) = i)
    (bm : Masked (fullMask rows) mask)
    (gm : Masked mask goal)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val)
    (sameMask : mixMove move mask = mask) (sameGoal : mixMove move goal = goal) :
    DagAuto mask goal select ∧ ∀ w, Masked mask w → mixMove move w = relabel select w := by
  have agree {w : Word} (hw : Masked mask w) : mixMove move w = relabel select w :=
    wordMoveAgreement bm (fun i h => (basis i h).trans (relabelBasis left i (right i)).symm) hw
  exact ⟨⟨fun i => ⟨inverse i,right i⟩,(agree (by simp [Masked])).symm.trans sameMask,
    (agree gm).symm.trans sameGoal⟩,fun _ h => agree h⟩

theorem maskedBelow {mask w : Word} (bm : Masked (fullMask rows) mask)
    (bw : Masked mask w) : Masked (fullMask rows) w := by
  unfold Masked at *
  rw [← bw, Nat.land_assoc, bm, bw]

theorem maskedTransfer {mask w : Word} {select : Fin rows → Fin rows}
    (same : relabel select mask = mask) (hw : Masked mask w) :
    Masked mask (relabel select w) := by
  unfold Masked at *
  rw [← same, ← relabelAnd, hw]

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

abbrev RowChart := { rows : List Nat // rows.length = 24 }

def chartRow (chart : RowChart) (i : Nat) : Nat :=
  chart.val.getD i 0

def chartBits (w : Word) (rows : List Nat) : Word :=
  List.rec 0 (fun r _ packed => ((w >>> r) &&& 1) ||| (packed <<< 1)) rows

theorem chartBitsBit (w : Word) (rows : List Nat) (i : Nat) (hi : i < rows.length) :
    (chartBits w rows).testBit i = w.testBit (rows.getD i 0) := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons row rows ih =>
    change (((w >>> row) &&& 1) ||| (chartBits w rows <<< 1)).testBit i = _
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp
    | succ i =>
      have lt : i < rows.length := by simpa using hi
      simp [ih i lt, Nat.testBit_succ]

def chartWord (chart : RowChart) (w : Word) : Word := chartBits w chart.val

def ChartOK (goal : Word) (chart : RowChart) : Prop :=
  (∀ i : Fin 12, goal.testBit (chartRow chart i.val) = true) ∧
  (∀ i : Fin 12, goal.testBit (chartRow chart (12+i.val)) = false)

def chartCheck (goal : Word) (chart : Option RowChart) : Bool :=
  chart.all fun c => @decide (ChartOK goal c) (by unfold ChartOK; infer_instance)

theorem chartOfCheck {goal : Word} {chart : Option RowChart}
    (ok : chartCheck goal chart = true) (c : RowChart) (eq : chart = some c) :
    ChartOK goal c := by
  subst chart
  unfold ChartOK
  exact of_decide_eq_true ok

theorem chartWordBit (chart : RowChart) (w : Word) {i : Nat} (hi : i < 24) :
    (chartWord chart w).testBit i = w.testBit (chartRow chart i) := by
  exact chartBitsBit w chart.val i (by rw [chart.property]; exact hi)

theorem chartPos {goal : Word} {chart : RowChart} (ok : ChartOK goal chart) {i : Nat} (hi : i < 12) :
    goal.testBit (chartRow chart i) = true := ok.1 ⟨i,hi⟩

theorem chartNeg {goal : Word} {chart : RowChart} (ok : ChartOK goal chart) {i : Nat} (hi : i < 12) :
    goal.testBit (chartRow chart (12+i)) = false := ok.2 ⟨i,hi⟩

theorem chartRectangles {goal : Word} {chart : RowChart} {ws : List Word}
    (ok : ChartOK goal chart) (nd : ws.Nodup) (kw : KWPartition goal ws.toFinset) :
    PackedRect.rectOK1 (ws.map (chartWord chart)) = true := by
  obtain ⟨f, good, rectangle⟩ := kw
  let label := fun p n => f (chartRow chart p) (chartRow chart (12+n))
  let part := fun w => ((fun q : Nat => q < 144 ∧ label (q/12) (q % 12) = w),
    PackedRect.rectW (chartWord chart w))
  have partition : PackedRect.Part (ws.map part) := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro z hz
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      intro p n p' n' hp hn hp' hn' h h'
      have divmod (a b : Nat) (lt : b < 12) :
          (12*a+b)/12 = a ∧ (12*a+b)%12 = b := by omega
      have h1 := h.2
      have h2 := h'.2
      rw [(divmod p n hn).1, (divmod p n hn).2] at h1
      rw [(divmod p' n' hn').1, (divmod p' n' hn').2] at h2
      refine ⟨by omega,?_⟩
      rw [(divmod p n' hn').1, (divmod p n' hn').2]
      exact (rectangle _ _ _ _ (chartPos ok hp) (chartPos ok hp') (chartNeg ok hn)
        (chartNeg ok hn') (h1.trans h2.symm)).trans h1
    · intro z hz q hq
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      exact hq.1
    · rw [List.pairwise_map]
      exact List.Pairwise.imp (fun hne q h1 h2 => hne (h1.2.symm.trans h2.2)) nd
    · intro q hq
      have member := (good _ _ (chartPos ok (show q/12 < 12 by omega))
        (chartNeg ok (Nat.mod_lt q (by decide : 0 < 12)))).1
      exact ⟨_, List.mem_map.mpr ⟨_,List.mem_toFinset.mp member,rfl⟩,hq,rfl⟩
    · intro z hz q hq
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      obtain ⟨bound, same⟩ := hq
      have hp : q/12 < 12 := by omega
      have hn : q % 12 < 12 := Nat.mod_lt _ (by decide)
      have h := (good _ _ (chartPos ok hp) (chartNeg ok hn)).2
      change (label (q/12) (q % 12)).testBit (chartRow chart (q/12)) = true ∧
        (label (q/12) (q % 12)).testBit (chartRow chart (12+q % 12)) = false at h
      rw [same] at h
      have bit := PackedRect.rectW_tb (chartWord chart w) (q/12) (q % 12) hp hn
        ((chartWordBit chart w (by omega)).trans h.1)
        ((chartWordBit chart w (by omega)).trans h.2)
      rwa [Nat.div_add_mod] at bit
  have hw := PackedRect.avOK1_sound partition
  simpa only [PackedRect.rectOK1, List.map_map, Function.comp_def, part] using hw

theorem tightChart {goal mask : Word} {chart : RowChart} {ws : List Word} {fuel : Nat}
    (ok : ChartOK goal chart) (tight : ws.length = fuel + 1)
    (viable : WordViable mask goal (fuel,ws,[])) : PackedRect.rectOK1 (ws.map (chartWord chart)) = true := by
  obtain ⟨nd,k,t,cap,live⟩ := viable
  change k ≤ fuel at cap
  have card := (liveWordSize live).2
  rw [List.toFinset_card_of_nodup nd] at card
  change (ws : List Word).length + t ≤ k + 1 at card
  have ht : t = 0 := by omega
  have hk : ws.toFinset.card = k + 1 := by
    have q : ws.toFinset.card = ws.length := List.toFinset_card_of_nodup nd
    omega
  subst t
  exact chartRectangles ok nd (kwFromLive live hk)

def dagForceWord {α : Type} (word : Word) (cont : Word → α) : α :=
  Nat.rec (cont 0) (fun k _ => cont (k + 1)) word

theorem dagForceWordEq {α : Type} (word : Word) (cont : Word → α) :
    dagForceWord word cont = cont word := by cases word <;> rfl

def dagForceWords (words : List Word) (cont : List Word → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Word → Bool) → Bool) (fun k => k [])
    (fun w _ next k => dagForceWord w (fun v => next (fun rest => k (v :: rest)))) words) cont

theorem dagForceWordsEq (words : List Word) (cont : List Word → Bool) :
    dagForceWords words cont = cont words := by
  induction words generalizing cont with
  | nil => rfl
  | cons w ws ih =>
    change dagForceWord w (fun v => dagForceWords ws (fun rest => cont (v :: rest))) = _
    rw [dagForceWordEq, ih]

def dagBoundCloses (target : Word) (state : RowState) (bound : Bound) : Bool :=
  let (mask, stock, lower, goal) := bound
  let (fuel, ws, history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    dagForceWord (fuel - flatCount mask ws) (fun remaining =>
      if Nat.blt remaining lower then
        dagForceWords (recipeStart mask stock ws) (fun start =>
          if Nat.blt (start.length + remaining) lower then
            dagForceWords (recipeClosure mask stock history start) (fun needed =>
              if Nat.blt (needed.length + remaining) lower then
                dagForceWords (replayRecipes mask needed history.reverse stock) (fun replay =>
                  decide (replay.length + remaining < lower) &&
                    ws.all (fun w => availableB mask (replay ++ stock) (w &&& mask)))
              else false)
          else false)
      else false)

theorem dagBoundClosesEq (target : Word) (state : RowState) (bound : Bound) :
    dagBoundCloses target state bound = boundCloses target state bound := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨mask, stock, lower, goal⟩ := bound
  simp [dagBoundCloses, boundCloses, dagForceWordsEq, dagForceWordEq, Nat.blt_eq]

def dagKnownCloses (target : Word) (bounds : List Bound) (state : RowState) : Bool :=
  List.rec false (fun bound _ later => dagBoundCloses target state bound || later) bounds

theorem dagKnownClosesEq (target : Word) (bounds : List Bound) (state : RowState) :
    dagKnownCloses target bounds state = knownCloses target bounds state := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (dagBoundCloses target state bound || dagKnownCloses target bounds state) =
      (boundCloses target state bound || knownCloses target bounds state)
    rw [dagBoundClosesEq, ih]

abbrev DagLink := Nat × Nat
abbrev DagLinks := Nat → Nat → Option DagLink

def dagAllowedRoot (witnesses : List Witness) (ws : List Word) : Bool :=
  witnesses.all (fun entry => ws.contains (witnessWord entry))

def dagTrace (mask : Word) (stock : List Word) (fuel : Nat) (forest : Forest)
    (i : Nat) : Option RowState :=
  (Nat.rec (motive := fun _ => Nat → Option RowState) (fun _ => none)
    (fun _ previous j =>
      let (parent, token) := forest j
      if parent == 0 then
        if token < 2 ^ stock.length then some (rootState stock fuel token) else none
      else (previous (parent - 1)).bind (childState mask token)) (fuel + 1)) i

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

def dagPartition (directed : Bool) (ws : List Word) : Word → Word → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      Nat.beq p 0 || Nat.beq n 0 ||
      dagForceWord (p &&& w) (fun up =>
        dagForceWord (n &&& w) (fun down =>
          rest up down &&
            dagForceWord (p ^^^ up) (fun offP =>
              dagForceWord (if directed then n else n ^^^ down) (rest offP))))) ws

theorem dagOffBits {v w : Word} {i : Nat} (bit : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor, Nat.testBit_and] at bit
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv, hw] at bit ⊢

theorem dagPartitionSound {directed : Bool} {ws : List Word} {positive negative : Word}
    (fail : dagPartition directed ws positive negative = false) :
    ∃ p n, positive.testBit p = true ∧ negative.testBit n = true ∧
      ∀ w ∈ ws, if directed then w.testBit p = true → w.testBit n = true
                  else w.testBit p = w.testBit n := by
  have nonempty {w : Word} (hn : w ≠ 0) : ∃ j, w.testBit j = true := by
    by_contra! all
    apply hn
    apply Nat.eq_of_testBit_eq
    intro i
    simp [all i]
  induction ws generalizing positive negative with
  | nil =>
    change (Nat.beq positive 0 || Nat.beq negative 0) = false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p,hp⟩ := nonempty (w := positive) (fun eq => by simp [eq] at fail)
    obtain ⟨n,hn⟩ := nonempty (w := negative) (fun eq => by simp [eq] at fail)
    exact ⟨p,n,hp,hn,by simp⟩
  | cons w ws ih =>
    change (Nat.beq positive 0 || Nat.beq negative 0 ||
      dagForceWord (positive &&& w) (fun up =>
        dagForceWord (negative &&& w) (fun down =>
          dagPartition directed ws up down &&
            dagForceWord (positive ^^^ up) (fun offP =>
              dagForceWord (if directed then negative else negative ^^^ down)
                (dagPartition directed ws offP))))) = false at fail
    simp only [dagForceWordEq, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p,n,hp,hn,agree⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hn
      refine ⟨p,n,hp.1,hn.1,?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | tail
      · simp [hp.2, hn.2]
      · exact agree _ tail
    · obtain ⟨p,n,hp,hn,agree⟩ := ih off
      have hp' := dagOffBits hp
      cases mode : directed
      · have hn' : negative.testBit n = true ∧ w.testBit n = false := by
          apply dagOffBits
          simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn'.1,?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2, hn'.2]
        · simpa [mode] using agree _ tail
      · have hn' : negative.testBit n = true := by simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn',?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2]
        · simpa [mode] using agree _ tail

theorem dagPartitionLive {mask goal : Word} {ws : List Word} {k t : Nat} {directed : Bool}
    (goalMask : Masked mask goal) (live : LiveWord mask goal k t ws.toFinset)
    (noNot : directed = true → t = 0) :
    dagPartition directed ws goal (mask ^^^ goal) = true := by
  by_contra fail
  have openPair : dagPartition directed ws goal (mask ^^^ goal) = false := by
    cases h : dagPartition directed ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p,n,hp,hn,agree⟩ := dagPartitionSound openPair
  have pm := positiveInMask goalMask hp
  have nm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have implied := fun ht : goal.testBit n = true => positiveInMask goalMask ht
    cases hm : mask.testBit n <;> cases ht : goal.testBit n <;> simp_all
  cases mode : directed with
  | false =>
    have same := liveAgrees live (pm.trans nm.1.symm) (fun w hw => by
      simpa [mode,AgreesAt] using agree w (List.mem_toFinset.mp hw))
    simp [AgreesAt, hp, nm.2] at same
  | true =>
    have ht := noNot mode
    subst t
    obtain ⟨w,hw,a,b⟩ := liveDirected live hp nm.2
    have same := agree w (List.mem_toFinset.mp hw)
    simp [mode, a, b] at same

abbrev DagSample := Nat × Nat
abbrev DagSignals := Word × Word
abbrev DagCounts := Word × Word × Word

def dagForceCache (tags : List DagSignals) (use : List DagSignals → Bool) : Bool :=
  (List.rec (motive := fun _ => (List DagSignals → Bool) → Bool) (fun k => k [])
    (fun tag _ next k =>
      dagForceWord tag.1 (fun up => dagForceWord tag.2 (fun down =>
        next (fun tail => k ((up,down)::tail))))) tags) use

theorem dagForceCacheEq (tags : List DagSignals) (use : List DagSignals → Bool) :
    dagForceCache tags use = use tags := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag rest ih =>
    obtain ⟨a,b⟩ := tag
    change dagForceWord a (fun up => dagForceWord b (fun down =>
      dagForceCache rest (fun tail => use ((up,down)::tail)))) = _
    simp only [dagForceWordEq, ih]

def dagSignalContrast (directed : Bool) (full : Word) (tag : DagSignals) : Word :=
  if directed then tag.1 &&& (tag.2 ^^^ full) else tag.1 ^^^ tag.2

def dagCountStep (acc : DagCounts) (column : Word) : DagCounts :=
  (acc.1 ||| column, acc.2.1 ||| (acc.1 &&& column), acc.2.2 ||| (acc.2.1 &&& column))

def dagCountSigns (directed : Bool) (full : Word) (tags : List DagSignals)
    (use : DagCounts → Bool) : Bool :=
  (List.rec (motive := fun _ => (DagCounts → Bool) → Bool) (fun k => k (0,0,0))
    (fun tag _ more k =>
      dagForceWord (dagSignalContrast directed full tag) (fun column =>
        more (fun acc =>
          dagForceWord (acc.1 ||| column) (fun once =>
            dagForceWord (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
              dagForceWord (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => k (once,twice,thrice)))))))
    tags) use

theorem dagCountSignsEq (directed : Bool) (full : Word) (tags : List DagSignals)
    (use : DagCounts → Bool) : dagCountSigns directed full tags use =
    use (tags.foldr (fun tag acc => dagCountStep acc (dagSignalContrast directed full tag)) (0,0,0)) := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag tags ih =>
    change dagForceWord (dagSignalContrast directed full tag) (fun column =>
      dagCountSigns directed full tags (fun acc =>
        dagForceWord (acc.1 ||| column) (fun once =>
          dagForceWord (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
            dagForceWord (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => use (once,twice,thrice)))))) = _
    simp only [dagForceWordEq, ih]
    rfl

def dagHighest (value : Word) : Nat :=
  (Nat.rec (motive := fun _ => Word → Nat → Nat) (fun _ offset => offset)
    (fun i next w offset =>
      let shift := 1 <<< i
      dagForceWord (w >>> shift) (fun upper =>
        if Nat.beq upper 0 then next w offset else next upper (offset+shift))) 8) value 0

def dagSampleMiss (sample : DagSample) (full : Word) (normal tight : DagCounts)
    (x y out : DagSignals) (directed : Bool) (op keep : Nat) : List Nat :=
  let counts := if directed then tight else normal
  let dx := if keep.testBit 0 then 0 else dagSignalContrast directed full x
  let dy := if op == 2 || keep.testBit 1 then 0 else dagSignalContrast directed full y
  let rest := counts.2.2 ||| (counts.2.1 ^^^ (counts.2.1 &&& dx &&& dy)) |||
    (counts.1 ^^^ (counts.1 &&& (dx ||| dy)))
  dagForceWord ((rest ||| dagSignalContrast directed full out) ^^^ full) (fun missing =>
    if Nat.beq missing 0 then [] else [unpack sample.1 18 (dagHighest missing)])

def dagPairReject (mask goal : Word) (directed : Bool) (ws : List Word) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    let p := code &&& 511
    let n := code >>> 9
    goal.testBit p && mask.testBit n && !goal.testBit n &&
      ws.all (fun w => if directed then !(w.testBit p) || w.testBit n
                       else w.testBit p == w.testBit n)

theorem dagPairsOpen {mask goal : Word} {ws : List Word} {pairs : List Nat} {k t : Nat} {directed : Bool}
    (masked : Masked mask goal) (live : LiveWord mask goal k t ws.toFinset)
    (noNot : directed = true → t = 0) : dagPairReject mask goal directed ws pairs = false := by
  apply Bool.eq_false_iff.mpr
  intro close
  obtain ⟨code,_,check⟩ := List.any_eq_true.mp close
  simp only [Bool.and_eq_true, Bool.not_eq_true, List.all_eq_true] at check
  obtain ⟨⟨⟨hp, mn⟩, hn⟩, bank⟩ := check
  have neg : goal.testBit (code >>> 9) = false := by simpa using hn
  cases mode : directed
  · have h := liveAgrees live ((positiveInMask masked hp).trans mn.symm) (fun w hw => by
      have pair := bank _ (List.mem_toFinset.mp hw)
      simpa [mode, AgreesAt] using pair)
    simp [AgreesAt, hp, neg] at h
  · have ht := noNot mode
    subst t
    obtain ⟨word,mem,on,off⟩ := liveDirected live hp neg
    have pair := bank _ (List.mem_toFinset.mp mem)
    simp [mode,on,off] at pair

def dagLocal (mask goal : Word) (chart : Option RowChart)
    (cut : CutCheck) (state : RowState) : Bool :=
  let (fuel,ws,_) := state
  ws.length > fuel + 1 ||
    (!ws.contains goal &&
      (fuel == 0 ||
        (if ws.length == fuel + 1 then
           chart.any (fun c => !PackedRect.rectOK1 (ws.map (chartWord c)))
         else false) ||
        cut state ||
        (if ws.length == fuel + 1 then !dagPartition true ws goal (mask ^^^ goal)
         else !dagPartition false ws goal (mask ^^^ goal))))

def dagSizeFloor (n op keep : Nat) : Nat :=
  (n - (if keep.testBit 0 then 0 else 1) -
    (if op == 2 || keep.testBit 1 then 0 else 1)) + 1

def dagTooWide (n fuel token : Nat) : Bool :=
  dagSizeFloor n (token / 4 % 3) (token % 4) > (fuel-1) + 1

def dagKept (ws : List Word) (op keep x y : Nat) : List Word :=
  keepWord (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)

def dagGateWord (mask op x y : Word) : Word :=
  if Nat.beq op 0 then x &&& y else if Nat.beq op 1 then x ||| y else mask ^^^ x

def dagDirectChild (mask : Word) (state : RowState) (a b op keep x y out : Nat) : Option RowState :=
  let (fuel, ws, history) := state
  if fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b) then none
  else if out == 0 || out == mask || ws.contains out then none
  else
    some (fuel-1, insertWord out (dagKept ws op keep x y), (out,x,y) :: history)

theorem dagDirectChildEq {mask a b op keep : Nat} {state : RowState}
    (hb : b < 64) (hop : op < 3) (hk : keep < 4) :
    let x := state.2.1.getD a 0
    let y := state.2.1.getD b 0
    dagDirectChild mask state a b op keep x y (dagGateWord mask op x y) =
      childState mask (gateToken a b op keep) state := by
  obtain ⟨fuel,ws,history⟩ := state
  obtain ⟨keepEq,opEq,aEq,bEq⟩ := gateTokenFields (a := a) hb hop hk
  simp only [childState, keepEq, opEq, aEq, bEq]
  rfl

abbrev DagTagged := Word × DagSignals

def dagTagBases (stock : List Word) (positive negative width : Nat) : List DagTagged :=
  (List.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun w _ next i => (w, unpack positive width i, unpack negative width i) :: next (i+1)) stock) 0

def dagTagRoot (bank : List DagTagged) (token : Nat) : List DagTagged :=
  (List.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun tag _ next k =>
      if Nat.beq (k &&& 1) 0 then next (k >>> 1) else tag :: next (k >>> 1)) bank) token

def dagTagKeep (keep : Bool) (w : Word) (bank : List DagTagged) : List DagTagged :=
  if keep then bank
  else List.rec [] (fun tag tail next => if Nat.beq tag.1 w then tail else tag :: next) bank

def dagTagInsert (tag : DagTagged) (bank : List DagTagged) : List DagTagged :=
  List.rec [tag] (fun old tail next => if Nat.ble tag.1 old.1 then tag :: old :: tail else old :: next) bank

def dagTagStep (mask full token : Word) (bank : List DagTagged) : List DagTagged :=
  let keep := token % 4
  let op := token / 4 % 3
  let x := bank.getD (token / (4*3*64)) (0,0,0)
  let y := bank.getD (token / (4*3) % 64) (0,0,0)
  let tag := (dagGateWord mask op x.1 y.1, dagGateWord full op x.2.1 y.2.1, dagGateWord full op x.2.2 y.2.2)
  dagTagInsert tag (dagTagKeep (op == 2 || keep.testBit 1) y.1 (dagTagKeep (keep.testBit 0) x.1 bank))

def dagTraceTags (mask width : Word) (root : List DagTagged) (fuel : Nat) (forest : Forest)
    (i : Nat) : List DagSignals :=
  let tags := (Nat.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun _ previous j =>
      let (parent, token) := forest j
      if Nat.beq parent 0 then dagTagRoot root token
      else dagTagStep mask (fullMask width) token (previous (parent-1))) (fuel+1)) i
  List.rec [] (fun tag _ rest => tag.2 :: rest) tags

def dagPackWords (ws : List Word) : Word :=
  List.rec 0 (fun w _ tail => (w &&& fullMask 512) ||| (tail <<< 512)) ws

def dagLaneMarks (n : Nat) : Word :=
  Nat.rec 0 (fun _ more => 1 ||| (more <<< 512)) n

def dagOmitted (a b : Nat) (left right : Bool) : Word :=
  (if left then 0 else 1 <<< (512*a)) ||| (if right then 0 else 1 <<< (512*b))

def dagPackedPair (mask goal packed marks erased out : Word) (directed : Bool) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    dagForceWord code (fun code =>
      dagForceWord (code &&& 511) (fun p =>
        dagForceWord (code >>> 9) (fun n =>
          let up := (packed >>> p) &&& marks
          let down := (packed >>> n) &&& marks
          let contrast := if directed then up &&& (down ^^^ marks) else up ^^^ down
          let gateOK := if directed then !out.testBit p || out.testBit n else out.testBit p == out.testBit n
          goal.testBit p && mask.testBit n && !goal.testBit n && Nat.blt p 512 && Nat.blt n 512 &&
            gateOK && Nat.beq (contrast &&& (marks ^^^ erased)) 0)))

theorem dagPackBits {ws : List Word} {i row : Nat} (inside : i < ws.length) (width : row < 512) :
    (dagPackWords ws).testBit (512*i+row) = (ws.getD i 0).testBit row := by
  induction ws generalizing i with
  | nil => simp at inside
  | cons w ws ih =>
    change ((w &&& fullMask 512) ||| (dagPackWords ws <<< 512)).testBit (512*i+row) = _
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp [fullMask, Nat.testBit_two_pow_sub_one, width, Nat.not_le.mpr width]
    | succ i =>
      have hi : i < ws.length := by simpa using inside
      have crossed : 512 ≤ 512*i.succ+row := by omega
      have offset : 512*i.succ+row-512 = 512*i+row := by omega
      have past : ¬ 512*i.succ+row < 512 := by omega
      simp [crossed, offset, fullMask, Nat.testBit_two_pow_sub_one, past, ih hi]

theorem dagMarkBits {length i : Nat} (inside : i < length) :
    (dagLaneMarks length).testBit (512*i) = true := by
  induction length generalizing i with
  | zero => omega
  | succ length ih =>
    change (1 ||| (dagLaneMarks length <<< 512)).testBit (512*i) = true
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp
    | succ i =>
      have hi : i < length := by omega
      have crossed : 512 ≤ 512*i.succ := by omega
      have offset : 512*i.succ-512 = 512*i := by omega
      simp [crossed, offset, ih hi]

def dagCheckChildren (mask goal : Word) (chart : Option RowChart) (cut : CutCheck)
    (reference : Nat → RowState → Bool) (state : RowState) (sample : DagSample) (tags : List DagSignals) : Bool :=
  let n := state.2.1.length
  (n ≤ 64) && !state.2.1.contains goal &&
  dagForceWord (dagPackWords state.2.1) (fun packed =>
    dagForceWord (dagLaneMarks n) (fun marks =>
      dagForceCache tags (fun tags =>
    dagForceWord (fullMask sample.2) (fun full =>
      dagCountSigns false full tags (fun normal =>
        dagCountSigns true full tags (fun tight =>
          let visit := fun a b op retains =>
            dagForceWord (state.2.1.getD a 0) (fun x =>
              dagForceWord (state.2.1.getD b 0) (fun y =>
                dagForceWord (dagGateWord mask op x y) (fun out =>
                  let xs := tags.getD a (0,0)
                  let ys := tags.getD b (0,0)
                  dagForceWord (dagGateWord full op xs.1 ys.1) (fun up =>
                    dagForceWord (dagGateWord full op xs.2 ys.2) (fun down =>
                      treeBlock 0 retains (fun keep =>
                        let token := gateToken a b op keep
                        if dagTooWide n state.1 token then true else
                          let directed := dagSizeFloor n op keep == (state.1-1)+1
                          let pairs := dagSampleMiss sample full normal tight xs ys (up,down) directed op keep
                          let erased := dagOmitted a b (keep.testBit 0) (op == 2 || keep.testBit 1)
                          if dagPackedPair mask goal packed marks erased out directed pairs then true
                          else match dagDirectChild mask state a b op keep x y out with
                          | none => true
                          | some (fuel, ws, history) => dagForceWords ws (fun forced =>
                            let child := (fuel, forced, history)
                            reference token child || dagLocal mask goal chart cut child)))))))
          treeBlock 0 n (fun a =>
            visit a a 2 2 && treeBlock (a+1) (n-(a+1)) (fun b =>
              treeBlock 0 2 (fun op => visit a b op 4)))))))))

def dagStateOK (mask : Word) (ws : List Word) : Bool :=
  (ws.dedup.length == ws.length) && ws.all (fun w => w &&& mask == w)

theorem dagStateOKSpec {mask : Word} {ws : List Word} (ok : dagStateOK mask ws = true) :
    ws.Nodup ∧ ∀ w ∈ ws, Masked mask w := by
  simp only [dagStateOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  exact ⟨List.nodup_iff_length_dedup_eq.mpr ok.1, ok.2⟩

def dagCheckNode (mask goal : Word) (chart : Option RowChart) (cut : CutCheck)
    (count : Nat) (states : Nat → Option RowState) (moves : Array WordMove) (links : DagLinks)
    (sample : DagSample) (tags : Nat → List DagSignals) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, history) => dagForceWords ws (fun forced =>
      dagStateOK mask forced && dagCheckChildren mask goal chart cut
        (dagRef count states moves links (i+1)) (fuel, forced, history) sample (tags i))

def dagCheckRoots (mask goal : Word) (chart : Option RowChart) (cut : CutCheck)
    (witnesses : List Witness) (reference : Nat → RowState → Bool) (stock : List Word)
    (fuel : Nat) : Bool :=
  treeBlock 0 (2^stock.length) fun token =>
    let state := rootState stock fuel token
    !dagAllowedRoot witnesses state.2.1 || dagLocal mask goal chart cut state || reference token state

theorem dagLocalOpen {mask goal : Word} {chart : Option RowChart}
    {cut : CutCheck} {state : RowState}
    (masked : Masked mask goal) (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (viable : WordViable mask goal state) (noCut : cut state = false) :
    dagLocal mask goal chart cut state = false := by
  obtain ⟨fuel,ws,history⟩ := state
  have ⟨nd,k,t,cap,live⟩ := viable
  change k ≤ fuel at cap
  have card := (liveWordSize live).2
  rw [List.toFinset_card_of_nodup nd] at card
  change ws.length + t ≤ k + 1 at card
  have fit : ¬ ws.length > fuel + 1 := by omega
  by_cases hz : fuel = 0
  · have kz : k = 0 := by omega
    subst k
    obtain ⟨_,eq,_⟩ := live
    have hm : goal ∈ ws := List.mem_toFinset.mp (by rw [eq]; simp)
    simp [dagLocal, fit, hm]
  by_cases tight : ws.length = fuel + 1
  · have ht : t = 0 := by omega
    subst t
    have dir := dagPartitionLive (directed := true) masked live (fun _ => rfl)
    have noChart : chart.any (fun c => !PackedRect.rectOK1 (ws.map (chartWord c))) = false := by
      cases opt : chart with
      | none => rfl
      | some c =>
        have vt : WordViable mask goal (fuel,ws,[]) := viable
        have ok := tightChart (chartOK c opt) tight vt
        simp [ok]
    simp [dagLocal, fit, hz, tight, dir, noCut, noChart]
  · have sep := dagPartitionLive (directed := false) masked live (by simp)
    simp [dagLocal, fit, hz, tight, sep, noCut]

theorem dagInsertLength (w : Word) (ws : List Word) :
    (insertWord w ws).length = ws.length + 1 := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    change (if w ≤ a then w :: a :: ws else a :: insertWord w ws).length = _
    split <;> simp [ih]

theorem dagKeepLength (keep : Bool) (w : Word) (ws : List Word) :
    ws.length - (if keep then 0 else 1) ≤ (keepWord keep w ws).length := by
  cases keep
  · exact List.le_length_erase
  · simp [keepWord]

theorem dagWideChild {mask token : Nat} {state child : RowState}
    (eval : childState mask token state = some child)
    (wide : dagTooWide state.2.1.length state.1 token = true) :
    child.2.1.length > child.1 + 1 := by
  obtain ⟨fuel,ws,history⟩ := state
  let keep := token % 4
  let op := token / 4 % 3
  let i := token / (4 * 3 * 64)
  let j := token / (4 * 3) % 64
  let x := ws.getD i 0
  let y := ws.getD j 0
  let z := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
  let a := keep.testBit 0
  let b := op == 2 || keep.testBit 1
  let rest := keepWord b y (keepWord a x ws)
  let bad : Bool := fuel == 0 || j ≥ ws.length || (if op == 2 then i != j || keep ≥ 2 else i ≥ j)
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z,x,y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb,hs] at eval
  have eq : (fuel-1, insertWord z rest, (z,x,y) :: history) = child := by simpa [hb,hs] using eval
  rw [← eq]
  change (insertWord z rest).length > fuel - 1 + 1
  rw [dagInsertLength]
  have h1 := dagKeepLength a x ws
  have h2 := dagKeepLength b y (keepWord a x ws)
  have h : ws.length - (if a then 0 else 1) - (if b then 0 else 1) + 1 > fuel - 1 + 1 :=
    of_decide_eq_true wide
  dsimp only [rest]
  omega

theorem dagKeepMem {ws : List Word} {x w : Word} {keep : Bool}
    (nd : ws.Nodup) (h : w ∈ keepWord keep x ws) : w ∈ ws ∧ (keep = true ∨ w ≠ x) := by
  cases keep
  · simpa [keepWord, nd.mem_erase_iff, and_comm] using h
  · simpa [keepWord] using h

theorem dagKeepNodup {ws : List Word} (nd : ws.Nodup) (keep : Bool) (x : Word) :
    (keepWord keep x ws).Nodup := by
  cases keep
  · exact nd.erase x
  · exact nd

theorem dagPackedPairSound {mask goal out : Word} {ws : List Word} {directed : Bool}
    {pairs : List Nat} {a b : Nat} {left right : Bool}
    (nd : ws.Nodup)
    (checked : dagPackedPair mask goal (dagPackWords ws) (dagLaneMarks ws.length)
      (dagOmitted a b left right) out directed pairs = true) :
    dagPairReject mask goal directed
      (out :: keepWord right (ws.getD b 0) (keepWord left (ws.getD a 0) ws)) pairs = true := by
  obtain ⟨code,mem,verdict⟩ := List.any_eq_true.mp checked
  apply List.any_eq_true.mpr
  refine ⟨code,mem,?_⟩
  simp only [dagForceWordEq, Bool.and_eq_true, Nat.blt_eq] at verdict
  obtain ⟨⟨⟨⟨⟨⟨hp, hn⟩, neg⟩, wp⟩, wn⟩, output⟩, closure⟩ := verdict
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨
    Bool.and_eq_true_iff.mpr ⟨hp,hn⟩,neg⟩,List.all_eq_true.mpr ?_⟩
  intro w hw
  rcases List.mem_cons.mp hw with rfl | later
  · exact output
  have rightMem := dagKeepMem (dagKeepNodup nd left (ws.getD a 0)) later
  have leftMem := dagKeepMem nd rightMem.1
  obtain ⟨i,inside,eq⟩ := List.mem_iff_getElem.mp leftMem.1
  have atIndex : ws.getD i 0 = w := by
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside] using eq
  have omitted : (dagOmitted a b left right).testBit (512*i) = false := by
    have cleared (j : Nat) (keep : Bool) (h : keep = true ∨ w ≠ ws.getD j 0) :
        (if keep then 0 else 1 <<< (512*j)).testBit (512*i) = false := by
      rcases h with yes | diff
      · simp [yes]
      · have ne : i ≠ j := fun same => diff (same ▸ atIndex).symm
        cases keep <;> simp [Nat.shiftLeft_eq, Nat.testBit_two_pow, show 512*j ≠ 512*i by omega]
    simp [dagOmitted, Nat.testBit_or, cleared a left leftMem.2, cleared b right rightMem.2]
  let p := code &&& 511
  let n := code >>> 9
  let marks := dagLaneMarks ws.length
  let signal := dagPackWords ws
  have mark : marks.testBit (512*i) = true := dagMarkBits inside
  have test {j : Nat} (within : j < 512) :
      ((signal >>> j) &&& marks).testBit (512*i) = w.testBit j := by
    rw [Nat.testBit_and, Nat.testBit_shiftRight, mark, Bool.and_true,
      Nat.add_comm j, dagPackBits inside within, atIndex]
  have h := congrArg (fun word => Nat.testBit word (512*i)) (Nat.beq_eq.mp closure)
  simp only [Nat.zero_testBit] at h
  change (((if directed then (signal >>> p &&& marks) &&& ((signal >>> n &&& marks) ^^^ marks)
      else (signal >>> p &&& marks) ^^^ (signal >>> n &&& marks)) &&&
    (marks ^^^ dagOmitted a b left right)).testBit (512*i)) = false at h
  have pt := test (j := p) wp
  have nt := test (j := n) wn
  cases directed <;> cases px : w.testBit p <;> cases nx : w.testBit n <;>
    simp [px,nx,pt,nt,Nat.testBit_and,Nat.testBit_xor,mark,omitted,p,n] at h ⊢

theorem dagEarlyOpen {mask goal a b op keep out : Nat} {state child : RowState}
    (masked : Masked mask goal) (viable : WordViable mask goal child)
    (parent : state.2.1.Nodup) (eval : dagDirectChild mask state a b op keep
      (state.2.1.getD a 0) (state.2.1.getD b 0) out = some child) (pairs : List Nat) :
    dagPackedPair mask goal (dagPackWords state.2.1) (dagLaneMarks state.2.1.length)
      (dagOmitted a b (keep.testBit 0) (op == 2 || keep.testBit 1)) out
      (dagSizeFloor state.2.1.length op keep == (state.1-1)+1) pairs = false := by
  obtain ⟨fuel,ws,history⟩ := state
  let x := ws.getD a 0
  let y := ws.getD b 0
  apply Bool.eq_false_iff.mpr
  intro closed
  have closed := dagPackedPairSound parent closed
  let bad : Bool := fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b)
  let stale : Bool := out == 0 || out == mask || ws.contains out
  let bank := dagKept ws op keep x y
  change (if bad then none else if stale then none else
    some (fuel-1, insertWord out bank, (out,x,y)::history)) = some child at eval
  by_cases h : bad = true
  · simp [h] at eval
  by_cases h' : stale = true
  · simp [h,h'] at eval
  have eq : (fuel-1,insertWord out bank,(out,x,y)::history) = child := by simpa [h,h'] using eval
  subst child
  obtain ⟨nd,k,t,cap,live⟩ := viable
  change k ≤ fuel-1 at cap
  have size := (liveWordSize live).2
  change (insertWord out bank : List Word).toFinset.card + t ≤ k+1 at size
  rw [List.toFinset_card_of_nodup nd, dagInsertLength] at size
  have same : (out::bank).toFinset = (insertWord out bank).toFinset := by
    ext w
    simp only [List.mem_toFinset, List.mem_cons, insertWordMem]
  have openBank := dagPairsOpen (pairs := pairs)
    (directed := dagSizeFloor ws.length op keep == (fuel-1)+1) masked (show LiveWord mask goal k t (out::bank).toFinset by rwa [same])
  have available : (dagSizeFloor ws.length op keep == (fuel-1)+1) = true → t = 0 := by
    intro directed
    have exactBudget := beq_iff_eq.mp directed
    have first := dagKeepLength (keep.testBit 0) x ws
    have second := dagKeepLength (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
    change dagSizeFloor ws.length op keep = (fuel-1)+1 at exactBudget
    unfold dagSizeFloor at exactBudget
    dsimp only [bank, dagKept] at size
    omega
  have refuses := openBank available
  exact Bool.noConfusion (closed.symm.trans refuses)

theorem dagChildAt {mask goal : Word} {chart : Option RowChart}
    {cut : CutCheck} {ref : Nat → RowState → Bool} {state child : RowState} {sample : DagSample} {tags : List DagSignals} {a b op keep : Nat}
    (checked : dagCheckChildren mask goal chart cut ref state sample tags = true)
    (ha : a < state.2.1.length)
    (legal : (a = b ∧ op = 2 ∧ keep < 2) ∨ (a < b ∧ b < state.2.1.length ∧ op < 2 ∧ keep < 4))
    (eval : childState mask (gateToken a b op keep) state = some child)
    (masked : Masked mask goal) (viable : WordViable mask goal child) (nd : state.2.1.Nodup)
    (openChild : dagLocal mask goal chart cut child = false) :
    ref (gateToken a b op keep) child = true := by
  have narrow : dagTooWide state.2.1.length state.1 (gateToken a b op keep) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have tooMany := dagWideChild eval h
    obtain ⟨f,w,path⟩ := child
    simp [dagLocal, tooMany] at openChild
  simp only [dagCheckChildren, dagForceCacheEq, dagForceWordEq, dagCountSignsEq,
    Bool.and_eq_true, decide_eq_true_eq] at checked
  have width := checked.1.1
  have atA := treeBlock_at checked.2 (i := a) (Nat.zero_le _) (by simpa using ha)
  rcases Bool.and_eq_true_iff.mp atA with ⟨unary,binary⟩
  rcases legal with ⟨rfl,rfl,hk⟩ | ⟨ab,hb,hop,hk⟩
  · have atKeep := treeBlock_at unary (i := keep) (Nat.zero_le _) (by simpa using hk)
    have fields := dagDirectChildEq (mask := mask) (state := state) (a := a) (b := a) (op := 2)
      (keep := keep) (by omega) (by decide) (by omega)
    have direct := fields.trans eval
    have early := dagEarlyOpen masked viable nd direct
    rcases child with ⟨fuel,ws,history⟩
    simpa only [narrow,Bool.false_eq_true,ite_false,fields,eval,dagForceWordsEq,early,openChild,Bool.or_false] using atKeep
  · have atB := treeBlock_at binary (i := b) (by omega) (by omega)
    have atOp := treeBlock_at atB (i := op) (Nat.zero_le _) (by simpa using hop)
    have atKeep := treeBlock_at atOp (i := keep) (Nat.zero_le _) (by simpa using hk)
    have fields := dagDirectChildEq (mask := mask) (state := state) (a := a) (b := b) (op := op)
      (keep := keep) (by omega) (by omega) hk
    have direct := fields.trans eval
    have early := dagEarlyOpen masked viable nd direct
    rcases child with ⟨fuel,ws,history⟩
    simpa only [narrow,Bool.false_eq_true,ite_false,fields,eval,dagForceWordsEq,early,openChild,Bool.or_false] using atKeep

theorem readWordMasked {mask : Word} {ws : List Word}
    (all : ∀ w ∈ ws, Masked mask w) (i : Nat) : Masked mask (ws.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => simp [Masked]
  | some w => exact all w (List.mem_of_getElem? h)

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

abbrev DagMoveRecord (width : Nat) := WordMove × (Fin width → Fin width) × (Fin width → Fin width)

def dagMoves (cert : List (DagMoveRecord width)) : Array WordMove := (cert.map Prod.fst).toArray

def dagMoveRecordProps {width : Nat} (mask goal : Word) (entry : DagMoveRecord width) : Prop :=
  let (move, select, inverse) := entry
  (∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal

def dagMoveRecordOK {width : Nat} (mask goal : Word) (entry : DagMoveRecord width) : Bool :=
  let (move, select, inverse) := entry
  decide ((∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal)

theorem dagMoveRecordSpec {width : Nat} {mask goal : Word} {entry : DagMoveRecord width}
    (ok : dagMoveRecordOK mask goal entry = true) : dagMoveRecordProps mask goal entry := by
  rcases entry with ⟨move,select,inverse⟩
  unfold dagMoveRecordProps
  exact of_decide_eq_true ok

theorem dagMovesOfCheck {width : Nat} {mask goal : Word} {cert : List (DagMoveRecord width)}
    (ok : cert.all (dagMoveRecordOK mask goal) = true) :
    DagMovesOK mask goal width (dagMoves cert) := by
  intro i m get
  simp only [dagMoves, List.getElem?_toArray, List.getElem?_map] at get
  cases e : cert[i]? with
  | none => simp [e] at get
  | some entry =>
    have eq : entry.1 = m := by simpa [e] using get
    rcases entry with ⟨move,select,inverse⟩
    obtain ⟨left,right,bm,gm,basis,mm,mg⟩ :=
      dagMoveRecordSpec (List.all_eq_true.mp ok _ (List.mem_of_getElem? e))
    subst m
    exact ⟨select, dagAutoFromMove left right bm gm basis mm mg⟩

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

theorem dagAllNodes {mask goal : Word} {width fuel count : Nat}
    {stock : List Word} {chart : Option RowChart}
    {cut : CutCheck} {forest : Forest} {moves : Array WordMove} {links : DagLinks} {sample : DagSample}
    {tags : Nat → List DagSignals}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal)
    (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (cutSound : ∀ s, WordViable mask goal s → cut s = false)
    (autos : DagMovesOK mask goal width moves)
    (verified : treeBlock 0 count (dagCheckNode mask goal chart cut count
      (dagTrace mask stock fuel forest) moves links sample tags) = true):
    ∀ cap i saved, i < count → dagTrace mask stock fuel forest i = some saved →
      saved.1 = cap → ∀ k t, k ≤ cap → ¬LiveWord mask goal k t saved.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i s iBound stateEq sFuel k t kBound live
    rcases s with ⟨remaining, words, history⟩
    let s : RowState := (remaining, words, history)
    let states := dagTrace mask stock fuel forest
    change states i = some s at stateEq
    have checked := treeBlock_at verified (Nat.zero_le i) (by simpa using iBound)
    change dagCheckNode mask goal chart cut count states moves links sample tags i = true at checked
    simp only [dagCheckNode, stateEq, dagForceWordsEq, Bool.and_eq_true] at checked
    obtain ⟨nd,masked⟩ := dagStateOKSpec checked.1
    have ok := checked.2
    have viable : WordViable mask goal s := ⟨nd,k,t,sFuel ▸ kBound,live⟩
    have scanned := ok
    simp only [dagCheckChildren, Bool.and_eq_true, decide_eq_true_eq] at scanned
    have wide := scanned.1.1
    have absent := scanned.1.2
    rcases wordProgress wide viable with hit | ⟨child, possible, cv⟩
    · simpa [hit] using absent
    obtain ⟨a,b,op,keep,ha,legal,eval⟩ := possible
    have r := dagChildAt ok ha legal eval goalMask cv nd (dagLocalOpen goalMask chartOK cv (cutSound _ cv))
    have ⟨less,cm⟩ := childStateData eval masked
    have below : child.1 < cap := sFuel ▸ less
    obtain ⟨_,k',t',fits,clive⟩ := cv
    obtain ⟨j,dest,bound,restore,fuelEq,tail⟩ :=
      dagLinked maskBounds autos cm r clive
    exact ih child.1 below j dest bound restore fuelEq k' t' fits tail

theorem lowerDag {mask goal : Word} {width fuel count : Nat}
    {stock : List Word} {chart : Option RowChart}
    {forest : Forest} {moves : Array WordMove} {links : DagLinks} {sample : DagSample}
    {tags : Nat → List DagSignals}
    {bounds : List Bound} {witnesses : List Witness}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal) (proper : properWord mask goal)
    (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (autos : DagMovesOK mask goal width moves)
    (stockMasked : ∀ w ∈ stock, Masked mask w) (stockNd : stock.Nodup)
    (essential : witnesses.all (essentialB mask goal stock) = true)
    (known : Known bounds) (submasks : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (rootCheck : dagCheckRoots mask goal chart (dagKnownCloses goal bounds) witnesses
      (dagRef count (dagTrace mask stock fuel forest) moves links 0)
      stock fuel = true)
    (nodeCheck : treeBlock 0 count (dagCheckNode mask goal chart (dagKnownCloses goal bounds)
      count (dagTrace mask stock fuel forest) moves links sample tags) = true) :
    Lower mask stock goal (fuel+1) := by
  intro values build hit
  by_contra! small
  obtain ⟨k,t,S,hk,live,sub⟩ := extractWordLive stockMasked build hit proper
  have included : S ⊆ stock.toFinset := fun w hw => List.mem_toFinset.mpr (sub w hw)
  obtain ⟨token,tokenBound,eq⟩ := rootToken stock S
  rw [Finset.inter_eq_right.mpr included] at eq
  let state := rootState stock fuel token
  have eq' : state.2.1.toFinset = S := eq
  have v : WordViable mask goal state := by
    refine ⟨(rootWordSublist stock token).nodup stockNd,k,t,?_,?_⟩
    · change k ≤ fuel
      omega
    · rwa [eq']
  have cutOpen (s : RowState) (h : WordViable mask goal s) : dagKnownCloses goal bounds s = false := by
    rw [dagKnownClosesEq]
    exact knownClosesSound known submasks h
  have openRoot := dagLocalOpen goalMask chartOK v (cutOpen _ v)
  have allowed : dagAllowedRoot witnesses state.2.1 = true := by
    apply List.all_eq_true.mpr
    intro entry mem
    apply List.contains_iff_mem.mpr
    rw [← List.mem_toFinset, eq']
    exact essentialRequired (List.all_eq_true.mp essential entry mem) sub live
  have checked := treeBlock_at rootCheck (Nat.zero_le token) (by simpa using tokenBound)
  change (!dagAllowedRoot witnesses state.2.1 || dagLocal mask goal chart (dagKnownCloses goal bounds) state ||
    dagRef count (dagTrace mask stock fuel forest) moves links 0 token state) = true at checked
  simp only [allowed,openRoot,Bool.not_true,Bool.false_or] at checked
  have finish := dagAllNodes maskBounds goalMask chartOK cutOpen autos nodeCheck
  have fits : k ≤ fuel := by omega
  have still : LiveWord mask goal k t state.2.1.toFinset := by rwa [eq']
  have stateMask : ∀ w ∈ state.2.1, Masked mask w := by
    intro w hw
    exact stockMasked _ ((rootWordSublist stock token).subset hw)
  obtain ⟨i,s,hi,restore,cap,plan⟩ := dagLinked maskBounds autos stateMask checked still
  exact finish fuel i s hi restore cap k t fits plan

def dagLookupLinks (index data indexWidth sizeBits tokenBits destinationBits autoBits trials : Nat) :
    DagLinks := fun parent token =>
  let entry := unpack index indexWidth parent
  let size := entry &&& ((1 <<< sizeBits) - 1)
  let offset := entry >>> sizeBits
  let width := tokenBits + destinationBits + autoBits
  (Nat.rec (motive := fun _ => Nat → Nat → Option DagLink) (fun _ _ => none)
    (fun _ next lo hi =>
      if Nat.blt lo hi then
        let mid := (lo+hi)/2
        let code := unpack data width mid
        let key := code &&& ((1 <<< tokenBits) - 1)
        if Nat.beq token key then
          some ((code >>> tokenBits) &&& ((1 <<< destinationBits) - 1),
            code >>> (tokenBits + destinationBits))
        else if Nat.blt token key then next lo mid else next (mid+1) hi
      else none) trials) offset (offset+size)

def projectDAGStock (mask : Word) (source : List Word) (indices : List Nat) : List Word :=
  List.rec [] (fun i _ rest => (mask &&& source.getD i 0) :: rest) indices

theorem stockMaskedOfCheck {mask : Word} {stock : List Word}
    (h : stock.all (fun w => w &&& mask == w) = true) :
    ∀ w ∈ stock, Masked mask w := by
  intro w hw
  exact beq_iff_eq.mp (List.all_eq_true.mp h w hw)

theorem suppliesOfCheck {oldMask : Word} {old new : List Word} {rename : Word → Word}
    (h : new.all (fun w => availableB oldMask old (rename w)) = true) :
    ∀ w ∈ new, AvailableWord oldMask old (rename w) := by
  intro w hw
  exact availableB_spec.mp (List.all_eq_true.mp h w hw)

def dagShift (mask : Word) (move : WordMove) (word : Word) : Word :=
  mixMove move (word &&& mask)

def dagShiftUnique (mask : Word) (move : WordMove) : Nat → Word → Bool :=
  Nat.rec (fun _ => true) (fun i next occupied =>
    if mask.testBit i then
      dagForceWord (mixMove move (2^i)) (fun col =>
        Nat.beq (col &&& occupied) 0 && dagForceWord (occupied ||| col) next)
    else next occupied)

theorem dagShiftLinear (mask : Word) (move : WordMove) : BitLinear (dagShift mask move) := by
  apply bitLinearComp (mixMoveLinear move)
  simpa using bitLinearRight mask 0

theorem dagShiftBasis (mask : Word) (move : WordMove) (i : Nat) :
    dagShift mask move (2 ^ i) = if mask.testBit i then mixMove move (2^i) else 0 := by
  have select : 2 ^ i &&& mask = if mask.testBit i then 2^i else 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases same : i = j
    · subst j
      simp only [Nat.testBit_and, Nat.testBit_two_pow, decide_true, Bool.true_and]
      cases mask.testBit i <;> simp
    · cases h : mask.testBit i <;> simp [Nat.testBit_and, Nat.testBit_two_pow, same, h]
  rw [dagShift, select]
  split
  · rfl
  · apply Nat.eq_of_testBit_eq
    intro j
    apply Bool.eq_iff_iff.mpr
    rw [mixMoveLinear]
    simp

theorem dagShiftUniqueSpec {mask : Word} {move : WordMove} {n : Nat} {occupied : Word}
    (ok : dagShiftUnique mask move n occupied = true) :
    (∀ j < n, ∀ b, (dagShift mask move (2^j)).testBit b = true → occupied.testBit b = false) ∧
    (∀ j < n, ∀ k < n, ∀ b, (dagShift mask move (2^j)).testBit b = true →
      (dagShift mask move (2^k)).testBit b = true → j = k) := by
  induction n generalizing occupied with
  | zero => simp
  | succ n ih =>
    let col := mixMove move (2^n)
    change (if mask.testBit n then dagForceWord col (fun w =>
      Nat.beq (w &&& occupied) 0 && dagForceWord (occupied ||| w) (dagShiftUnique mask move n))
      else dagShiftUnique mask move n occupied) = true at ok
    cases active : mask.testBit n
    · simp [active,dagForceWordEq] at ok
      obtain ⟨existing,unique⟩ := ih ok
      have dead : dagShift mask move (2^n) = 0 := by simp [dagShiftBasis,active]
      refine ⟨?_,?_⟩
      · intro j hj b h
        by_cases same : j = n
        · simp [same,dead] at h
        · exact existing j (by omega) b h
      · intro j hj k hk b a c
        by_cases e : j = n
        · simp [e,dead] at a
        by_cases e' : k = n
        · simp [e',dead] at c
        exact unique j (by omega) k (by omega) b a c
    · simp only [active,ite_true,dagForceWordEq,Bool.and_eq_true] at ok
      have disjoint := Nat.beq_eq.mp ok.1
      obtain ⟨existing,unique⟩ := ih ok.2
      have colEq : dagShift mask move (2^n) = col := by simp [dagShiftBasis,active,col]
      have old {j b : Nat} (hj : j < n) (h : (dagShift mask move (2^j)).testBit b = true) :
          occupied.testBit b = false ∧ col.testBit b = false := by
        simpa [Nat.testBit_or, Bool.or_eq_false_iff] using existing j hj b h
      refine ⟨?_,?_⟩
      · intro j hj b h
        by_cases same : j = n
        · rw [same,colEq] at h
          have bit := congrArg (fun w => Nat.testBit w b) disjoint
          simpa [Nat.testBit_and,h] using bit
        · exact (old (by omega) h).1
      · intro j hj k hk b a c
        by_cases e : j = n
        · by_cases e' : k = n
          · exact e.trans e'.symm
          · rw [e,colEq,(old (by omega) c).2] at a
            contradiction
        by_cases e' : k = n
        · rw [e',colEq,(old (by omega) a).2] at c
          contradiction
        exact unique j (by omega) k (by omega) b a c

theorem dagShiftGates {mask : Word} {move : WordMove} {width : Nat}
    (bounded : Masked (fullMask width) mask) (checked : dagShiftUnique mask move width 0 = true) :
    (∀ a b, dagShift mask move (a &&& b) = dagShift mask move a &&& dagShift mask move b) ∧
    (∀ a b, dagShift mask move (a ||| b) = dagShift mask move a ||| dagShift mask move b) ∧
    (∀ a b, dagShift mask move (a ^^^ b) = dagShift mask move a ^^^ dagShift mask move b) := by
  let f := dagShift mask move
  have lin := dagShiftLinear mask move
  have uniq {j k i : Nat} (hj : (f (2^j)).testBit i = true) (hk : (f (2^k)).testBit i = true) : j = k := by
    have within {m : Nat} (a : (f (2^m)).testBit i = true) : m < width := by
      by_contra! big
      have eq := congrArg (fun w => Nat.testBit w m) bounded
      have zero : mask.testBit m = false := by
        simpa [Masked,fullMask,Nat.testBit_and,Nat.testBit_two_pow_sub_one,show ¬m < width by omega] using eq.symm
      simp [f,dagShiftBasis,zero] at a
    exact (dagShiftUniqueSpec checked).2 j (within hj) k (within hk) i hj hk
  refine ⟨?_,?_,?_⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [Nat.testBit_and, Bool.and_eq_true, lin, lin, lin]
    constructor
    · rintro ⟨j,hj,h⟩
      rw [Nat.testBit_and, Bool.and_eq_true] at hj
      exact ⟨⟨j,hj.1,h⟩,⟨j,hj.2,h⟩⟩
    · rintro ⟨⟨j,hj,q⟩,⟨k,hk,r⟩⟩
      have same := uniq q r
      subst k
      exact ⟨j,by simp [Nat.testBit_and,hj,hk],q⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [lin (a ||| b) i, Nat.testBit_or, Bool.or_eq_true, lin a i, lin b i]
    simp only [Nat.testBit_or, Bool.or_eq_true]
    constructor
    · rintro ⟨j,(left | right),same⟩
      · exact Or.inl ⟨j,left,same⟩
      · exact Or.inr ⟨j,right,same⟩
    · rintro (⟨j,left,same⟩ | ⟨j,right,same⟩)
      · exact ⟨j,Or.inl left,same⟩
      · exact ⟨j,Or.inr right,same⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    have l := lin a i
    have r := lin b i
    have v := lin (a ^^^ b) i
    cases pa : (f a).testBit i <;> cases pb : (f b).testBit i
    · rw [Nat.testBit_xor,pa,pb]
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,hj,h⟩ := v.mp yes
      have disj : a.testBit j = true ∨ b.testBit j = true := by
        rw [Nat.testBit_xor] at hj
        cases aj : a.testBit j <;> cases bj : b.testBit j <;> simp [aj,bj] at hj ⊢
      rcases disj with da | db
      · have := l.mpr ⟨j,da,h⟩
        change (f a).testBit i = true at this
        simp [pa] at this
      · have := r.mpr ⟨j,db,h⟩
        change (f b).testBit i = true at this
        simp [pb] at this
    · rw [Nat.testBit_xor,pa,pb]
      apply v.mpr
      obtain ⟨j,hj,h⟩ := r.mp pb
      have notA : a.testBit j = false := Bool.eq_false_iff.mpr (fun yes => by
        have := l.mpr ⟨j,yes,h⟩
        change (f a).testBit i = true at this
        simp [pa] at this)
      exact ⟨j,by simp [Nat.testBit_xor,notA,hj],h⟩
    · rw [Nat.testBit_xor,pa,pb]
      apply v.mpr
      obtain ⟨j,hj,h⟩ := l.mp pa
      have notB : b.testBit j = false := Bool.eq_false_iff.mpr (fun yes => by
        have := r.mpr ⟨j,yes,h⟩
        change (f b).testBit i = true at this
        simp [pb] at this)
      exact ⟨j,by simp [Nat.testBit_xor,hj,notB],h⟩
    · rw [Nat.testBit_xor,pa,pb]
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,hj,h⟩ := v.mp yes
      obtain ⟨a',ha,q⟩ := l.mp pa
      obtain ⟨b',hb,r⟩ := r.mp pb
      have ea := uniq h q
      have eb := uniq h r
      rw [← ea] at ha
      rw [← eb] at hb
      simp [Nat.testBit_xor,ha,hb] at hj

def dagShiftCheck (width mask goal oldMask oldGoal : Word) (stock old : List Word) (move : WordMove) : Bool :=
  Nat.beq (mask &&& fullMask width) mask && dagShiftUnique mask move width 0 &&
    Nat.beq (dagShift mask move mask) oldMask && Nat.beq (dagShift mask move goal) oldGoal &&
    stock.all (fun w => availableB oldMask old (dagShift mask move w))

theorem dagShiftLower {width mask goal oldMask oldGoal : Word} {stock old : List Word} {min : Nat}
    (move : WordMove) (origin : Lower oldMask old oldGoal min)
    (ok : dagShiftCheck width mask goal oldMask oldGoal stock old move = true) :
    Lower mask stock goal min := by
  simp only [dagShiftCheck,Bool.and_eq_true,Nat.beq_eq] at ok
  obtain ⟨⟨⟨⟨bounded,unique⟩,masks⟩,goals⟩,supply⟩ := ok
  obtain ⟨andG,orG,xorG⟩ := dagShiftGates bounded unique
  have zero : dagShift mask move 0 = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    apply Bool.eq_iff_iff.mpr
    rw [dagShiftLinear]
    simp
  apply lowerMap (dagShift mask move) zero masks (fun w => by rw [xorG,masks]) andG orG (suppliesOfCheck supply)
  rwa [goals]

def moveSchedule (stages : Array WordMoveStep) (indices : List Nat) : WordMove :=
  List.rec [] (fun i _ rest => stages[i]?.getD ([],[]) :: rest) indices

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

theorem hcsGateWord {rows : Nat} (bank : List (BitVec rows))
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp))
    (hlen : g.inputs.length ≤ 2) :
    GateWord (fullMask rows) (bank.map BitVec.toNat) (hcsGateVal bank g).toNat := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have zeroAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) 0 := Or.inl rfl
  have maskAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) (fullMask rows) :=
    Or.inr (Or.inl rfl)
  rcases hop with rfl | rfl | rfl
  · cases ins with
    | nil => exact gateOfAvailable (by simpa [hcsGateVal, fullMask] using maskAv)
    | cons a t =>
      cases t with
      | nil => exact gateOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact Or.inr ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inl (by simp [hcsGateVal, BitVec.toNat_and])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact gateOfAvailable (by simpa [hcsGateVal] using zeroAv)
    | cons a t =>
      cases t with
      | nil => exact gateOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact Or.inr ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inr (by simp [hcsGateVal, BitVec.toNat_or])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact Or.inl ⟨0, zeroAv, by simpa [hcsGateVal] using notNat (0 : BitVec rows)⟩
    | cons a _ => exact Or.inl ⟨_, toNatAvailable bank a, by simpa [hcsGateVal] using notNat (bank.getD a 0)⟩

theorem hcsBuilds {rows : Nat} (bank : List (BitVec rows))
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    ∃ vs, vs.length = gs.length ∧ WordBuilds (fullMask rows) (bank.map BitVec.toNat) vs ∧
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
    refine ⟨v.toNat :: xs, by simp [len], ⟨hcsGateWord bank g hg.1 hg.2, buildsWeaken ?_ build⟩, ?_⟩
    · intro u hu; exact Or.inr (Or.inr (by simpa [or_comm] using hu))
    · intro u hu; have m := sub u hu; rw [eq] at m
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using m

def hcsCheckPow (p : Nat → Bool) : Nat → Nat → Bool
  | 0, s => p s
  | k + 1, s => hcsCheckPow p k s && hcsCheckPow p k (s + 2 ^ k)

theorem hcsCheckPow_spec {p : Nat → Bool} {k s i : Nat}
    (h : hcsCheckPow p k s = true) (lo : s ≤ i) (hi : i < s + 2 ^ k) : p i = true := by
  induction k generalizing s with
  | zero =>
    have e : i = s := by omega
    simpa [hcsCheckPow, e] using h
  | succ k ih =>
    simp only [hcsCheckPow, Bool.and_eq_true] at h
    by_cases hlt : i < s + 2 ^ k
    · exact ih h.1 lo hlt
    · exact ih h.2 (by omega) (by rw [Nat.pow_succ] at hi; omega)

theorem hcsLowerEq {m1 m2 g1 g2 min : Nat} {b1 b2 : List Word}
    (hm : m1 = m2) (hb : b1 = b2) (hg : g1 = g2)
    (h : Lower m1 b1 g1 min) : Lower m2 b2 g2 min := by
  subst hm; subst hb; subst hg; exact h

theorem hcsLower {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n)) (min : Nat)
    (f : (Fin n → Bool) → Bool)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin n => r.testBit j.val) n 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f (fun j : Fin n => r.testBit j.val)) n 0 = true)
    (claim : Lower (fullMask (2 ^ n)) (raw.map BitVec.toNat) goal.toNat min)
    (t : Nat) (h : PEqualNP.MetaComplexity.HasCircuitSize n f t) : min ≤ t := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  obtain ⟨vs, len, built, sub⟩ := hcsBuilds raw C.gates hfan
  let eb := C.gates.foldl hcsStep raw
  have same : eb.getD C.output 0 = goal := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let y : Fin n → Bool := fun k => j.testBit k.val
    have hbank : raw.map (fun v => v.getLsbD j) = List.ofFn y :=
      beq_iff_eq.mp (hcsCheckPow_spec hRaw (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
    have hfg : goal.getLsbD j = f y :=
      beq_iff_eq.mp (hcsCheckPow_spec hGoal (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
    have hbits := hcsFoldBits raw ⟨j, hj⟩ C.gates hfan
    have hevj : (C.wires (List.ofFn y)).getD C.output false = f y := hev y
    change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
      (List.ofFn y)).getD C.output false = f y at hevj
    rw [← hbank, ← hbits] at hevj
    rw [hfg, ← hevj, ← hcsGetDBit]
  have av : AvailableWord (fullMask (2 ^ n)) (vs ++ raw.map BitVec.toNat) goal.toNat := by
    rw [← same, List.getD_eq_getElem?_getD]
    cases h : eb[C.output]? with
    | none => exact Or.inl rfl
    | some v => exact Or.inr (Or.inr (sub v (List.mem_of_getElem? h)))
  have lb := claim vs built av
  have hs : C.gates.length ≤ t := hsz
  omega

def moveStage0 : WordMoveStep := ([(0xffffffffffffffff0000000000000000ffffffffffffffff, 64)], [(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 64)])
def moveStage1 : WordMoveStep := ([(0x9999999999999999999999999999999999999999999999999999999999999999, 0), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x4444444444444444444444444444444444444444444444444444444444444444, 1)])
def moveStage2 : WordMoveStep := ([(0xff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ff, 0), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000, 24)])
def moveStage3 : WordMoveStep := ([(0xffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff, 0), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xffff000000000000ffff000000000000ffff000000000000ffff00000000, 16)])
def moveStage4 : WordMoveStep := ([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)])
def moveStage5 : WordMoveStep := ([(0xaa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55, 0), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0x5500550055005500550055005500550055005500550055005500550055005500, 7)])
def moveStage6 : WordMoveStep := ([(0xcc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33, 0), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0x3300330033003300330033003300330033003300330033003300330033003300, 6)])
def moveStage7 : WordMoveStep := ([(0xff00ff00ff00ff0000ff00ff00ff00ffff00ff00ff00ff0000ff00ff00ff00ff, 0), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000, 56)])
def moveStage8 : WordMoveStep := ([(0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff, 0), (0xffffffff000000000000000000000000ffffffff00000000, 32)], [(0xffffffff000000000000000000000000ffffffff0000000000000000, 32)])
def moveStage9 : WordMoveStep := ([(0xaaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555, 0), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0x5555555500000000555555550000000055555555000000005555555500000000, 31)])
def moveStage10 : WordMoveStep := ([(0xaaaaaaaaaaaaaaaa5555555555555555aaaaaaaaaaaaaaaa5555555555555555, 0), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0x5555555555555555000000000000000055555555555555550000000000000000, 63)])
def moveStage11 : WordMoveStep := ([(0xffffffffffffffffffffffffffffffff, 128)], [(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128)])
def moveStage12 : WordMoveStep := ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])
def moveStage13 : WordMoveStep := ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)])
def moveStage14 : WordMoveStep := ([(0xf00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f, 0), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 4)])
def moveStages : Array WordMoveStep := #[moveStage0, moveStage1, moveStage2, moveStage3, moveStage4, moveStage5, moveStage6, moveStage7, moveStage8, moveStage9, moveStage10, moveStage11, moveStage12, moveStage13, moveStage14]
def sBase : List Word := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def sGoal : Word := 0xffffffffffffffffffffffffffeaeae8ffeeeeeeffeeeeecffeaeaeaffeaeae8
-- s0: K3_012 (lb=4, vars=3, kind=2)
def s0Mask : Word := 0xff
abbrev s0Goal : Word := sGoal &&& s0Mask
abbrev s0StockWords : List Word := projectDAGStock s0Mask sBase [0, 1, 2]
def s0Fact : Bound := (s0Mask, s0StockWords, 4, s0Goal)
def s0Witnesses := unpackWitnesses s0StockWords [1538, 263681, 526849]
def s0Cuts : List Bound := []
def s0Chart : Option RowChart := some ⟨[3, 5, 6, 7, 3, 5, 6, 7, 3, 5, 6, 7, 1, 2, 4, 0, 1, 2, 4, 0, 1, 2, 4, 0], rfl⟩
def s0Sample : DagSample := (0x201802050100c0406020140203, 6)
def s0Links : DagLinks :=
  dagLookupLinks 0x9 0x7 2 1 3 1 3 4
def s0Data : Forest := fun i => decodeNode 1 4 0xe i
def s0Tags := dagTraceTags s0Mask 6 (dagTagBases s0StockWords 0x36b5b 0x22311 6) 3 s0Data
def s0States := dagTrace s0Mask s0StockWords 3 s0Data
def s0Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s0Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 5, 6, 7] 0 i.val)
def s0Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 4, 3, 5, 6, 7] 0 i.val)
def s0Move3Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 5, 7] 0 i.val)
def s0MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s0Move0Map, s0Move0Map), ([([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)])], s0Move1Map, s0Move1Map), ([([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)]), ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s0Move2Map, s0Move2Map), ([([(0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff, 0), (0xffffffff000000000000000000000000ffffffff00000000, 32)], [(0xffffffff000000000000000000000000ffffffff0000000000000000, 32)])], s0Move3Map, s0Move3Map)]
def s0Moves := dagMoves s0MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Autos : DagMovesOK s0Mask s0Goal 256 s0Moves := dagMovesOfCheck (by decide +kernel)
def s0Check := dagCheckNode s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) 1 s0States s0Moves s0Links s0Sample s0Tags
def s0RootAt (token : Nat) : Bool :=
  let s := rootState s0StockWords 3 token
  !dagAllowedRoot s0Witnesses s.2.1 || dagLocal s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) s ||
  dagRef 1 s0States s0Moves s0Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0RootBlock0 : treeBlock 0 8 s0RootAt = true := by decide +kernel
theorem s0RootVerified : treeBlock 0 8 s0RootAt = true := s0RootBlock0
theorem s0Roots : dagCheckRoots s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) s0Witnesses (dagRef 1 s0States s0Moves s0Links 0) s0StockWords 3 = true := s0RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Block0 : treeBlock 0 1 s0Check = true := by decide +kernel
theorem s0Verified : treeBlock 0 1 s0Check = true := s0Block0
theorem s0Blocks : treeBlock 0 1 s0Check = true := s0Verified
theorem s0Known : Known s0Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Stock : Lower s0Mask s0StockWords s0Goal 4 := by
  apply lowerDag _ _ _ _ s0Autos _ _ _ s0Known _ s0Roots s0Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s0StockWords; decide +kernel
  · decide +kernel
  · simp only [s0Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
-- s1: K3_034 (lb=4, vars=3, kind=2)
def s1Mask : Word := 0x3030303
abbrev s1Goal : Word := sGoal &&& s1Mask
abbrev s1StockWords : List Word := projectDAGStock s1Mask sBase [0, 3, 4]
def s1Fact : Bound := (s1Mask, s1StockWords, 4, s1Goal)
def s1Witnesses := unpackWitnesses s1StockWords [4616, 266753, 532993]
def s1Cuts : List Bound := []
def s1Chart : Option RowChart := some ⟨[9, 17, 24, 25, 9, 17, 24, 25, 9, 17, 24, 25, 1, 8, 16, 0, 1, 8, 16, 0, 1, 8, 16, 0], rfl⟩
def s1Sample : DagSample := (0x80600211040241018080440209, 6)
def s1Links : DagLinks :=
  dagLookupLinks 0x9 0x7 2 1 3 1 3 4
def s1Data : Forest := fun i => decodeNode 1 4 0xe i
def s1Tags := dagTraceTags s1Mask 6 (dagTagBases s1StockWords 0x36b5b 0x22311 6) 3 s1Data
def s1States := dagTrace s1Mask s1StockWords 3 s1Data
def s1Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s1Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 5, 6, 7] 0 i.val)
def s1Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 4, 3, 5, 6, 7] 0 i.val)
def s1Move3Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 5, 2, 3, 4, 1, 7, 6] 0 i.val)
def s1Move4Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 5, 2, 4, 3, 1, 7, 6] 0 i.val)
def s1Move5Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 5, 7] 0 i.val)
def s1MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s1Move0Map, s1Move0Map), ([([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)])], s1Move1Map, s1Move1Map), ([([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)]), ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s1Move2Map, s1Move2Map), ([([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333, 0), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x3333333300000000333333330000000033333333000000003333333300000000, 30)]), ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)])], s1Move3Map, s1Move3Map), ([([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333, 0), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x3333333300000000333333330000000033333333000000003333333300000000, 30)]), ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)]), ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s1Move4Map, s1Move4Map), ([([(0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff, 0), (0xffffffff000000000000000000000000ffffffff00000000, 32)], [(0xffffffff000000000000000000000000ffffffff0000000000000000, 32)])], s1Move5Map, s1Move5Map)]
def s1Moves := dagMoves s1MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Autos : DagMovesOK s1Mask s1Goal 256 s1Moves := dagMovesOfCheck (by decide +kernel)
def s1Check := dagCheckNode s1Mask s1Goal s1Chart (dagKnownCloses s1Goal s1Cuts) 1 s1States s1Moves s1Links s1Sample s1Tags
def s1RootAt (token : Nat) : Bool :=
  let s := rootState s1StockWords 3 token
  !dagAllowedRoot s1Witnesses s.2.1 || dagLocal s1Mask s1Goal s1Chart (dagKnownCloses s1Goal s1Cuts) s ||
  dagRef 1 s1States s1Moves s1Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1RootBlock0 : treeBlock 0 8 s1RootAt = true := by decide +kernel
theorem s1RootVerified : treeBlock 0 8 s1RootAt = true := s1RootBlock0
theorem s1Roots : dagCheckRoots s1Mask s1Goal s1Chart (dagKnownCloses s1Goal s1Cuts) s1Witnesses (dagRef 1 s1States s1Moves s1Links 0) s1StockWords 3 = true := s1RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Block0 : treeBlock 0 1 s1Check = true := by decide +kernel
theorem s1Verified : treeBlock 0 1 s1Check = true := s1Block0
theorem s1Blocks : treeBlock 0 1 s1Check = true := s1Verified
theorem s1Known : Known s1Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Stock : Lower s1Mask s1StockWords s1Goal 4 := by
  apply lowerDag _ _ _ _ s1Autos _ _ _ s1Known _ s1Roots s1Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s1StockWords; decide +kernel
  · decide +kernel
  · simp only [s1Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
-- s2: P4_1675 (lb=4, vars=4, kind=2)
def s2Mask : Word := 0x500000005000000050000000500000005000000050000000500000005
abbrev s2Goal : Word := sGoal &&& s2Mask
abbrev s2StockWords : List Word := projectDAGStock s2Mask sBase [1, 5, 6, 7]
def s2Fact : Bound := (s2Mask, s2StockWords, 4, s2Goal)
def s2Witnesses := unpackWitnesses s2StockWords [33856, 344192, 558082, 868384]
def s2Cuts : List Bound := []
def s2Chart : Option RowChart := some ⟨[66, 160, 192, 98, 162, 194, 224, 226, 66, 160, 192, 98, 34, 96, 130, 2, 32, 64, 128, 0, 34, 96, 130, 2], rfl⟩
def s2Sample : DagSample := (0x42, 1)
def s2Links : DagLinks :=
  dagLookupLinks 0x0 0x0 2 1 1 1 2 3
def s2Data : Forest := fun i => decodeNode 1 5 0x0 i
def s2Tags := dagTraceTags s2Mask 1 (dagTagBases s2StockWords 0x5 0x0 1) 3 s2Data
def s2States := dagTrace s2Mask s2StockWords 3 s2Data
def s2Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s2Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 5, 2, 3, 4, 1, 7, 6] 0 i.val)
def s2Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 5, 2, 4, 3, 1, 7, 6] 0 i.val)
def s2MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s2Move0Map, s2Move0Map), ([([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333, 0), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x3333333300000000333333330000000033333333000000003333333300000000, 30)]), ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)])], s2Move1Map, s2Move1Map), ([([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333, 0), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x3333333300000000333333330000000033333333000000003333333300000000, 30)]), ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)]), ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s2Move2Map, s2Move2Map)]
def s2Moves := dagMoves s2MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Autos : DagMovesOK s2Mask s2Goal 256 s2Moves := dagMovesOfCheck (by decide +kernel)
def s2Check := dagCheckNode s2Mask s2Goal s2Chart (dagKnownCloses s2Goal s2Cuts) 0 s2States s2Moves s2Links s2Sample s2Tags
def s2RootAt (token : Nat) : Bool :=
  let s := rootState s2StockWords 3 token
  !dagAllowedRoot s2Witnesses s.2.1 || dagLocal s2Mask s2Goal s2Chart (dagKnownCloses s2Goal s2Cuts) s ||
  dagRef 0 s2States s2Moves s2Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2RootBlock0 : treeBlock 0 16 s2RootAt = true := by decide +kernel
theorem s2RootVerified : treeBlock 0 16 s2RootAt = true := s2RootBlock0
theorem s2Roots : dagCheckRoots s2Mask s2Goal s2Chart (dagKnownCloses s2Goal s2Cuts) s2Witnesses (dagRef 0 s2States s2Moves s2Links 0) s2StockWords 3 = true := s2RootVerified
theorem s2Blocks : treeBlock 0 0 s2Check = true := rfl
theorem s2Known : Known s2Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Stock : Lower s2Mask s2StockWords s2Goal 4 := by
  apply lowerDag _ _ _ _ s2Autos _ _ _ s2Known _ s2Roots s2Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s2StockWords; decide +kernel
  · decide +kernel
  · simp only [s2Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
-- s3: P5_21675 (lb=5, vars=5, kind=1)
def s3Mask : Word := 0x5500000055000000550000005500000055000000550000005500000055
abbrev s3Goal : Word := sGoal &&& s3Mask
abbrev s3StockWords : List Word := projectDAGStock s3Mask sBase [1, 2, 5, 6, 7]
def s3Fact : Bound := (s3Mask, s3StockWords, 5, s3Goal)
def s3Witnesses := unpackWitnesses s3StockWords [3076, 265218, 606336, 820226, 1130528]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s3Stock : Lower s3Mask s3StockWords s3Goal 5 := by
  apply essentialLift (witnesses := s3Witnesses) (cut := s2Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s2StockWords) (by decide +kernel)
  · exact s2Stock
  · decide +kernel
-- s4: C5_1=0 (lb=4, vars=4, kind=2)
def s4Mask : Word := 0x300000003000000030000000300000003000000030000000300000003
abbrev s4Goal : Word := sGoal &&& s4Mask
abbrev s4StockWords : List Word := projectDAGStock s4Mask sBase [0, 5, 6, 7]
def s4Fact : Bound := (s4Mask, s4StockWords, 4, s4Goal)
def s4Witnesses := unpackWitnesses s4StockWords [16928, 279041, 622720, 868384]
def s4Cuts : List Bound := []
def s4Chart : Option RowChart := some ⟨[33, 160, 192, 97, 161, 193, 224, 225, 33, 160, 192, 97, 65, 96, 129, 1, 32, 64, 128, 0, 65, 96, 129, 1], rfl⟩
def s4Sample : DagSample := (0x21, 1)
def s4Links : DagLinks :=
  dagLookupLinks 0x0 0x0 2 1 1 1 3 3
def s4Data : Forest := fun i => decodeNode 1 5 0x0 i
def s4Tags := dagTraceTags s4Mask 1 (dagTagBases s4StockWords 0x3 0x0 1) 3 s4Data
def s4States := dagTrace s4Mask s4StockWords 3 s4Data
def s4Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s4Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 5, 6, 7] 0 i.val)
def s4Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 4, 3, 5, 6, 7] 0 i.val)
def s4Move3Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 3, 4, 1, 2, 5, 6, 7] 0 i.val)
def s4Move4Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 3, 2, 1, 5, 6, 7] 0 i.val)
def s4MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s4Move0Map, s4Move0Map), ([([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)])], s4Move1Map, s4Move1Map), ([([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)]), ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s4Move2Map, s4Move2Map), ([([(0xcc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33, 0), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0x3300330033003300330033003300330033003300330033003300330033003300, 6)]), ([(0xf0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0f, 0), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000, 12)])], s4Move3Map, s4Move3Map), ([([(0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333, 0), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x3333000033330000333300003333000033330000333300003333000033330000, 14)]), ([(0xf00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f, 0), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 4)])], s4Move4Map, s4Move4Map)]
def s4Moves := dagMoves s4MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Autos : DagMovesOK s4Mask s4Goal 256 s4Moves := dagMovesOfCheck (by decide +kernel)
def s4Check := dagCheckNode s4Mask s4Goal s4Chart (dagKnownCloses s4Goal s4Cuts) 0 s4States s4Moves s4Links s4Sample s4Tags
def s4RootAt (token : Nat) : Bool :=
  let s := rootState s4StockWords 3 token
  !dagAllowedRoot s4Witnesses s.2.1 || dagLocal s4Mask s4Goal s4Chart (dagKnownCloses s4Goal s4Cuts) s ||
  dagRef 0 s4States s4Moves s4Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4RootBlock0 : treeBlock 0 16 s4RootAt = true := by decide +kernel
theorem s4RootVerified : treeBlock 0 16 s4RootAt = true := s4RootBlock0
theorem s4Roots : dagCheckRoots s4Mask s4Goal s4Chart (dagKnownCloses s4Goal s4Cuts) s4Witnesses (dagRef 0 s4States s4Moves s4Links 0) s4StockWords 3 = true := s4RootVerified
theorem s4Blocks : treeBlock 0 0 s4Check = true := rfl
theorem s4Known : Known s4Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Stock : Lower s4Mask s4StockWords s4Goal 4 := by
  apply lowerDag _ _ _ _ s4Autos _ _ _ s4Known _ s4Roots s4Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s4StockWords; decide +kernel
  · decide +kernel
  · simp only [s4Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
-- s5: C5_5=0 (lb=4, vars=4, kind=2)
def s5Mask : Word := 0xf000000000000000f000000000000000f000000000000000f
abbrev s5Goal : Word := sGoal &&& s5Mask
abbrev s5StockWords : List Word := projectDAGStock s5Mask sBase [0, 1, 6, 7]
def s5Fact : Bound := (s5Mask, s5StockWords, 4, s5Goal)
def s5Witnesses := unpackWitnesses s5StockWords [1538, 263681, 558082, 884800]
def s5Cuts : List Bound := []
def s5Chart : Option RowChart := some ⟨[3, 66, 192, 67, 131, 193, 194, 195, 3, 66, 192, 67, 65, 129, 130, 1, 2, 64, 128, 0, 65, 129, 130, 1], rfl⟩
def s5Sample : DagSample := (0x3, 1)
def s5Links : DagLinks :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 3
def s5Data : Forest := fun i => decodeNode 1 5 0x0 i
def s5Tags := dagTraceTags s5Mask 1 (dagTagBases s5StockWords 0x3 0x0 1) 3 s5Data
def s5States := dagTrace s5Mask s5StockWords 3 s5Data
def s5Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s5MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s5Move0Map, s5Move0Map)]
def s5Moves := dagMoves s5MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s5Autos : DagMovesOK s5Mask s5Goal 256 s5Moves := dagMovesOfCheck (by decide +kernel)
def s5Check := dagCheckNode s5Mask s5Goal s5Chart (dagKnownCloses s5Goal s5Cuts) 0 s5States s5Moves s5Links s5Sample s5Tags
def s5RootAt (token : Nat) : Bool :=
  let s := rootState s5StockWords 3 token
  !dagAllowedRoot s5Witnesses s.2.1 || dagLocal s5Mask s5Goal s5Chart (dagKnownCloses s5Goal s5Cuts) s ||
  dagRef 0 s5States s5Moves s5Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s5RootBlock0 : treeBlock 0 16 s5RootAt = true := by decide +kernel
theorem s5RootVerified : treeBlock 0 16 s5RootAt = true := s5RootBlock0
theorem s5Roots : dagCheckRoots s5Mask s5Goal s5Chart (dagKnownCloses s5Goal s5Cuts) s5Witnesses (dagRef 0 s5States s5Moves s5Links 0) s5StockWords 3 = true := s5RootVerified
theorem s5Blocks : treeBlock 0 0 s5Check = true := rfl
theorem s5Known : Known s5Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s5Stock : Lower s5Mask s5StockWords s5Goal 4 := by
  apply lowerDag _ _ _ _ s5Autos _ _ _ s5Known _ s5Roots s5Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s5StockWords; decide +kernel
  · decide +kernel
  · simp only [s5Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
-- s6: C5_6=0 (lb=4, vars=4, kind=2)
def s6Mask : Word := 0xf0000000f00000000000000000000000f0000000f
abbrev s6Goal : Word := sGoal &&& s6Mask
abbrev s6StockWords : List Word := projectDAGStock s6Mask sBase [0, 1, 5, 7]
def s6Fact : Bound := (s6Mask, s6StockWords, 4, s6Goal)
def s6Witnesses := unpackWitnesses s6StockWords [1538, 263681, 541185, 868384]
def s6Cuts : List Bound := []
def s6Chart : Option RowChart := some ⟨[3, 33, 160, 35, 131, 161, 162, 163, 3, 33, 160, 35, 34, 129, 130, 1, 2, 32, 128, 0, 34, 129, 130, 1], rfl⟩
def s6Sample : DagSample := (0x3, 1)
def s6Links : DagLinks :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 3
def s6Data : Forest := fun i => decodeNode 1 5 0x0 i
def s6Tags := dagTraceTags s6Mask 1 (dagTagBases s6StockWords 0x3 0x0 1) 3 s6Data
def s6States := dagTrace s6Mask s6StockWords 3 s6Data
def s6Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s6MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s6Move0Map, s6Move0Map)]
def s6Moves := dagMoves s6MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Autos : DagMovesOK s6Mask s6Goal 256 s6Moves := dagMovesOfCheck (by decide +kernel)
def s6Check := dagCheckNode s6Mask s6Goal s6Chart (dagKnownCloses s6Goal s6Cuts) 0 s6States s6Moves s6Links s6Sample s6Tags
def s6RootAt (token : Nat) : Bool :=
  let s := rootState s6StockWords 3 token
  !dagAllowedRoot s6Witnesses s.2.1 || dagLocal s6Mask s6Goal s6Chart (dagKnownCloses s6Goal s6Cuts) s ||
  dagRef 0 s6States s6Moves s6Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6RootBlock0 : treeBlock 0 16 s6RootAt = true := by decide +kernel
theorem s6RootVerified : treeBlock 0 16 s6RootAt = true := s6RootBlock0
theorem s6Roots : dagCheckRoots s6Mask s6Goal s6Chart (dagKnownCloses s6Goal s6Cuts) s6Witnesses (dagRef 0 s6States s6Moves s6Links 0) s6StockWords 3 = true := s6RootVerified
theorem s6Blocks : treeBlock 0 0 s6Check = true := rfl
theorem s6Known : Known s6Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Stock : Lower s6Mask s6StockWords s6Goal 4 := by
  apply lowerDag _ _ _ _ s6Autos _ _ _ s6Known _ s6Roots s6Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s6StockWords; decide +kernel
  · decide +kernel
  · simp only [s6Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
-- s7: C5_7=0 (lb=4, vars=4, kind=2)
def s7Mask : Word := 0xf0000000f0000000f0000000f
abbrev s7Goal : Word := sGoal &&& s7Mask
abbrev s7StockWords : List Word := projectDAGStock s7Mask sBase [0, 1, 5, 6]
def s7Fact : Bound := (s7Mask, s7StockWords, 4, s7Goal)
def s7Witnesses := unpackWitnesses s7StockWords [1538, 263681, 541185, 820226]
def s7Cuts : List Bound := []
def s7Chart : Option RowChart := some ⟨[3, 33, 66, 35, 67, 97, 98, 99, 3, 33, 66, 35, 34, 65, 96, 1, 2, 32, 64, 0, 34, 65, 96, 1], rfl⟩
def s7Sample : DagSample := (0x3, 1)
def s7Links : DagLinks :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 3
def s7Data : Forest := fun i => decodeNode 1 5 0x0 i
def s7Tags := dagTraceTags s7Mask 1 (dagTagBases s7StockWords 0x3 0x0 1) 3 s7Data
def s7States := dagTrace s7Mask s7StockWords 3 s7Data
def s7Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s7MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s7Move0Map, s7Move0Map)]
def s7Moves := dagMoves s7MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Autos : DagMovesOK s7Mask s7Goal 256 s7Moves := dagMovesOfCheck (by decide +kernel)
def s7Check := dagCheckNode s7Mask s7Goal s7Chart (dagKnownCloses s7Goal s7Cuts) 0 s7States s7Moves s7Links s7Sample s7Tags
def s7RootAt (token : Nat) : Bool :=
  let s := rootState s7StockWords 3 token
  !dagAllowedRoot s7Witnesses s.2.1 || dagLocal s7Mask s7Goal s7Chart (dagKnownCloses s7Goal s7Cuts) s ||
  dagRef 0 s7States s7Moves s7Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7RootBlock0 : treeBlock 0 16 s7RootAt = true := by decide +kernel
theorem s7RootVerified : treeBlock 0 16 s7RootAt = true := s7RootBlock0
theorem s7Roots : dagCheckRoots s7Mask s7Goal s7Chart (dagKnownCloses s7Goal s7Cuts) s7Witnesses (dagRef 0 s7States s7Moves s7Links 0) s7StockWords 3 = true := s7RootVerified
theorem s7Blocks : treeBlock 0 0 s7Check = true := rfl
theorem s7Known : Known s7Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Stock : Lower s7Mask s7StockWords s7Goal 4 := by
  apply lowerDag _ _ _ _ s7Autos _ _ _ s7Known _ s7Roots s7Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s7StockWords; decide +kernel
  · decide +kernel
  · simp only [s7Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
-- s8: C5 (lb=7, vars=5, kind=2)
def s8Mask : Word := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
abbrev s8Goal : Word := sGoal &&& s8Mask
abbrev s8StockWords : List Word := projectDAGStock s8Mask sBase [0, 1, 5, 6, 7]
def s8Fact : Bound := (s8Mask, s8StockWords, 7, s8Goal)
def s8Witnesses := unpackWitnesses s8StockWords [1538, 263681, 541185, 820226, 1130528]
def s8Cuts : List Bound := [s2Fact, s4Fact, s5Fact, s6Fact, s7Fact]
def s8Chart : Option RowChart := some ⟨[3, 33, 66, 160, 192, 35, 67, 97, 98, 131, 161, 162, 34, 65, 96, 129, 130, 1, 2, 32, 64, 128, 0, 34], rfl⟩
def s8Sample : DagSample := (0x2030088440a01110844a02010880c02080c82c04028100c04110904a010084440311084822130084c04230189020340b0504034128844a230185022140a0d02a14120c824320b044423111888261, 35)
def s8Links : DagLinks :=
  dagLookupLinks 0x30c30341 0xbc38392ca62023141008001f 6 3 12 2 2 5
def s8Data : Forest := fun i => decodeNode 3 15 0x92c2628402080f8 i
def s8Tags := dagTraceTags s8Mask 35 (dagTagBases s8StockWords 0x157402ce816b034436d09ba3d1e5448ee5b6083e73fd 0x3c079e00780f0432700ee1818606c0e1360c0461d9 35) 6 s8Data
def s8States := dagTrace s8Mask s8StockWords 6 s8Data
def s8Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s8Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 5, 2, 3, 4, 1, 7, 6] 0 i.val)
def s8Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 5, 2, 4, 3, 1, 7, 6] 0 i.val)
def s8MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s8Move0Map, s8Move0Map), ([([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333, 0), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x3333333300000000333333330000000033333333000000003333333300000000, 30)]), ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)])], s8Move1Map, s8Move1Map), ([([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333, 0), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x3333333300000000333333330000000033333333000000003333333300000000, 30)]), ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)]), ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s8Move2Map, s8Move2Map)]
def s8Moves := dagMoves s8MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8Autos : DagMovesOK s8Mask s8Goal 256 s8Moves := dagMovesOfCheck (by decide +kernel)
def s8Check := dagCheckNode s8Mask s8Goal s8Chart (dagKnownCloses s8Goal s8Cuts) 4 s8States s8Moves s8Links s8Sample s8Tags
def s8RootAt (token : Nat) : Bool :=
  let s := rootState s8StockWords 6 token
  !dagAllowedRoot s8Witnesses s.2.1 || dagLocal s8Mask s8Goal s8Chart (dagKnownCloses s8Goal s8Cuts) s ||
  dagRef 4 s8States s8Moves s8Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8RootBlock0 : treeBlock 0 32 s8RootAt = true := by decide +kernel
theorem s8RootVerified : treeBlock 0 32 s8RootAt = true := s8RootBlock0
theorem s8Roots : dagCheckRoots s8Mask s8Goal s8Chart (dagKnownCloses s8Goal s8Cuts) s8Witnesses (dagRef 4 s8States s8Moves s8Links 0) s8StockWords 6 = true := s8RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8Block0 : treeBlock 0 4 s8Check = true := by decide +kernel
theorem s8Verified : treeBlock 0 4 s8Check = true := s8Block0
theorem s8Blocks : treeBlock 0 4 s8Check = true := s8Verified
theorem s8Known : Known s8Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s7Stock) s6Stock) s5Stock) s4Stock) s2Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8Stock : Lower s8Mask s8StockWords s8Goal 7 := by
  apply lowerDag _ _ _ _ s8Autos _ _ _ s8Known _ s8Roots s8Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s8StockWords; decide +kernel
  · decide +kernel
  · simp only [s8Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
-- s9: BT_3=0 (lb=5, vars=4, kind=1)
def s9Mask : Word := 0xff00ff
abbrev s9Goal : Word := sGoal &&& s9Mask
abbrev s9StockWords : List Word := projectDAGStock s9Mask sBase [0, 1, 2, 4]
def s9Fact : Bound := (s9Mask, s9StockWords, 5, s9Goal)
def s9Witnesses := unpackWitnesses s9StockWords [1538, 263681, 526849, 795137]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s9Stock : Lower s9Mask s9StockWords s9Goal 5 := by
  apply essentialLift (witnesses := s9Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
-- s10: BT_4=0 (lb=5, vars=4, kind=1)
def s10Mask : Word := 0xffff
abbrev s10Goal : Word := sGoal &&& s10Mask
abbrev s10StockWords : List Word := projectDAGStock s10Mask sBase [0, 1, 2, 3]
def s10Fact : Bound := (s10Mask, s10StockWords, 5, s10Goal)
def s10Witnesses := unpackWitnesses s10StockWords [1538, 263681, 526849, 791041]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10Stock : Lower s10Mask s10StockWords s10Goal 5 := by
  apply essentialLift (witnesses := s10Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
-- s11: BT_1=0 (lb=5, vars=4, kind=1)
def s11Mask : Word := 0x33333333
abbrev s11Goal : Word := sGoal &&& s11Mask
abbrev s11StockWords : List Word := projectDAGStock s11Mask sBase [0, 2, 3, 4]
def s11Fact : Bound := (s11Mask, s11StockWords, 5, s11Goal)
def s11Witnesses := unpackWitnesses s11StockWords [2564, 264705, 528897, 795137]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s11Stock : Lower s11Mask s11StockWords s11Goal 5 := by
  apply essentialLift (witnesses := s11Witnesses) (cut := s1Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s1StockWords) (by decide +kernel)
  · exact s1Stock
  · decide +kernel
-- s12: BT_2=0 (lb=5, vars=4, kind=1)
def s12Mask : Word := 0xf0f0f0f
abbrev s12Goal : Word := sGoal &&& s12Mask
abbrev s12StockWords : List Word := projectDAGStock s12Mask sBase [0, 1, 3, 4]
def s12Fact : Bound := (s12Mask, s12StockWords, 5, s12Goal)
def s12Witnesses := unpackWitnesses s12StockWords [1538, 263681, 528897, 795137]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Stock : Lower s12Mask s12StockWords s12Goal 5 := by
  apply essentialLift (witnesses := s12Witnesses) (cut := s1Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s1StockWords) (by decide +kernel)
  · exact s1Stock
  · decide +kernel
-- s13: BT_0=0 (lb=3, vars=4, kind=0)
def s13Mask : Word := 0x55555555
abbrev s13Goal : Word := sGoal &&& s13Mask
abbrev s13StockWords : List Word := projectDAGStock s13Mask sBase [1, 2, 3, 4]
def s13Fact : Bound := (s13Mask, s13StockWords, 3, s13Goal)
def s13Witnesses := unpackWitnesses s13StockWords [3076, 265218, 536592, 798728]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Stock : Lower s13Mask s13StockWords s13Goal 3 := by
  apply essentialLower (witnesses := s13Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s14: BT_1=1 (lb=3, vars=4, kind=0)
def s14Mask : Word := 0xcccccccc
abbrev s14Goal : Word := sGoal &&& s14Mask
abbrev s14StockWords : List Word := projectDAGStock s14Mask sBase [0, 2, 3, 4]
def s14Fact : Bound := (s14Mask, s14StockWords, 3, s14Goal)
def s14Witnesses := unpackWitnesses s14StockWords [1538, 265218, 537618, 799754]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s14Stock : Lower s14Mask s14StockWords s14Goal 3 := by
  apply essentialLower (witnesses := s14Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s15: BT_2=1 (lb=3, vars=4, kind=0)
def s15Mask : Word := 0xf0f0f0f0
abbrev s15Goal : Word := sGoal &&& s15Mask
abbrev s15StockWords : List Word := projectDAGStock s15Mask sBase [0, 1, 3, 4]
def s15Fact : Bound := (s15Mask, s15StockWords, 3, s15Goal)
def s15Witnesses := unpackWitnesses s15StockWords [2564, 265220, 538644, 800780]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15Stock : Lower s15Mask s15StockWords s15Goal 3 := by
  apply essentialLower (witnesses := s15Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s16: BT_3=1 (lb=3, vars=4, kind=0)
def s16Mask : Word := 0xff00ff00
abbrev s16Goal : Word := sGoal &&& s16Mask
abbrev s16StockWords : List Word := projectDAGStock s16Mask sBase [0, 1, 2, 4]
def s16Fact : Bound := (s16Mask, s16StockWords, 3, s16Goal)
def s16Witnesses := unpackWitnesses s16StockWords [4616, 269324, 531466, 798728]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16Stock : Lower s16Mask s16StockWords s16Goal 3 := by
  apply essentialLower (witnesses := s16Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s17: BT_4=1 (lb=3, vars=4, kind=0)
def s17Mask : Word := 0xffff0000
abbrev s17Goal : Word := sGoal &&& s17Mask
abbrev s17StockWords : List Word := projectDAGStock s17Mask sBase [0, 1, 2, 3]
def s17Fact : Bound := (s17Mask, s17StockWords, 3, s17Goal)
def s17Witnesses := unpackWitnesses s17StockWords [8720, 273428, 535570, 798736]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s17Stock : Lower s17Mask s17StockWords s17Goal 3 := by
  apply essentialLower (witnesses := s17Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s18: BOWTIE (lb=8, vars=5, kind=2)
def s18Mask : Word := 0xffffffff
abbrev s18Goal : Word := sGoal &&& s18Mask
abbrev s18StockWords : List Word := projectDAGStock s18Mask sBase [0, 1, 2, 3, 4]
def s18Fact : Bound := (s18Mask, s18StockWords, 8, s18Goal)
def s18Witnesses := unpackWitnesses s18StockWords [1538, 263681, 526849, 791041, 1057281]
def s18Cuts : List Bound := [s9Fact, s10Fact, s11Fact, s12Fact, s13Fact, s14Fact, s15Fact, s16Fact, s17Fact]
def s18Chart : Option RowChart := some ⟨[3, 5, 6, 9, 17, 24, 7, 11, 13, 14, 19, 21, 10, 12, 18, 20, 1, 2, 4, 8, 16, 0, 10, 12], rfl⟩
def s18Sample : DagSample := (0x8050402c14180601420180a044100d0606020110a01428180406014090602428150402414030900c28060601824160a05814060904c180d09018281c0080c181c00844180e0906802050502c020905038141a, 37)
def s18Links : DagLinks :=
  dagLookupLinks 0x320c8320c8320a92a0a82240c001 0x19c381325821880398a57c388f2589d880398a54c388b26f124b1b31ba662b48c4058cdc31958531f086294c0de1815a301f060260802408040001f 10 5 12 4 3 7
def s18Data : Forest := fun i => decodeNode 4 16 0x92c56205314232b131f1314101310091008101f0 i
def s18Tags := dagTraceTags s18Mask 37 (dagTagBases s18StockWords 0x5b641a5a16b3d00ab7c9211f75490003fd4d7ad9f8329c 0x19c4dac20731d928a5cab31a550080232d056000000294 37) 7 s18Data
def s18States := dagTrace s18Mask s18StockWords 7 s18Data
def s18Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s18Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 5, 6, 7] 0 i.val)
def s18Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 4, 3, 5, 6, 7] 0 i.val)
def s18Move3Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 3, 4, 1, 2, 5, 6, 7] 0 i.val)
def s18Move4Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 3, 2, 1, 5, 6, 7] 0 i.val)
def s18Move5Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 5, 7] 0 i.val)
def s18MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s18Move0Map, s18Move0Map), ([([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)])], s18Move1Map, s18Move1Map), ([([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)]), ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s18Move2Map, s18Move2Map), ([([(0xcc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33, 0), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0x3300330033003300330033003300330033003300330033003300330033003300, 6)]), ([(0xf0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0f, 0), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000, 12)])], s18Move3Map, s18Move3Map), ([([(0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333, 0), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x3333000033330000333300003333000033330000333300003333000033330000, 14)]), ([(0xf00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f, 0), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 4)])], s18Move4Map, s18Move4Map), ([([(0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff, 0), (0xffffffff000000000000000000000000ffffffff00000000, 32)], [(0xffffffff000000000000000000000000ffffffff0000000000000000, 32)])], s18Move5Map, s18Move5Map)]
def s18Moves := dagMoves s18MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Autos : DagMovesOK s18Mask s18Goal 256 s18Moves := dagMovesOfCheck (by decide +kernel)
def s18Check := dagCheckNode s18Mask s18Goal s18Chart (dagKnownCloses s18Goal s18Cuts) 10 s18States s18Moves s18Links s18Sample s18Tags
def s18RootAt (token : Nat) : Bool :=
  let s := rootState s18StockWords 7 token
  !dagAllowedRoot s18Witnesses s.2.1 || dagLocal s18Mask s18Goal s18Chart (dagKnownCloses s18Goal s18Cuts) s ||
  dagRef 10 s18States s18Moves s18Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18RootBlock0 : treeBlock 0 32 s18RootAt = true := by decide +kernel
theorem s18RootVerified : treeBlock 0 32 s18RootAt = true := s18RootBlock0
theorem s18Roots : dagCheckRoots s18Mask s18Goal s18Chart (dagKnownCloses s18Goal s18Cuts) s18Witnesses (dagRef 10 s18States s18Moves s18Links 0) s18StockWords 7 = true := s18RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Block0 : treeBlock 0 10 s18Check = true := by decide +kernel
theorem s18Verified : treeBlock 0 10 s18Check = true := s18Block0
theorem s18Blocks : treeBlock 0 10 s18Check = true := s18Verified
theorem s18Known : Known s18Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s17Stock) s16Stock) s15Stock) s14Stock) s13Stock) s12Stock) s11Stock) s10Stock) s9Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Stock : Lower s18Mask s18StockWords s18Goal 8 := by
  apply lowerDag _ _ _ _ s18Autos _ _ _ s18Known _ s18Roots s18Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s18StockWords; decide +kernel
  · decide +kernel
  · simp only [s18Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
-- s19: K3_012_7=1 (lb=4, vars=3, kind=3)
def s19Mask : Word := 0xff00000000000000000000000000000000
abbrev s19Goal : Word := sGoal &&& s19Mask
abbrev s19StockWords : List Word := projectDAGStock s19Mask sBase [0, 1, 2]
def s19Fact : Bound := (s19Mask, s19StockWords, 4, s19Goal)
def s19Witnesses := unpackWitnesses s19StockWords [67202, 329345, 592513]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19Stock : Lower s19Mask s19StockWords s19Goal 4 := dagShiftLower (width := 256) [([(0xffffffffffffffffffffffffffffffff, 128)], [(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128)])] s0Stock (by decide +kernel)
-- s20: K3_034_7=1 (lb=4, vars=3, kind=3)
def s20Mask : Word := 0x303030300000000000000000000000000000000
abbrev s20Goal : Word := sGoal &&& s20Mask
abbrev s20StockWords : List Word := projectDAGStock s20Mask sBase [0, 3, 4]
def s20Fact : Bound := (s20Mask, s20StockWords, 4, s20Goal)
def s20Witnesses := unpackWitnesses s20StockWords [70280, 332417, 598657]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s20Stock : Lower s20Mask s20StockWords s20Goal 4 := dagShiftLower (width := 256) [([(0xffffffffffffffffffffffffffffffff, 128)], [(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128)])] s1Stock (by decide +kernel)
-- s21: K3_034_6=1 (lb=4, vars=3, kind=3)
def s21Mask : Word := 0x30303030000000000000000
abbrev s21Goal : Word := sGoal &&& s21Mask
abbrev s21StockWords : List Word := projectDAGStock s21Mask sBase [0, 3, 4]
def s21Fact : Bound := (s21Mask, s21StockWords, 4, s21Goal)
def s21Witnesses := unpackWitnesses s21StockWords [37448, 299585, 565825]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Stock : Lower s21Mask s21StockWords s21Goal 4 := dagShiftLower (width := 256) [([(0xffffffffffffffff0000000000000000ffffffffffffffff, 64)], [(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 64)])] s1Stock (by decide +kernel)
-- s22: P4_3=1 (lb=4, vars=4, kind=3)
def s22Mask : Word := 0x50000000500000005000000050000000500000005000000050000000500
abbrev s22Goal : Word := sGoal &&& s22Mask
abbrev s22StockWords : List Word := projectDAGStock s22Mask sBase [1, 5, 6, 7]
def s22Fact : Bound := (s22Mask, s22StockWords, 4, s22Goal)
def s22Witnesses := unpackWitnesses s22StockWords [37960, 348296, 562186, 872488]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s22Stock : Lower s22Mask s22StockWords s22Goal 4 := dagShiftLower (width := 256) [([(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 8)], [(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 8)])] s2Stock (by decide +kernel)
-- s23: P4_4=1 (lb=4, vars=4, kind=3)
def s23Mask : Word := 0x5000000050000000500000005000000050000000500000005000000050000
abbrev s23Goal : Word := sGoal &&& s23Mask
abbrev s23StockWords : List Word := projectDAGStock s23Mask sBase [1, 5, 6, 7]
def s23Fact : Bound := (s23Mask, s23StockWords, 4, s23Goal)
def s23Witnesses := unpackWitnesses s23StockWords [42064, 352400, 566290, 876592]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Stock : Lower s23Mask s23StockWords s23Goal 4 := dagShiftLower (width := 256) [([(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 16)], [(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 16)])] s2Stock (by decide +kernel)
-- s24: P5_3=1 (lb=5, vars=5, kind=3)
def s24Mask : Word := 0x550000005500000055000000550000005500000055000000550000005500
abbrev s24Goal : Word := sGoal &&& s24Mask
abbrev s24StockWords : List Word := projectDAGStock s24Mask sBase [1, 2, 5, 6, 7]
def s24Fact : Bound := (s24Mask, s24StockWords, 5, s24Goal)
def s24Witnesses := unpackWitnesses s24StockWords [7180, 269322, 610440, 824330, 1134632]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s24Stock : Lower s24Mask s24StockWords s24Goal 5 := dagShiftLower (width := 256) [([(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 8)], [(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 8)])] s3Stock (by decide +kernel)
-- s25: P5_4=1 (lb=5, vars=5, kind=3)
def s25Mask : Word := 0x55000000550000005500000055000000550000005500000055000000550000
abbrev s25Goal : Word := sGoal &&& s25Mask
abbrev s25StockWords : List Word := projectDAGStock s25Mask sBase [1, 2, 5, 6, 7]
def s25Fact : Bound := (s25Mask, s25StockWords, 5, s25Goal)
def s25Witnesses := unpackWitnesses s25StockWords [11284, 273426, 614544, 828434, 1138736]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Stock : Lower s25Mask s25StockWords s25Goal 5 := dagShiftLower (width := 256) [([(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 16)], [(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 16)])] s3Stock (by decide +kernel)
-- s26: BOWTIE_7=1 (lb=8, vars=5, kind=3)
def s26Mask : Word := 0xffffffff00000000000000000000000000000000
abbrev s26Goal : Word := sGoal &&& s26Mask
abbrev s26StockWords : List Word := projectDAGStock s26Mask sBase [0, 1, 2, 3, 4]
def s26Fact : Bound := (s26Mask, s26StockWords, 8, s26Goal)
def s26Witnesses := unpackWitnesses s26StockWords [67202, 329345, 592513, 856705, 1122945]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s26Stock : Lower s26Mask s26StockWords s26Goal 8 := dagShiftLower (width := 256) [([(0xffffffffffffffffffffffffffffffff, 128)], [(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128)])] s18Stock (by decide +kernel)
-- s27: 34_50_70 (lb=5, vars=4, kind=1)
def s27Mask : Word := 0xff00000000000000ff
abbrev s27Goal : Word := sGoal &&& s27Mask
abbrev s27StockWords : List Word := projectDAGStock s27Mask sBase [0, 1, 2, 6]
def s27Fact : Bound := (s27Mask, s27StockWords, 5, s27Goal)
def s27Witnesses := unpackWitnesses s27StockWords [1538, 263681, 526849, 820226]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s27Stock : Lower s27Mask s27StockWords s27Goal 5 := by
  apply essentialLift (witnesses := s27Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
-- s28: 34_50_71 (lb=5, vars=4, kind=1)
def s28Mask : Word := 0xff00000000000000ff00000000000000000000000000000000
abbrev s28Goal : Word := sGoal &&& s28Mask
abbrev s28StockWords : List Word := projectDAGStock s28Mask sBase [0, 1, 2, 6]
def s28Fact : Bound := (s28Mask, s28StockWords, 5, s28Goal)
def s28Witnesses := unpackWitnesses s28StockWords [67202, 329345, 592513, 884864]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s28Stock : Lower s28Mask s28StockWords s28Goal 5 := by
  apply essentialLift (witnesses := s28Witnesses) (cut := s19Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s19StockWords) (by decide +kernel)
  · exact s19Stock
  · decide +kernel
-- s29: 34_50 (lb=7, vars=5, kind=2)
def s29Mask : Word := 0xff00000000000000ff00000000000000ff00000000000000ff
abbrev s29Goal : Word := sGoal &&& s29Mask
abbrev s29StockWords : List Word := projectDAGStock s29Mask sBase [0, 1, 2, 6, 7]
def s29Fact : Bound := (s29Mask, s29StockWords, 7, s29Goal)
def s29Witnesses := unpackWitnesses s29StockWords [1538, 263681, 526849, 820226, 1146944]
def s29Cuts : List Bound := [s27Fact, s28Fact]
def s29Chart : Option RowChart := some ⟨[3, 5, 6, 66, 192, 7, 67, 69, 70, 131, 133, 134, 65, 68, 129, 130, 132, 1, 2, 4, 64, 128, 0, 65], rfl⟩
def s29Sample : DagSample := (0x2201902c04221908c04231080422080c82052090888052210908852211904c22090c884540a15048620915028340b050483, 22)
def s29Links : DagLinks :=
  dagLookupLinks 0xa28a28301 0x492c362023141008001f 6 3 12 3 1 5
def s29Data : Forest := fun i => decodeNode 3 15 0x49616202628402080f8 i
def s29Tags := dagTraceTags s29Mask 22 (dagTagBases s29StockWords 0x1e05375caf2aa5678a6ae540d4ef 0x1e053787eb22e1e400004450e0ae 22) 6 s29Data
def s29States := dagTrace s29Mask s29StockWords 6 s29Data
def s29Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s29MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s29Move0Map, s29Move0Map)]
def s29Moves := dagMoves s29MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Autos : DagMovesOK s29Mask s29Goal 256 s29Moves := dagMovesOfCheck (by decide +kernel)
def s29Check := dagCheckNode s29Mask s29Goal s29Chart (dagKnownCloses s29Goal s29Cuts) 5 s29States s29Moves s29Links s29Sample s29Tags
def s29RootAt (token : Nat) : Bool :=
  let s := rootState s29StockWords 6 token
  !dagAllowedRoot s29Witnesses s.2.1 || dagLocal s29Mask s29Goal s29Chart (dagKnownCloses s29Goal s29Cuts) s ||
  dagRef 5 s29States s29Moves s29Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29RootBlock0 : treeBlock 0 32 s29RootAt = true := by decide +kernel
theorem s29RootVerified : treeBlock 0 32 s29RootAt = true := s29RootBlock0
theorem s29Roots : dagCheckRoots s29Mask s29Goal s29Chart (dagKnownCloses s29Goal s29Cuts) s29Witnesses (dagRef 5 s29States s29Moves s29Links 0) s29StockWords 6 = true := s29RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block0 : treeBlock 0 5 s29Check = true := by decide +kernel
theorem s29Verified : treeBlock 0 5 s29Check = true := s29Block0
theorem s29Blocks : treeBlock 0 5 s29Check = true := s29Verified
theorem s29Known : Known s29Cuts := (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s28Stock) s27Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Stock : Lower s29Mask s29StockWords s29Goal 7 := by
  apply lowerDag _ _ _ _ s29Autos _ _ _ s29Known _ s29Roots s29Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s29StockWords; decide +kernel
  · decide +kernel
  · simp only [s29Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
-- s30: 34_60_70 (lb=5, vars=4, kind=1)
def s30Mask : Word := 0xff000000ff
abbrev s30Goal : Word := sGoal &&& s30Mask
abbrev s30StockWords : List Word := projectDAGStock s30Mask sBase [0, 1, 2, 5]
def s30Fact : Bound := (s30Mask, s30StockWords, 5, s30Goal)
def s30Witnesses := unpackWitnesses s30StockWords [1538, 263681, 526849, 803329]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s30Stock : Lower s30Mask s30StockWords s30Goal 5 := by
  apply essentialLift (witnesses := s30Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
-- s31: 34_60_71 (lb=5, vars=4, kind=1)
def s31Mask : Word := 0xff000000ff00000000000000000000000000000000
abbrev s31Goal : Word := sGoal &&& s31Mask
abbrev s31StockWords : List Word := projectDAGStock s31Mask sBase [0, 1, 2, 5]
def s31Fact : Bound := (s31Mask, s31StockWords, 5, s31Goal)
def s31Witnesses := unpackWitnesses s31StockWords [67202, 329345, 592513, 868480]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Stock : Lower s31Mask s31StockWords s31Goal 5 := by
  apply essentialLift (witnesses := s31Witnesses) (cut := s19Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s19StockWords) (by decide +kernel)
  · exact s19Stock
  · decide +kernel
-- s32: 34_60 (lb=7, vars=5, kind=2)
def s32Mask : Word := 0xff000000ff0000000000000000000000ff000000ff
abbrev s32Goal : Word := sGoal &&& s32Mask
abbrev s32StockWords : List Word := projectDAGStock s32Mask sBase [0, 1, 2, 5, 7]
def s32Fact : Bound := (s32Mask, s32StockWords, 7, s32Goal)
def s32Witnesses := unpackWitnesses s32StockWords [1538, 263681, 526849, 803329, 1130528]
def s32Cuts : List Bound := [s30Fact, s31Fact]
def s32Chart : Option RowChart := some ⟨[3, 5, 6, 33, 160, 7, 35, 37, 38, 131, 133, 134, 34, 36, 129, 130, 132, 1, 2, 4, 32, 128, 0, 34], rfl⟩
def s32Sample : DagSample := (0x40211100c44211201508864228108a41101848061208504864221504a21108c48251209904831109902a140a150283, 21)
def s32Links : DagLinks :=
  dagLookupLinks 0x28a28301 0x392ca62023141008001f 6 3 12 2 2 5
def s32Data : Forest := fun i => decodeNode 3 15 0x92c2628402080f8 i
def s32Tags := dagTraceTags s32Mask 21 (dagTagBases s32StockWords 0x1c717a64f60dd9a926b73e0ad7 0x1c717f1c740f698184b3000007 21) 6 s32Data
def s32States := dagTrace s32Mask s32StockWords 6 s32Data
def s32Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s32Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 5, 6, 7] 0 i.val)
def s32Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 4, 3, 5, 6, 7] 0 i.val)
def s32MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s32Move0Map, s32Move0Map), ([([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)])], s32Move1Map, s32Move1Map), ([([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)]), ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s32Move2Map, s32Move2Map)]
def s32Moves := dagMoves s32MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s32Autos : DagMovesOK s32Mask s32Goal 256 s32Moves := dagMovesOfCheck (by decide +kernel)
def s32Check := dagCheckNode s32Mask s32Goal s32Chart (dagKnownCloses s32Goal s32Cuts) 4 s32States s32Moves s32Links s32Sample s32Tags
def s32RootAt (token : Nat) : Bool :=
  let s := rootState s32StockWords 6 token
  !dagAllowedRoot s32Witnesses s.2.1 || dagLocal s32Mask s32Goal s32Chart (dagKnownCloses s32Goal s32Cuts) s ||
  dagRef 4 s32States s32Moves s32Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s32RootBlock0 : treeBlock 0 32 s32RootAt = true := by decide +kernel
theorem s32RootVerified : treeBlock 0 32 s32RootAt = true := s32RootBlock0
theorem s32Roots : dagCheckRoots s32Mask s32Goal s32Chart (dagKnownCloses s32Goal s32Cuts) s32Witnesses (dagRef 4 s32States s32Moves s32Links 0) s32StockWords 6 = true := s32RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s32Block0 : treeBlock 0 4 s32Check = true := by decide +kernel
theorem s32Verified : treeBlock 0 4 s32Check = true := s32Block0
theorem s32Blocks : treeBlock 0 4 s32Check = true := s32Verified
theorem s32Known : Known s32Cuts := (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s31Stock) s30Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s32Stock : Lower s32Mask s32StockWords s32Goal 7 := by
  apply lowerDag _ _ _ _ s32Autos _ _ _ s32Known _ s32Roots s32Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s32StockWords; decide +kernel
  · decide +kernel
  · simp only [s32Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
-- s33: 34_70 (lb=6, vars=5, kind=1)
def s33Mask : Word := 0xff000000ff000000ff000000ff
abbrev s33Goal : Word := sGoal &&& s33Mask
abbrev s33StockWords : List Word := projectDAGStock s33Mask sBase [0, 1, 2, 5, 6]
def s33Fact : Bound := (s33Mask, s33StockWords, 6, s33Goal)
def s33Witnesses := unpackWitnesses s33StockWords [1538, 263681, 526849, 803329, 1082370]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s33Stock : Lower s33Mask s33StockWords s33Goal 6 := by
  apply essentialLift (witnesses := s33Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
-- s34: 34_71 (lb=6, vars=5, kind=1)
def s34Mask : Word := 0xff000000ff000000ff000000ff00000000000000000000000000000000
abbrev s34Goal : Word := sGoal &&& s34Mask
abbrev s34StockWords : List Word := projectDAGStock s34Mask sBase [0, 1, 2, 5, 6]
def s34Fact : Bound := (s34Mask, s34StockWords, 6, s34Goal)
def s34Witnesses := unpackWitnesses s34StockWords [67202, 329345, 592513, 868480, 1147008]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Stock : Lower s34Mask s34StockWords s34Goal 6 := by
  apply essentialLift (witnesses := s34Witnesses) (cut := s19Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s19StockWords) (by decide +kernel)
  · exact s19Stock
  · decide +kernel
-- s35: 34_10 (lb=5, vars=5, kind=1)
def s35Mask : Word := 0x3300000033000000330000003300000033000000330000003300000033
abbrev s35Goal : Word := sGoal &&& s35Mask
abbrev s35StockWords : List Word := projectDAGStock s35Mask sBase [0, 2, 5, 6, 7]
def s35Fact : Bound := (s35Mask, s35StockWords, 5, s35Goal)
def s35Witnesses := unpackWitnesses s35StockWords [2564, 264705, 541185, 884864, 1130528]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s35Stock : Lower s35Mask s35StockWords s35Goal 5 := by
  apply essentialLift (witnesses := s35Witnesses) (cut := s4Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s4StockWords) (by decide +kernel)
  · exact s4Stock
  · decide +kernel
-- s36: 34_51 (lb=4, vars=5, kind=0)
def s36Mask : Word := 0xff00000000000000ff00000000000000ff00000000000000ff00000000
abbrev s36Goal : Word := sGoal &&& s36Mask
abbrev s36StockWords : List Word := projectDAGStock s36Mask sBase [0, 1, 2, 6, 7]
def s36Fact : Bound := (s36Mask, s36StockWords, 4, s36Goal)
def s36Witnesses := unpackWitnesses s36StockWords [16928, 281636, 543778, 836642, 1130528]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Stock : Lower s36Mask s36StockWords s36Goal 4 := by
  apply essentialLower (witnesses := s36Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s37: 34_61 (lb=4, vars=5, kind=0)
def s37Mask : Word := 0xff000000ff0000000000000000000000ff000000ff0000000000000000
abbrev s37Goal : Word := sGoal &&& s37Mask
abbrev s37StockWords : List Word := projectDAGStock s37Mask sBase [0, 1, 2, 5, 7]
def s37Fact : Bound := (s37Mask, s37StockWords, 4, s37Goal)
def s37Witnesses := unpackWitnesses s37StockWords [35396, 296000, 559681, 836161, 1146944]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Stock : Lower s37Mask s37StockWords s37Goal 4 := by
  apply essentialLower (witnesses := s37Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s38: 34_21 (lb=4, vars=5, kind=0)
def s38Mask : Word := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0
abbrev s38Goal : Word := sGoal &&& s38Mask
abbrev s38StockWords : List Word := projectDAGStock s38Mask sBase [0, 1, 5, 6, 7]
def s38Fact : Bound := (s38Mask, s38StockWords, 4, s38Goal)
def s38Witnesses := unpackWitnesses s38StockWords [2564, 265220, 608388, 886916, 1132580]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Stock : Lower s38Mask s38StockWords s38Goal 4 := by
  apply essentialLower (witnesses := s38Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s39: 34_01 (lb=4, vars=5, kind=0)
def s39Mask : Word := 0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa
abbrev s39Goal : Word := sGoal &&& s39Mask
abbrev s39StockWords : List Word := projectDAGStock s39Mask sBase [1, 2, 5, 6, 7]
def s39Fact : Bound := (s39Mask, s39StockWords, 4, s39Goal)
def s39Witnesses := unpackWitnesses s39StockWords [1537, 264705, 541185, 885377, 1147457]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Stock : Lower s39Mask s39StockWords s39Goal 4 := by
  apply essentialLower (witnesses := s39Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s40: 34_11 (lb=4, vars=5, kind=0)
def s40Mask : Word := 0xcc000000cc000000cc000000cc000000cc000000cc000000cc000000cc
abbrev s40Goal : Word := sGoal &&& s40Mask
abbrev s40StockWords : List Word := projectDAGStock s40Mask sBase [0, 2, 5, 6, 7]
def s40Fact : Bound := (s40Mask, s40StockWords, 4, s40Goal)
def s40Witnesses := unpackWitnesses s40StockWords [1538, 265218, 607362, 820226, 1131554]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Stock : Lower s40Mask s40StockWords s40Goal 4 := by
  apply essentialLower (witnesses := s40Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s41: K3C5 (lb=9, vars=6, kind=2)
def s41Mask : Word := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
abbrev s41Goal : Word := sGoal &&& s41Mask
abbrev s41StockWords : List Word := projectDAGStock s41Mask sBase [0, 1, 2, 5, 6, 7]
def s41Fact : Bound := (s41Mask, s41StockWords, 9, s41Goal)
def s41Witnesses := unpackWitnesses s41StockWords [1538, 263681, 526849, 803329, 1082370, 1392672]
def s41Cuts : List Bound := [s8Fact, s29Fact, s32Fact, s33Fact, s34Fact, s3Fact, s35Fact, s36Fact, s37Fact, s38Fact, s39Fact, s40Fact]
def s41Chart : Option RowChart := some ⟨[3, 5, 6, 33, 66, 160, 192, 7, 35, 37, 38, 67, 100, 34, 36, 65, 68, 96, 129, 130, 132, 1, 2, 4], rfl⟩
def s41Sample : DagSample := (0x486512198886522198c06530198c8a432310c8e03239102034100d04064110844422080d08a042300440311188c8263211504a242015080611084442611288826140815022140b0444232090c824532094c84632184c86232198c8651101882052088482c1, 45)
def s41Links : DagLinks :=
  dagLookupLinks 0x8888888888887a786a685350420f01 0xd620498a37d110628c040581a280a13e8883143fa218c54a62840131807880242010003f 8 3 12 4 1 6
def s41Data : Forest := fun i => decodeNode 4 16 0xf446040403440284f4423142f44131513141013100f10091008103f0 i
def s41Tags := dagTraceTags s41Mask 45 (dagTagBases s41StockWords 0xf030844003fb8ca812df1fec09a7a9797fa406d21cf150fceac32d150624a9fe97 0xf30e1c0007f821810ff7cfc23c709fc79e066c00fc00078c9c20100042001ec07 45) 8 s41Data
def s41States := dagTrace s41Mask s41StockWords 8 s41Data
def s41Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s41MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s41Move0Map, s41Move0Map)]
def s41Moves := dagMoves s41MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Autos : DagMovesOK s41Mask s41Goal 256 s41Moves := dagMovesOfCheck (by decide +kernel)
def s41Check := dagCheckNode s41Mask s41Goal s41Chart (dagKnownCloses s41Goal s41Cuts) 14 s41States s41Moves s41Links s41Sample s41Tags
def s41RootAt (token : Nat) : Bool :=
  let s := rootState s41StockWords 8 token
  !dagAllowedRoot s41Witnesses s.2.1 || dagLocal s41Mask s41Goal s41Chart (dagKnownCloses s41Goal s41Cuts) s ||
  dagRef 14 s41States s41Moves s41Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41RootBlock0 : treeBlock 0 64 s41RootAt = true := by decide +kernel
theorem s41RootVerified : treeBlock 0 64 s41RootAt = true := s41RootBlock0
theorem s41Roots : dagCheckRoots s41Mask s41Goal s41Chart (dagKnownCloses s41Goal s41Cuts) s41Witnesses (dagRef 14 s41States s41Moves s41Links 0) s41StockWords 8 = true := s41RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Block0 : treeBlock 0 14 s41Check = true := by decide +kernel
theorem s41Verified : treeBlock 0 14 s41Check = true := s41Block0
theorem s41Blocks : treeBlock 0 14 s41Check = true := s41Verified
theorem s41Known : Known s41Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s40Stock) s39Stock) s38Stock) s37Stock) s36Stock) s35Stock) s3Stock) s34Stock) s33Stock) s32Stock) s29Stock) s8Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Stock : Lower s41Mask s41StockWords s41Goal 9 := by
  apply lowerDag _ _ _ _ s41Autos _ _ _ s41Known _ s41Roots s41Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s41StockWords; decide +kernel
  · decide +kernel
  · simp only [s41Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
-- s42: 20_30 (lb=8, vars=6, kind=1)
def s42Mask : Word := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
abbrev s42Goal : Word := sGoal &&& s42Mask
abbrev s42StockWords : List Word := projectDAGStock s42Mask sBase [0, 1, 4, 5, 6, 7]
def s42Fact : Bound := (s42Mask, s42StockWords, 8, s42Goal)
def s42Witnesses := unpackWitnesses s42StockWords [1538, 263681, 532993, 803329, 1082370, 1392672]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s42Stock : Lower s42Mask s42StockWords s42Goal 8 := by
  apply essentialLift (witnesses := s42Witnesses) (cut := s8Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s8StockWords) (by decide +kernel)
  · exact s8Stock
  · decide +kernel
-- s43: 20_40 (lb=8, vars=6, kind=1)
def s43Mask : Word := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
abbrev s43Goal : Word := sGoal &&& s43Mask
abbrev s43StockWords : List Word := projectDAGStock s43Mask sBase [0, 1, 3, 5, 6, 7]
def s43Fact : Bound := (s43Mask, s43StockWords, 8, s43Goal)
def s43Witnesses := unpackWitnesses s43StockWords [1538, 263681, 528897, 803329, 1082370, 1392672]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43Stock : Lower s43Mask s43StockWords s43Goal 8 := by
  apply essentialLift (witnesses := s43Witnesses) (cut := s8Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s8StockWords) (by decide +kernel)
  · exact s8Stock
  · decide +kernel
-- s44: 20_10_60_70 (lb=5, vars=4, kind=1)
def s44Mask : Word := 0x303030303030303
abbrev s44Goal : Word := sGoal &&& s44Mask
abbrev s44StockWords : List Word := projectDAGStock s44Mask sBase [0, 3, 4, 5]
def s44Fact : Bound := (s44Mask, s44StockWords, 5, s44Goal)
def s44Witnesses := unpackWitnesses s44StockWords [4616, 266753, 532993, 803329]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44Stock : Lower s44Mask s44StockWords s44Goal 5 := by
  apply essentialLift (witnesses := s44Witnesses) (cut := s1Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s1StockWords) (by decide +kernel)
  · exact s1Stock
  · decide +kernel
-- s45: 20_10_60_71 (lb=5, vars=4, kind=1)
def s45Mask : Word := 0x30303030303030300000000000000000000000000000000
abbrev s45Goal : Word := sGoal &&& s45Mask
abbrev s45StockWords : List Word := projectDAGStock s45Mask sBase [0, 3, 4, 5]
def s45Fact : Bound := (s45Mask, s45StockWords, 5, s45Goal)
def s45Witnesses := unpackWitnesses s45StockWords [70280, 332417, 598657, 868480]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s45Stock : Lower s45Mask s45StockWords s45Goal 5 := by
  apply essentialLift (witnesses := s45Witnesses) (cut := s20Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s20StockWords) (by decide +kernel)
  · exact s20Stock
  · decide +kernel
-- s46: 20_10_60 (lb=7, vars=5, kind=2)
def s46Mask : Word := 0x30303030303030300000000000000000303030303030303
abbrev s46Goal : Word := sGoal &&& s46Mask
abbrev s46StockWords : List Word := projectDAGStock s46Mask sBase [0, 3, 4, 5, 7]
def s46Fact : Bound := (s46Mask, s46StockWords, 7, s46Goal)
def s46Witnesses := unpackWitnesses s46StockWords [4616, 266753, 532993, 803329, 1130528]
def s46Cuts : List Bound := [s44Fact, s45Fact]
def s46Chart : Option RowChart := some ⟨[9, 17, 24, 33, 160, 25, 41, 49, 56, 137, 145, 152, 40, 48, 129, 136, 144, 1, 8, 16, 32, 128, 0, 40], rfl⟩
def s46Sample : DagSample := (0x40211402450211804520984828120b01406060181808510984824510a8140a46031180e11089140e102a140a450289, 21)
def s46Links : DagLinks :=
  dagLookupLinks 0x28a28301 0x392c662023141008001f 6 3 12 2 2 5
def s46Data : Forest := fun i => decodeNode 3 15 0x92c2628402080f8 i
def s46Tags := dagTraceTags s46Mask 21 (dagTagBases s46StockWords 0x1c717a64f60dd9a926b73e0ad7 0x1c717f1c740f698184b3000007 21) 6 s46Data
def s46States := dagTrace s46Mask s46StockWords 6 s46Data
def s46Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s46Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 5, 6, 7] 0 i.val)
def s46Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 4, 3, 5, 6, 7] 0 i.val)
def s46MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s46Move0Map, s46Move0Map), ([([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)])], s46Move1Map, s46Move1Map), ([([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)]), ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s46Move2Map, s46Move2Map)]
def s46Moves := dagMoves s46MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Autos : DagMovesOK s46Mask s46Goal 256 s46Moves := dagMovesOfCheck (by decide +kernel)
def s46Check := dagCheckNode s46Mask s46Goal s46Chart (dagKnownCloses s46Goal s46Cuts) 4 s46States s46Moves s46Links s46Sample s46Tags
def s46RootAt (token : Nat) : Bool :=
  let s := rootState s46StockWords 6 token
  !dagAllowedRoot s46Witnesses s.2.1 || dagLocal s46Mask s46Goal s46Chart (dagKnownCloses s46Goal s46Cuts) s ||
  dagRef 4 s46States s46Moves s46Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46RootBlock0 : treeBlock 0 32 s46RootAt = true := by decide +kernel
theorem s46RootVerified : treeBlock 0 32 s46RootAt = true := s46RootBlock0
theorem s46Roots : dagCheckRoots s46Mask s46Goal s46Chart (dagKnownCloses s46Goal s46Cuts) s46Witnesses (dagRef 4 s46States s46Moves s46Links 0) s46StockWords 6 = true := s46RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Block0 : treeBlock 0 4 s46Check = true := by decide +kernel
theorem s46Verified : treeBlock 0 4 s46Check = true := s46Block0
theorem s46Blocks : treeBlock 0 4 s46Check = true := s46Verified
theorem s46Known : Known s46Cuts := (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s45Stock) s44Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Stock : Lower s46Mask s46StockWords s46Goal 7 := by
  apply lowerDag _ _ _ _ s46Autos _ _ _ s46Known _ s46Roots s46Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s46StockWords; decide +kernel
  · decide +kernel
  · simp only [s46Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
-- s47: 20_10 (lb=8, vars=6, kind=1)
def s47Mask : Word := 0x303030303030303030303030303030303030303030303030303030303030303
abbrev s47Goal : Word := sGoal &&& s47Mask
abbrev s47StockWords : List Word := projectDAGStock s47Mask sBase [0, 3, 4, 5, 6, 7]
def s47Fact : Bound := (s47Mask, s47StockWords, 8, s47Goal)
def s47Witnesses := unpackWitnesses s47StockWords [4616, 266753, 532993, 803329, 1147008, 1392672]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s47Stock : Lower s47Mask s47StockWords s47Goal 8 := by
  apply essentialLift (witnesses := s47Witnesses) (cut := s46Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s46StockWords) (by decide +kernel)
  · exact s46Stock
  · decide +kernel
-- s48: 20_50_70_60 (lb=5, vars=4, kind=1)
def s48Mask : Word := 0xf0f0f0f
abbrev s48Goal : Word := sGoal &&& s48Mask
abbrev s48StockWords : List Word := projectDAGStock s48Mask sBase [0, 1, 3, 4]
def s48Fact : Bound := (s48Mask, s48StockWords, 5, s48Goal)
def s48Witnesses := unpackWitnesses s48StockWords [1538, 263681, 528897, 795137]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s48Stock : Lower s48Mask s48StockWords s48Goal 5 := by
  apply essentialLift (witnesses := s48Witnesses) (cut := s1Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s1StockWords) (by decide +kernel)
  · exact s1Stock
  · decide +kernel
-- s49: 20_50_70_61 (lb=5, vars=4, kind=1)
def s49Mask : Word := 0xf0f0f0f0000000000000000
abbrev s49Goal : Word := sGoal &&& s49Mask
abbrev s49StockWords : List Word := projectDAGStock s49Mask sBase [0, 1, 3, 4]
def s49Fact : Bound := (s49Mask, s49StockWords, 5, s49Goal)
def s49Witnesses := unpackWitnesses s49StockWords [37448, 296000, 561729, 827969]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Stock : Lower s49Mask s49StockWords s49Goal 5 := by
  apply essentialLift (witnesses := s49Witnesses) (cut := s21Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s21StockWords) (by decide +kernel)
  · exact s21Stock
  · decide +kernel
-- s50: 20_50_70 (lb=7, vars=5, kind=2)
def s50Mask : Word := 0xf0f0f0f000000000f0f0f0f
abbrev s50Goal : Word := sGoal &&& s50Mask
abbrev s50StockWords : List Word := projectDAGStock s50Mask sBase [0, 1, 3, 4, 6]
def s50Fact : Bound := (s50Mask, s50StockWords, 7, s50Goal)
def s50Witnesses := unpackWitnesses s50StockWords [1538, 263681, 528897, 795137, 1082370]
def s50Cuts : List Bound := [s48Fact, s49Fact]
def s50Chart : Option RowChart := some ⟨[3, 9, 17, 24, 66, 11, 19, 25, 26, 67, 73, 74, 10, 18, 65, 72, 80, 1, 2, 8, 16, 64, 0, 10], rfl⟩
def s50Sample : DagSample := (0x100c140305024241124160a04205060240309060a05128148140b0904c241a24124904a0506882512090c8249, 20)
def s50Links : DagLinks :=
  dagLookupLinks 0x28a28301 0x792c6c408c50804001f 6 3 12 2 1 5
def s50Data : Forest := fun i => decodeNode 3 14 0xc4058a101040f8 i
def s50Tags := dagTraceTags s50Mask 20 (dagTagBases s50StockWords 0xc6371aecc2a979c53daf15a7 0xc63715ec06a138f39c800007 20) 6 s50Data
def s50States := dagTrace s50Mask s50StockWords 6 s50Data
def s50Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s50MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s50Move0Map, s50Move0Map)]
def s50Moves := dagMoves s50MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Autos : DagMovesOK s50Mask s50Goal 256 s50Moves := dagMovesOfCheck (by decide +kernel)
def s50Check := dagCheckNode s50Mask s50Goal s50Chart (dagKnownCloses s50Goal s50Cuts) 4 s50States s50Moves s50Links s50Sample s50Tags
def s50RootAt (token : Nat) : Bool :=
  let s := rootState s50StockWords 6 token
  !dagAllowedRoot s50Witnesses s.2.1 || dagLocal s50Mask s50Goal s50Chart (dagKnownCloses s50Goal s50Cuts) s ||
  dagRef 4 s50States s50Moves s50Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50RootBlock0 : treeBlock 0 32 s50RootAt = true := by decide +kernel
theorem s50RootVerified : treeBlock 0 32 s50RootAt = true := s50RootBlock0
theorem s50Roots : dagCheckRoots s50Mask s50Goal s50Chart (dagKnownCloses s50Goal s50Cuts) s50Witnesses (dagRef 4 s50States s50Moves s50Links 0) s50StockWords 6 = true := s50RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Block0 : treeBlock 0 4 s50Check = true := by decide +kernel
theorem s50Verified : treeBlock 0 4 s50Check = true := s50Block0
theorem s50Blocks : treeBlock 0 4 s50Check = true := s50Verified
theorem s50Known : Known s50Cuts := (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s49Stock) s48Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Stock : Lower s50Mask s50StockWords s50Goal 7 := by
  apply lowerDag _ _ _ _ s50Autos _ _ _ s50Known _ s50Roots s50Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s50StockWords; decide +kernel
  · decide +kernel
  · simp only [s50Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
-- s51: 20_50 (lb=8, vars=6, kind=1)
def s51Mask : Word := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
abbrev s51Goal : Word := sGoal &&& s51Mask
abbrev s51StockWords : List Word := projectDAGStock s51Mask sBase [0, 1, 3, 4, 6, 7]
def s51Fact : Bound := (s51Mask, s51StockWords, 8, s51Goal)
def s51Witnesses := unpackWitnesses s51StockWords [1538, 263681, 528897, 795137, 1082370, 1409088]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Stock : Lower s51Mask s51StockWords s51Goal 8 := by
  apply essentialLift (witnesses := s51Witnesses) (cut := s50Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s50StockWords) (by decide +kernel)
  · exact s50Stock
  · decide +kernel
-- s52: 20_60 (lb=8, vars=6, kind=1)
def s52Mask : Word := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
abbrev s52Goal : Word := sGoal &&& s52Mask
abbrev s52StockWords : List Word := projectDAGStock s52Mask sBase [0, 1, 3, 4, 5, 7]
def s52Fact : Bound := (s52Mask, s52StockWords, 8, s52Goal)
def s52Witnesses := unpackWitnesses s52StockWords [1538, 263681, 528897, 795137, 1065473, 1392672]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s52Stock : Lower s52Mask s52StockWords s52Goal 8 := by
  apply essentialLift (witnesses := s52Witnesses) (cut := s46Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s46StockWords) (by decide +kernel)
  · exact s46Stock
  · decide +kernel
-- s53: 20_70 (lb=8, vars=6, kind=1)
def s53Mask : Word := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
abbrev s53Goal : Word := sGoal &&& s53Mask
abbrev s53StockWords : List Word := projectDAGStock s53Mask sBase [0, 1, 3, 4, 5, 6]
def s53Fact : Bound := (s53Mask, s53StockWords, 8, s53Goal)
def s53Witnesses := unpackWitnesses s53StockWords [1538, 263681, 528897, 795137, 1065473, 1344514]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s53Stock : Lower s53Mask s53StockWords s53Goal 8 := by
  apply essentialLift (witnesses := s53Witnesses) (cut := s50Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s50StockWords) (by decide +kernel)
  · exact s50Stock
  · decide +kernel
-- s54: 20_61 (lb=7, vars=6, kind=1)
def s54Mask : Word := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000
abbrev s54Goal : Word := sGoal &&& s54Mask
abbrev s54StockWords : List Word := projectDAGStock s54Mask sBase [0, 1, 3, 4, 5, 7]
def s54Fact : Bound := (s54Mask, s54StockWords, 7, s54Goal)
def s54Witnesses := unpackWitnesses s54StockWords [37448, 296000, 561729, 827969, 1098305, 1409088]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s54Stock : Lower s54Mask s54StockWords s54Goal 7 := by
  apply essentialLift (witnesses := s54Witnesses) (cut := s21Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s21StockWords) (by decide +kernel)
  · exact s21Stock
  · decide +kernel
-- s55: 20_71 (lb=7, vars=6, kind=1)
def s55Mask : Word := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
abbrev s55Goal : Word := sGoal &&& s55Mask
abbrev s55StockWords : List Word := projectDAGStock s55Mask sBase [0, 1, 3, 4, 5, 6]
def s55Fact : Bound := (s55Mask, s55StockWords, 7, s55Goal)
def s55Witnesses := unpackWitnesses s55StockWords [67202, 329345, 594561, 860801, 1130624, 1409152]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Stock : Lower s55Mask s55StockWords s55Goal 7 := by
  apply essentialLift (witnesses := s55Witnesses) (cut := s20Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s20StockWords) (by decide +kernel)
  · exact s20Stock
  · decide +kernel
-- s56: 20_31 (lb=6, vars=6, kind=1)
def s56Mask : Word := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00
abbrev s56Goal : Word := sGoal &&& s56Mask
abbrev s56StockWords : List Word := projectDAGStock s56Mask sBase [0, 1, 4, 5, 6, 7]
def s56Fact : Bound := (s56Mask, s56StockWords, 6, s56Goal)
def s56Witnesses := unpackWitnesses s56StockWords [4616, 300104, 536584, 872584, 1086474, 1396776]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Stock : Lower s56Mask s56StockWords s56Goal 6 := by
  apply essentialLift (witnesses := s56Witnesses) (cut := s22Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s22StockWords) (by decide +kernel)
  · exact s22Stock
  · decide +kernel
-- s57: 20_41 (lb=6, vars=6, kind=1)
def s57Mask : Word := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000
abbrev s57Goal : Word := sGoal &&& s57Mask
abbrev s57StockWords : List Word := projectDAGStock s57Mask sBase [0, 1, 3, 5, 6, 7]
def s57Fact : Bound := (s57Mask, s57StockWords, 6, s57Goal)
def s57Witnesses := unpackWitnesses s57StockWords [8720, 304208, 536592, 876688, 1090578, 1400880]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s57Stock : Lower s57Mask s57StockWords s57Goal 6 := by
  apply essentialLift (witnesses := s57Witnesses) (cut := s23Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s23StockWords) (by decide +kernel)
  · exact s23Stock
  · decide +kernel
-- s58: 20_00_31 (lb=5, vars=5, kind=1)
def s58Mask : Word := 0x500050005000500050005000500050005000500050005000500050005000500
abbrev s58Goal : Word := sGoal &&& s58Mask
abbrev s58StockWords : List Word := projectDAGStock s58Mask sBase [1, 4, 5, 6, 7]
def s58Fact : Bound := (s58Mask, s58StockWords, 5, s58Goal)
def s58Witnesses := unpackWitnesses s58StockWords [37960, 274440, 610440, 824330, 1134632]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s58Stock : Lower s58Mask s58StockWords s58Goal 5 := by
  apply essentialLift (witnesses := s58Witnesses) (cut := s22Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s22StockWords) (by decide +kernel)
  · exact s22Stock
  · decide +kernel
-- s59: 20_00 (lb=6, vars=6, kind=2)
def s59Mask : Word := 0x505050505050505050505050505050505050505050505050505050505050505
abbrev s59Goal : Word := sGoal &&& s59Mask
abbrev s59StockWords : List Word := projectDAGStock s59Mask sBase [1, 3, 4, 5, 6, 7]
def s59Fact : Bound := (s59Mask, s59StockWords, 6, s59Goal)
def s59Witnesses := unpackWitnesses s59StockWords [33856, 274448, 536584, 868480, 1082370, 1392672]
def s59Cuts : List Bound := [s2Fact, s58Fact]
def s59Chart : Option RowChart := some ⟨[24, 66, 160, 192, 26, 56, 74, 82, 88, 98, 152, 162, 42, 50, 104, 112, 138, 146, 10, 18, 34, 40, 48, 72], rfl⟩
def s59Sample : DagSample := (0x18, 1)
def s59Links : DagLinks :=
  dagLookupLinks 0x0 0x0 2 1 1 1 2 3
def s59Data : Forest := fun i => decodeNode 1 7 0x0 i
def s59Tags := dagTraceTags s59Mask 1 (dagTagBases s59StockWords 0x6 0x0 1) 5 s59Data
def s59States := dagTrace s59Mask s59StockWords 5 s59Data
def s59Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s59Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 5, 2, 3, 4, 1, 7, 6] 0 i.val)
def s59Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 5, 2, 4, 3, 1, 7, 6] 0 i.val)
def s59MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s59Move0Map, s59Move0Map), ([([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333, 0), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x3333333300000000333333330000000033333333000000003333333300000000, 30)]), ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)])], s59Move1Map, s59Move1Map), ([([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333, 0), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x3333333300000000333333330000000033333333000000003333333300000000, 30)]), ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)]), ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s59Move2Map, s59Move2Map)]
def s59Moves := dagMoves s59MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s59Autos : DagMovesOK s59Mask s59Goal 256 s59Moves := dagMovesOfCheck (by decide +kernel)
def s59Check := dagCheckNode s59Mask s59Goal s59Chart (dagKnownCloses s59Goal s59Cuts) 0 s59States s59Moves s59Links s59Sample s59Tags
def s59RootAt (token : Nat) : Bool :=
  let s := rootState s59StockWords 5 token
  !dagAllowedRoot s59Witnesses s.2.1 || dagLocal s59Mask s59Goal s59Chart (dagKnownCloses s59Goal s59Cuts) s ||
  dagRef 0 s59States s59Moves s59Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s59RootBlock0 : treeBlock 0 64 s59RootAt = true := by decide +kernel
theorem s59RootVerified : treeBlock 0 64 s59RootAt = true := s59RootBlock0
theorem s59Roots : dagCheckRoots s59Mask s59Goal s59Chart (dagKnownCloses s59Goal s59Cuts) s59Witnesses (dagRef 0 s59States s59Moves s59Links 0) s59StockWords 5 = true := s59RootVerified
theorem s59Blocks : treeBlock 0 0 s59Check = true := rfl
theorem s59Known : Known s59Cuts := (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s58Stock) s2Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s59Stock : Lower s59Mask s59StockWords s59Goal 6 := by
  apply lowerDag _ _ _ _ s59Autos _ _ _ s59Known _ s59Roots s59Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s59StockWords; decide +kernel
  · decide +kernel
  · simp only [s59Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
-- s60: 20_01 (lb=5, vars=6, kind=0)
def s60Mask : Word := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
abbrev s60Goal : Word := sGoal &&& s60Mask
abbrev s60StockWords : List Word := projectDAGStock s60Mask sBase [1, 3, 4, 5, 6, 7]
def s60Fact : Bound := (s60Mask, s60StockWords, 5, s60Goal)
def s60Witnesses := unpackWitnesses s60StockWords [1537, 266753, 532993, 803329, 1147521, 1409601]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s60Stock : Lower s60Mask s60StockWords s60Goal 5 := by
  apply essentialLower (witnesses := s60Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s61: 20_11 (lb=5, vars=6, kind=0)
def s61Mask : Word := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
abbrev s61Goal : Word := sGoal &&& s61Mask
abbrev s61StockWords : List Word := projectDAGStock s61Mask sBase [0, 3, 4, 5, 6, 7]
def s61Fact : Bound := (s61Mask, s61StockWords, 5, s61Goal)
def s61Witnesses := unpackWitnesses s61StockWords [1538, 275474, 537610, 869506, 1082370, 1393698]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s61Stock : Lower s61Mask s61StockWords s61Goal 5 := by
  apply essentialLower (witnesses := s61Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s62: 20_51 (lb=5, vars=6, kind=0)
def s62Mask : Word := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000
abbrev s62Goal : Word := sGoal &&& s62Mask
abbrev s62StockWords : List Word := projectDAGStock s62Mask sBase [0, 1, 3, 4, 6, 7]
def s62Fact : Bound := (s62Mask, s62StockWords, 5, s62Goal)
def s62Witnesses := unpackWitnesses s62StockWords [16928, 312416, 553008, 815144, 1098786, 1392672]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s62Stock : Lower s62Mask s62StockWords s62Goal 5 := by
  apply essentialLower (witnesses := s62Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s63: x2=0 (lb=11, vars=7, kind=2)
def s63Mask : Word := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
abbrev s63Goal : Word := sGoal &&& s63Mask
abbrev s63StockWords : List Word := projectDAGStock s63Mask sBase [0, 1, 3, 4, 5, 6, 7]
def s63Fact : Bound := (s63Mask, s63StockWords, 11, s63Goal)
def s63Witnesses := unpackWitnesses s63StockWords [1538, 263681, 528897, 795137, 1065473, 1344514, 1654816]
def s63Cuts : List Bound := [s42Fact, s43Fact, s47Fact, s51Fact, s52Fact, s53Fact, s54Fact, s55Fact, s56Fact, s57Fact, s59Fact, s60Fact, s61Fact, s62Fact, s8Fact]
def s63Chart : Option RowChart := some ⟨[3, 9, 17, 24, 33, 66, 160, 192, 11, 19, 25, 26, 42, 50, 104, 112, 138, 146, 10, 18, 34, 40, 48, 65], rfl⟩
def s63Sample : DagSample := (0x1249a1508d02092412510a8150a454a81502d148b20884e0781908c6438191c8e0724088524b2192c8e07120844d04a19068d078408445438190cc541a341a502a140a0d029140a248243341a882c12098514aa150ad02c1152a8643a20944546a20924543a, 45)
def s63Links : DagLinks :=
  dagLookupLinks 0x85821608582160858216085821608582160858216085821608582160858216083160c083020c083020448102040810204081020408102040810204081020028002000800200080020007f09f257c81e857a01e807795de07781de07591d607581d607505d407501d217481d207481d207481d207481d207481d207481d207481d207481d207481d207481d207481d207215c807011c007001c007001b656d81b606d81b606a998155c9d5304fa93074538fcc34d4c282b2c90e1c403bb00f0001 0x2d1250763d10d8c383424b0c2620364942ccf4432a4b0c06207580d0d6028350100d2034344942cef447330e0cc92c2f9880d125033bd11cac3832a4b0bc620b3c940cef447230e0c892c2e9880cd25032bd10c8c382e1880c60483100d0c3250afbd11c0c383024b0bc620b04940c0f44ae30e0b86202fc940bcf442eb0e1b892c2e188280c386b24b0ac620200c50b60550d8020b5250a8bd3e82f44ecb13f90c436ab0e2b294fa4250caa92c2a193c9a6436398dc8e62b1f98826e34f968d0d64337190cac5831f118c54343142cd57276c382c19688831d1d0c50ae0490c8022ab2502b3d3caaf44a8313ea6c439c30e0a664f28190c966371c18826a34f1a8d0e54337150c7c443150c0c50a8f449eb0e1a692c2998809e342250cd98632a218c78a40550b8020a355c9f30e1a092c2818809e35a2701242c008a6d5709b250263d1294c4e6325059692c23190496620250d68520412480f64c0351300442a0082455708f2509cbd108c94222a4b08864e218d68500292100946001d1280442800820c94080f4f1fbd107cc4f1eb10c78c385da53d749435ca4dd7092c1d993c746431c98dc706209b0d3c68343958cdd5e32b178c7c42315098c506f55c1b30e16a92c1a988068314198168480121000226555c1949425ef449425086292c98190850329180c745e31417016c3e00816d5705925015bd1154c381524b0526425418d85062a1398804c342528cd84a32a1201383c00891d5704725090bd1144c381124b042620900d684034e8f0d093e3360f8ca83c31e8e01093a0360e80a83801e8d494036f4f0d3d122cc4f8bb10e26c38cca53d32943ca24dd3092c8c993c326438a18dc306200b8d3c2c3430a8cdd2832b0a0c7c2631489013c240438800dd2202b08807c200130780261b250073d3c1af4484b13e14c438330e31894f46250f0e93745a4b21864f06190e0e6370598801434f048d0c10337438cac0e31f030c520a04f02810e060374200ac0801f01804c040090080200007f 14 5 13 7 2 7
def s63Data : Forest := fun i => decodeNode 7 20 0x928560144a0204301a43928407a23d928397a23961c390243501a329281b7a219928147a21461c143101402a8f9280eaae0d32d0d0248d7a78c7a20c7a20b3100b02a8baae0a3100a1ad0a0248a928097a209310091ad0901e89aae08928084a10849608327081ad0801288928077a7877a207627876218761c07327873218731b8731007aae0661c063100618a0602d06928054960518e8518a0502d85aae04928047a204496043210431504310041a10419504027049280349603310031a7031950318f030150300f037a7827a20232182310021a7821a18219b8218f8218a020218200f8200982004827a7817a20132181310011a7811a18119b8118f8118a010218100f8100981004810040103f80 i
def s63Tags := dagTraceTags s63Mask 45 (dagTagBases s63StockWords 0x4540600795804098a843c9c9cffc5b0bb5802ef7e200cdfd40758a6df065b319336aeba262bf6ca 0x5440c08785004188e843c148e7cdde08b5803ee4400082fc0055826971e73138036a4082221f64a 45) 10 s63Data
def s63States := dagTrace s63Mask s63StockWords 10 s63Data
def s63Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s63Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 5, 2, 3, 4, 1, 7, 6] 0 i.val)
def s63Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 5, 2, 4, 3, 1, 7, 6] 0 i.val)
def s63MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s63Move0Map, s63Move0Map), ([([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333, 0), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x3333333300000000333333330000000033333333000000003333333300000000, 30)]), ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)])], s63Move1Map, s63Move1Map), ([([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333, 0), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x3333333300000000333333330000000033333333000000003333333300000000, 30)]), ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)]), ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s63Move2Map, s63Move2Map)]
def s63Moves := dagMoves s63MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63Autos : DagMovesOK s63Mask s63Goal 256 s63Moves := dagMovesOfCheck (by decide +kernel)
def s63Check := dagCheckNode s63Mask s63Goal s63Chart (dagKnownCloses s63Goal s63Cuts) 109 s63States s63Moves s63Links s63Sample s63Tags
def s63RootAt (token : Nat) : Bool :=
  let s := rootState s63StockWords 10 token
  !dagAllowedRoot s63Witnesses s.2.1 || dagLocal s63Mask s63Goal s63Chart (dagKnownCloses s63Goal s63Cuts) s ||
  dagRef 109 s63States s63Moves s63Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63RootBlock0 : treeBlock 0 64 s63RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63RootBlock64 : treeBlock 64 64 s63RootAt = true := by decide +kernel
theorem s63RootVerified : treeBlock 0 128 s63RootAt = true := (@treeBlock_merge 0 64 64 s63RootAt s63RootBlock0 s63RootBlock64)
theorem s63Roots : dagCheckRoots s63Mask s63Goal s63Chart (dagKnownCloses s63Goal s63Cuts) s63Witnesses (dagRef 109 s63States s63Moves s63Links 0) s63StockWords 10 = true := s63RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63Block0 : treeBlock 0 16 s63Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63Block16 : treeBlock 16 16 s63Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63Block32 : treeBlock 32 16 s63Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63Block48 : treeBlock 48 16 s63Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63Block64 : treeBlock 64 16 s63Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63Block80 : treeBlock 80 16 s63Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63Block96 : treeBlock 96 13 s63Check = true := by decide +kernel
theorem s63Verified : treeBlock 0 109 s63Check = true := (@treeBlock_merge 0 64 45 s63Check (@treeBlock_merge 0 32 32 s63Check (@treeBlock_merge 0 16 16 s63Check s63Block0 s63Block16) (@treeBlock_merge 32 16 16 s63Check s63Block32 s63Block48)) (@treeBlock_merge 64 32 13 s63Check (@treeBlock_merge 64 16 16 s63Check s63Block64 s63Block80) s63Block96))
theorem s63Blocks : treeBlock 0 109 s63Check = true := s63Verified
theorem s63Known : Known s63Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s8Stock) s62Stock) s61Stock) s60Stock) s59Stock) s57Stock) s56Stock) s55Stock) s54Stock) s53Stock) s52Stock) s51Stock) s47Stock) s43Stock) s42Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63Stock : Lower s63Mask s63StockWords s63Goal 11 := by
  apply lowerDag _ _ _ _ s63Autos _ _ _ s63Known _ s63Roots s63Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s63StockWords; decide +kernel
  · decide +kernel
  · simp only [s63Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
-- s64: 30_50 (lb=8, vars=6, kind=1)
def s64Mask : Word := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
abbrev s64Goal : Word := sGoal &&& s64Mask
abbrev s64StockWords : List Word := projectDAGStock s64Mask sBase [0, 1, 2, 4, 6, 7]
def s64Fact : Bound := (s64Mask, s64StockWords, 8, s64Goal)
def s64Witnesses := unpackWitnesses s64StockWords [1538, 263681, 526849, 795137, 1082370, 1409088]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s64Stock : Lower s64Mask s64StockWords s64Goal 8 := by
  apply essentialLift (witnesses := s64Witnesses) (cut := s29Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s29StockWords) (by decide +kernel)
  · exact s29Stock
  · decide +kernel
-- s65: 30_60 (lb=8, vars=6, kind=1)
def s65Mask : Word := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
abbrev s65Goal : Word := sGoal &&& s65Mask
abbrev s65StockWords : List Word := projectDAGStock s65Mask sBase [0, 1, 2, 4, 5, 7]
def s65Fact : Bound := (s65Mask, s65StockWords, 8, s65Goal)
def s65Witnesses := unpackWitnesses s65StockWords [1538, 263681, 526849, 795137, 1065473, 1392672]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s65Stock : Lower s65Mask s65StockWords s65Goal 8 := by
  apply essentialLift (witnesses := s65Witnesses) (cut := s32Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s32StockWords) (by decide +kernel)
  · exact s32Stock
  · decide +kernel
-- s66: 40_50 (lb=8, vars=6, kind=1)
def s66Mask : Word := 0xffff000000000000ffff000000000000ffff000000000000ffff
abbrev s66Goal : Word := sGoal &&& s66Mask
abbrev s66StockWords : List Word := projectDAGStock s66Mask sBase [0, 1, 2, 3, 6, 7]
def s66Fact : Bound := (s66Mask, s66StockWords, 8, s66Goal)
def s66Witnesses := unpackWitnesses s66StockWords [1538, 263681, 526849, 791041, 1082370, 1409088]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s66Stock : Lower s66Mask s66StockWords s66Goal 8 := by
  apply essentialLift (witnesses := s66Witnesses) (cut := s29Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s29StockWords) (by decide +kernel)
  · exact s29Stock
  · decide +kernel
-- s67: 40_60 (lb=8, vars=6, kind=1)
def s67Mask : Word := 0xffff0000ffff00000000000000000000ffff0000ffff
abbrev s67Goal : Word := sGoal &&& s67Mask
abbrev s67StockWords : List Word := projectDAGStock s67Mask sBase [0, 1, 2, 3, 5, 7]
def s67Fact : Bound := (s67Mask, s67StockWords, 8, s67Goal)
def s67Witnesses := unpackWitnesses s67StockWords [1538, 263681, 526849, 791041, 1065473, 1392672]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Stock : Lower s67Mask s67StockWords s67Goal 8 := by
  apply essentialLift (witnesses := s67Witnesses) (cut := s32Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s32StockWords) (by decide +kernel)
  · exact s32Stock
  · decide +kernel
-- s68: 10_60 (lb=8, vars=6, kind=1)
def s68Mask : Word := 0x333333333333333300000000000000003333333333333333
abbrev s68Goal : Word := sGoal &&& s68Mask
abbrev s68StockWords : List Word := projectDAGStock s68Mask sBase [0, 2, 3, 4, 5, 7]
def s68Fact : Bound := (s68Mask, s68StockWords, 8, s68Goal)
def s68Witnesses := unpackWitnesses s68StockWords [2564, 264705, 528897, 795137, 1065473, 1392672]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Stock : Lower s68Mask s68StockWords s68Goal 8 := by
  apply essentialLift (witnesses := s68Witnesses) (cut := s46Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s46StockWords) (by decide +kernel)
  · exact s46Stock
  · decide +kernel
-- s69: 10_61 (lb=7, vars=6, kind=1)
def s69Mask : Word := 0x3333333333333333000000000000000033333333333333330000000000000000
abbrev s69Goal : Word := sGoal &&& s69Mask
abbrev s69StockWords : List Word := projectDAGStock s69Mask sBase [0, 2, 3, 4, 5, 7]
def s69Fact : Bound := (s69Mask, s69StockWords, 7, s69Goal)
def s69Witnesses := unpackWitnesses s69StockWords [35396, 297537, 561729, 827969, 1098305, 1409088]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s69Stock : Lower s69Mask s69StockWords s69Goal 7 := by
  apply essentialLift (witnesses := s69Witnesses) (cut := s21Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s21StockWords) (by decide +kernel)
  · exact s21Stock
  · decide +kernel
-- s70: 50_61 (lb=7, vars=6, kind=1)
def s70Mask : Word := 0xffffffff000000000000000000000000ffffffff0000000000000000
abbrev s70Goal : Word := sGoal &&& s70Mask
abbrev s70StockWords : List Word := projectDAGStock s70Mask sBase [0, 1, 2, 3, 4, 7]
def s70Fact : Bound := (s70Mask, s70StockWords, 7, s70Goal)
def s70Witnesses := unpackWitnesses s70StockWords [35396, 296000, 559681, 823873, 1090113, 1409088]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s70Stock : Lower s70Mask s70StockWords s70Goal 7 := by
  apply essentialLift (witnesses := s70Witnesses) (cut := s21Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s21StockWords) (by decide +kernel)
  · exact s21Stock
  · decide +kernel
-- s71: 50_10_60 (lb=5, vars=4, kind=1)
def s71Mask : Word := 0x3333333300000000000000000000000033333333
abbrev s71Goal : Word := sGoal &&& s71Mask
abbrev s71StockWords : List Word := projectDAGStock s71Mask sBase [0, 2, 3, 4]
def s71Fact : Bound := (s71Mask, s71StockWords, 5, s71Goal)
def s71Witnesses := unpackWitnesses s71StockWords [2564, 264705, 528897, 795137]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s71Stock : Lower s71Mask s71StockWords s71Goal 5 := by
  apply essentialLift (witnesses := s71Witnesses) (cut := s1Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s1StockWords) (by decide +kernel)
  · exact s1Stock
  · decide +kernel
-- s72: 50_10_61 (lb=6, vars=5, kind=1)
def s72Mask : Word := 0x33333333000000000000000000000000333333330000000000000000
abbrev s72Goal : Word := sGoal &&& s72Mask
abbrev s72StockWords : List Word := projectDAGStock s72Mask sBase [0, 2, 3, 4, 7]
def s72Fact : Bound := (s72Mask, s72StockWords, 6, s72Goal)
def s72Witnesses := unpackWitnesses s72StockWords [35396, 297537, 561729, 827969, 1146944]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72Stock : Lower s72Mask s72StockWords s72Goal 6 := by
  apply essentialLift (witnesses := s72Witnesses) (cut := s21Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s21StockWords) (by decide +kernel)
  · exact s21Stock
  · decide +kernel
-- s73: 50_10 (lb=7, vars=6, kind=2)
def s73Mask : Word := 0x33333333000000003333333300000000333333330000000033333333
abbrev s73Goal : Word := sGoal &&& s73Mask
abbrev s73StockWords : List Word := projectDAGStock s73Mask sBase [0, 2, 3, 4, 6, 7]
def s73Fact : Bound := (s73Mask, s73StockWords, 7, s73Goal)
def s73Witnesses := unpackWitnesses s73StockWords [2564, 264705, 528897, 795137, 1147008, 1409088]
def s73Cuts : List Bound := [s71Fact, s72Fact]
def s73Chart : Option RowChart := some ⟨[5, 9, 17, 24, 192, 13, 21, 25, 28, 69, 73, 81, 76, 84, 140, 148, 12, 20, 65, 68, 72, 80, 129, 132], rfl⟩
def s73Sample : DagSample := (0x5, 1)
def s73Links : DagLinks :=
  dagLookupLinks 0x0 0x0 2 1 1 1 2 3
def s73Data : Forest := fun i => decodeNode 1 7 0x0 i
def s73Tags := dagTraceTags s73Mask 1 (dagTagBases s73StockWords 0x3 0x0 1) 6 s73Data
def s73States := dagTrace s73Mask s73StockWords 6 s73Data
def s73Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s73Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 5, 2, 3, 4, 1, 7, 6] 0 i.val)
def s73Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 5, 2, 4, 3, 1, 7, 6] 0 i.val)
def s73MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s73Move0Map, s73Move0Map), ([([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333, 0), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x3333333300000000333333330000000033333333000000003333333300000000, 30)]), ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)])], s73Move1Map, s73Move1Map), ([([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333, 0), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x3333333300000000333333330000000033333333000000003333333300000000, 30)]), ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)]), ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s73Move2Map, s73Move2Map)]
def s73Moves := dagMoves s73MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s73Autos : DagMovesOK s73Mask s73Goal 256 s73Moves := dagMovesOfCheck (by decide +kernel)
def s73Check := dagCheckNode s73Mask s73Goal s73Chart (dagKnownCloses s73Goal s73Cuts) 0 s73States s73Moves s73Links s73Sample s73Tags
def s73RootAt (token : Nat) : Bool :=
  let s := rootState s73StockWords 6 token
  !dagAllowedRoot s73Witnesses s.2.1 || dagLocal s73Mask s73Goal s73Chart (dagKnownCloses s73Goal s73Cuts) s ||
  dagRef 0 s73States s73Moves s73Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s73RootBlock0 : treeBlock 0 64 s73RootAt = true := by decide +kernel
theorem s73RootVerified : treeBlock 0 64 s73RootAt = true := s73RootBlock0
theorem s73Roots : dagCheckRoots s73Mask s73Goal s73Chart (dagKnownCloses s73Goal s73Cuts) s73Witnesses (dagRef 0 s73States s73Moves s73Links 0) s73StockWords 6 = true := s73RootVerified
theorem s73Blocks : treeBlock 0 0 s73Check = true := rfl
theorem s73Known : Known s73Cuts := (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s72Stock) s71Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s73Stock : Lower s73Mask s73StockWords s73Goal 7 := by
  apply lowerDag _ _ _ _ s73Autos _ _ _ s73Known _ s73Roots s73Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s73StockWords; decide +kernel
  · decide +kernel
  · simp only [s73Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
-- s74: 50_00 (lb=5, vars=6, kind=0)
def s74Mask : Word := 0x55555555000000005555555500000000555555550000000055555555
abbrev s74Goal : Word := sGoal &&& s74Mask
abbrev s74StockWords : List Word := projectDAGStock s74Mask sBase [1, 2, 3, 4, 6, 7]
def s74Fact : Bound := (s74Mask, s74StockWords, 5, s74Goal)
def s74Witnesses := unpackWitnesses s74StockWords [3076, 265218, 536592, 798728, 1082370, 1409088]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s74Stock : Lower s74Mask s74StockWords s74Goal 5 := by
  apply essentialLower (witnesses := s74Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s75: 50_01 (lb=5, vars=6, kind=0)
def s75Mask : Word := 0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa
abbrev s75Goal : Word := sGoal &&& s75Mask
abbrev s75StockWords : List Word := projectDAGStock s75Mask sBase [1, 2, 3, 4, 6, 7]
def s75Fact : Bound := (s75Mask, s75StockWords, 5, s75Goal)
def s75Witnesses := unpackWitnesses s75StockWords [1537, 264705, 528897, 795137, 1147521, 1409601]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s75Stock : Lower s75Mask s75StockWords s75Goal 5 := by
  apply essentialLower (witnesses := s75Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s76: 50_11 (lb=4, vars=5, kind=0)
def s76Mask : Word := 0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc
abbrev s76Goal : Word := sGoal &&& s76Mask
abbrev s76StockWords : List Word := projectDAGStock s76Mask sBase [0, 2, 3, 4, 6]
def s76Fact : Bound := (s76Mask, s76StockWords, 4, s76Goal)
def s76Witnesses := unpackWitnesses s76StockWords [1538, 265218, 537618, 799754, 1082370]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76Stock : Lower s76Mask s76StockWords s76Goal 4 := by
  apply essentialLower (witnesses := s76Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s77: 50_21 (lb=5, vars=6, kind=0)
def s77Mask : Word := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0
abbrev s77Goal : Word := sGoal &&& s77Mask
abbrev s77StockWords : List Word := projectDAGStock s77Mask sBase [0, 1, 3, 4, 6, 7]
def s77Fact : Bound := (s77Mask, s77StockWords, 5, s77Goal)
def s77Witnesses := unpackWitnesses s77StockWords [2564, 265220, 538644, 800780, 1149060, 1411140]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s77Stock : Lower s77Mask s77StockWords s77Goal 5 := by
  apply essentialLower (witnesses := s77Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s78: 50_31 (lb=5, vars=6, kind=0)
def s78Mask : Word := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00
abbrev s78Goal : Word := sGoal &&& s78Mask
abbrev s78StockWords : List Word := projectDAGStock s78Mask sBase [0, 1, 2, 4, 6, 7]
def s78Fact : Bound := (s78Mask, s78StockWords, 5, s78Goal)
def s78Witnesses := unpackWitnesses s78StockWords [4616, 269324, 531466, 798728, 1086474, 1413192]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s78Stock : Lower s78Mask s78StockWords s78Goal 5 := by
  apply essentialLower (witnesses := s78Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s79: 50_41 (lb=5, vars=6, kind=0)
def s79Mask : Word := 0xffff000000000000ffff000000000000ffff000000000000ffff0000
abbrev s79Goal : Word := sGoal &&& s79Mask
abbrev s79StockWords : List Word := projectDAGStock s79Mask sBase [0, 1, 2, 3, 6, 7]
def s79Fact : Bound := (s79Mask, s79StockWords, 5, s79Goal)
def s79Witnesses := unpackWitnesses s79StockWords [8720, 273428, 535570, 798736, 1090578, 1417296]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s79Stock : Lower s79Mask s79StockWords s79Goal 5 := by
  apply essentialLower (witnesses := s79Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s80: 60_51 (lb=5, vars=6, kind=0)
def s80Mask : Word := 0xffffffff000000000000000000000000ffffffff00000000
abbrev s80Goal : Word := sGoal &&& s80Mask
abbrev s80StockWords : List Word := projectDAGStock s80Mask sBase [0, 1, 2, 3, 4, 7]
def s80Fact : Bound := (s80Mask, s80StockWords, 5, s80Goal)
def s80Witnesses := unpackWitnesses s80StockWords [16928, 281636, 543778, 815152, 1077288, 1392672]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s80Stock : Lower s80Mask s80StockWords s80Goal 5 := by
  apply essentialLower (witnesses := s80Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s81: 60_00 (lb=5, vars=6, kind=0)
def s81Mask : Word := 0x555555555555555500000000000000005555555555555555
abbrev s81Goal : Word := sGoal &&& s81Mask
abbrev s81StockWords : List Word := projectDAGStock s81Mask sBase [1, 2, 3, 4, 5, 7]
def s81Fact : Bound := (s81Mask, s81StockWords, 5, s81Goal)
def s81Witnesses := unpackWitnesses s81StockWords [3076, 265218, 536592, 798728, 1130624, 1392672]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s81Stock : Lower s81Mask s81StockWords s81Goal 5 := by
  apply essentialLower (witnesses := s81Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s82: 60_01 (lb=4, vars=5, kind=0)
def s82Mask : Word := 0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa
abbrev s82Goal : Word := sGoal &&& s82Mask
abbrev s82StockWords : List Word := projectDAGStock s82Mask sBase [1, 2, 3, 4, 5]
def s82Fact : Bound := (s82Mask, s82StockWords, 4, s82Goal)
def s82Witnesses := unpackWitnesses s82StockWords [1537, 264705, 528897, 795137, 1065473]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s82Stock : Lower s82Mask s82StockWords s82Goal 4 := by
  apply essentialLower (witnesses := s82Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s83: 60_11 (lb=5, vars=6, kind=0)
def s83Mask : Word := 0xcccccccccccccccc0000000000000000cccccccccccccccc
abbrev s83Goal : Word := sGoal &&& s83Mask
abbrev s83StockWords : List Word := projectDAGStock s83Mask sBase [0, 2, 3, 4, 5, 7]
def s83Fact : Bound := (s83Mask, s83StockWords, 5, s83Goal)
def s83Witnesses := unpackWitnesses s83StockWords [1538, 265218, 537618, 799754, 1131650, 1393698]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s83Stock : Lower s83Mask s83StockWords s83Goal 5 := by
  apply essentialLower (witnesses := s83Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s84: 60_21 (lb=5, vars=6, kind=0)
def s84Mask : Word := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0
abbrev s84Goal : Word := sGoal &&& s84Mask
abbrev s84StockWords : List Word := projectDAGStock s84Mask sBase [0, 1, 3, 4, 5, 7]
def s84Fact : Bound := (s84Mask, s84StockWords, 5, s84Goal)
def s84Witnesses := unpackWitnesses s84StockWords [2564, 265220, 538644, 800780, 1132676, 1394724]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s84Stock : Lower s84Mask s84StockWords s84Goal 5 := by
  apply essentialLower (witnesses := s84Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s85: 60_31 (lb=5, vars=6, kind=0)
def s85Mask : Word := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00
abbrev s85Goal : Word := sGoal &&& s85Mask
abbrev s85StockWords : List Word := projectDAGStock s85Mask sBase [0, 1, 2, 4, 5, 7]
def s85Fact : Bound := (s85Mask, s85StockWords, 5, s85Goal)
def s85Witnesses := unpackWitnesses s85StockWords [4616, 269324, 531466, 798728, 1134728, 1396776]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85Stock : Lower s85Mask s85StockWords s85Goal 5 := by
  apply essentialLower (witnesses := s85Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s86: 60_41 (lb=5, vars=6, kind=0)
def s86Mask : Word := 0xffff0000ffff00000000000000000000ffff0000ffff0000
abbrev s86Goal : Word := sGoal &&& s86Mask
abbrev s86StockWords : List Word := projectDAGStock s86Mask sBase [0, 1, 2, 3, 5, 7]
def s86Fact : Bound := (s86Mask, s86StockWords, 5, s86Goal)
def s86Witnesses := unpackWitnesses s86StockWords [8720, 273428, 535570, 798736, 1138832, 1400880]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s86Stock : Lower s86Mask s86StockWords s86Goal 5 := by
  apply essentialLower (witnesses := s86Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s87: 50_70 (lb=9, vars=6, kind=1)
def s87Mask : Word := 0xffffffff00000000ffffffff
abbrev s87Goal : Word := sGoal &&& s87Mask
abbrev s87StockWords : List Word := projectDAGStock s87Mask sBase [0, 1, 2, 3, 4, 6]
def s87Fact : Bound := (s87Mask, s87StockWords, 9, s87Goal)
def s87Witnesses := unpackWitnesses s87StockWords [1538, 263681, 526849, 791041, 1057281, 1344514]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Stock : Lower s87Mask s87StockWords s87Goal 9 := by
  apply essentialLift (witnesses := s87Witnesses) (cut := s18Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s18StockWords) (by decide +kernel)
  · exact s18Stock
  · decide +kernel
-- s88: 50_71 (lb=9, vars=6, kind=1)
def s88Mask : Word := 0xffffffff00000000ffffffff00000000000000000000000000000000
abbrev s88Goal : Word := sGoal &&& s88Mask
abbrev s88StockWords : List Word := projectDAGStock s88Mask sBase [0, 1, 2, 3, 4, 6]
def s88Fact : Bound := (s88Mask, s88StockWords, 9, s88Goal)
def s88Witnesses := unpackWitnesses s88StockWords [67202, 329345, 592513, 856705, 1122945, 1409152]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s88Stock : Lower s88Mask s88StockWords s88Goal 9 := by
  apply essentialLift (witnesses := s88Witnesses) (cut := s26Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s26StockWords) (by decide +kernel)
  · exact s26Stock
  · decide +kernel
-- s89: x5=0 (lb=11, vars=7, kind=2)
def s89Mask : Word := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
abbrev s89Goal : Word := sGoal &&& s89Mask
abbrev s89StockWords : List Word := projectDAGStock s89Mask sBase [0, 1, 2, 3, 4, 6, 7]
def s89Fact : Bound := (s89Mask, s89StockWords, 11, s89Goal)
def s89Witnesses := unpackWitnesses s89StockWords [1538, 263681, 526849, 791041, 1057281, 1344514, 1671232]
def s89Cuts : List Bound := [s87Fact, s88Fact, s18Fact, s51Fact, s64Fact, s66Fact, s70Fact, s73Fact, s74Fact, s75Fact, s76Fact, s77Fact, s78Fact, s79Fact]
def s89Chart : Option RowChart := some ⟨[3, 5, 6, 9, 17, 24, 66, 192, 7, 11, 13, 14, 76, 84, 138, 140, 146, 148, 10, 12, 18, 20, 65, 68], rfl⟩
def s89Sample : DagSample := (0x98582814498454120d24c224124a84546320904a45309248326038a8554934898492603518cc2082498462080d14832a159148949258a85c4924d14862a118820526129248626170821140b04984d45328984e49269148e4522c82512092482452090d149a, 45)
def s89Links : DagLinks :=
  dagLookupLinks 0x840210084021008402100840210084021008402100840210084021008402100840210084021008402100840210084021008402100840210084020c2818e060818206081820228081fc37f01fc07f01fc07f01fc07e09f807e01f807e01f427d01f407d01f407d01f407b8dee07a0de807985e607981e417885e207881e207881e017801e007801e007785de07781de07705dc07701dc07685da07605d807601d61740dca3710dbc46f01b256c81a856a01a806a01a806a01a806811a006801a0068019a36681943650194065018e363818e063818e05e2d5ed51b12cd44b4fac3a24d0c2d389cc1e4860c11b427000c8001 0x4401421c071098708092c363102181010a03884c383fc961ad8810608082028c08202040d1018707f92c353105ff0e0ff258696203f01e1f4100f80687c6343c8081ec090f40507901c3c80e1e0d32ec680723343b9a65d0d00e8669730403981a1c00a2f18707892c3bb101bc020ed8707592c3a3101cc044dc01172c38394961c5880e00226d008379a65b8d00dc6686d3283661c1ae4b0d4c416bc3835c961a5882d58706a92c34b101a3d10c8c82606202e9a0934c508e0826703da201a9100a4700261a0083361c5964dcbf2595e6372bb1594988498c41483371f1958dcc7c58636243150c98a197d10c988463c3831321158cd4b66524b3141e81a9840c4860523b01d0c00457f0e0c126e5f92cad31b9698aca2c424a620a119b908cac6c63e2b31b1198a85cc50bde885dc422e61c1598d4b6c525a6202c9a1140c506a06a58031208148c40442c01157f442be1c55a508ad26c5592d2a49613cc5068052530251d00e8c00442a01152f442961c1464b2a0c845063627b150bcc74286284e00ea661c1364dc992594b63725b159298828066e4032b1c98f888c54266284900f247a211f1088d87a45c38224a10f58d486c52426201a99a904ca4806283f042170098840227de883ec389eca10f64d8792593b6421db1b0d0ca47463a39314168090800226fe8838c431be1c0da4b26ac84356361a3150cd89464c41313421899b0c0ca85e6292e0431701b8b40a85401a1f008967a20b30e0572582a31d0f18a0a413250085270401401b09c0d04c05425028927a20930e04725822620909a1084cd8406541f31e0f18d4741083a06c1c02a0d80f4670e03526e1992c8c31b8618ac2ec41163370b195854c7c2862a133148901b8480ac2203e1001307807c370e01d26e0d92c8631b8318ac16c410a33705195824c7c1062a073148301b8180ac0a03e0401301807808024020100007f 14 5 12 8 1 7
def s89Data : Forest := fun i => decodeNode 8 20 0x286801c680406201c62c3860040590285903454c384d92c4b03c490404663440024370283301c2e92c2a6202ac382892c28620280112892c26620260112634c1f3341f3281fc381a92c1892c1462014f440f03d0fc380ef440dc420dc380d6420d0310d9370c92c0cf440bc420bc380b6290b6200b3420b0310bc380a9360a92d0a92c0a0250ac380992c096360962a0900e099370892c0862b086200800f08f4407c4207c3d07c3807942076290762007329073140704207c38069360692c066360631d0631406c4305c380592c056360562a0562505620053360532a05314050370502a05c380492c0431d0404c04036040340402a0402804c380392c03620033360332a0331e0331a030360302a0301e039370292c0262b026200232b0231f02315023140202b0201f020130200f029370192c0162b016200132b0131f01315013140102b0101f010130100f01009010080107f00 i
def s89Tags := dagTraceTags s89Mask 45 (dagTagBases s89StockWords 0xcb245b12b87bf3a9255e3d80180b830918593c2853f4910cd2dd951063d0f5d87c6ec56b491c3e 0xcb245b12b879a6dd276a3c94580ba4080a5d3aa253b0d18dd24a940061902d885c20000a01181e 45) 10 s89Data
def s89States := dagTrace s89Mask s89StockWords 10 s89Data
def s89Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s89MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s89Move0Map, s89Move0Map)]
def s89Moves := dagMoves s89MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89Autos : DagMovesOK s89Mask s89Goal 256 s89Moves := dagMovesOfCheck (by decide +kernel)
def s89Check := dagCheckNode s89Mask s89Goal s89Chart (dagKnownCloses s89Goal s89Cuts) 137 s89States s89Moves s89Links s89Sample s89Tags
def s89RootAt (token : Nat) : Bool :=
  let s := rootState s89StockWords 10 token
  !dagAllowedRoot s89Witnesses s.2.1 || dagLocal s89Mask s89Goal s89Chart (dagKnownCloses s89Goal s89Cuts) s ||
  dagRef 137 s89States s89Moves s89Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89RootBlock0 : treeBlock 0 64 s89RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89RootBlock64 : treeBlock 64 64 s89RootAt = true := by decide +kernel
theorem s89RootVerified : treeBlock 0 128 s89RootAt = true := (@treeBlock_merge 0 64 64 s89RootAt s89RootBlock0 s89RootBlock64)
theorem s89Roots : dagCheckRoots s89Mask s89Goal s89Chart (dagKnownCloses s89Goal s89Cuts) s89Witnesses (dagRef 137 s89States s89Moves s89Links 0) s89StockWords 10 = true := s89RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89Block0 : treeBlock 0 16 s89Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89Block16 : treeBlock 16 16 s89Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89Block32 : treeBlock 32 16 s89Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89Block48 : treeBlock 48 16 s89Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89Block64 : treeBlock 64 16 s89Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89Block80 : treeBlock 80 16 s89Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89Block96 : treeBlock 96 16 s89Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89Block112 : treeBlock 112 16 s89Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89Block128 : treeBlock 128 9 s89Check = true := by decide +kernel
theorem s89Verified : treeBlock 0 137 s89Check = true := (@treeBlock_merge 0 80 57 s89Check (@treeBlock_merge 0 48 32 s89Check (@treeBlock_merge 0 32 16 s89Check (@treeBlock_merge 0 16 16 s89Check s89Block0 s89Block16) s89Block32) (@treeBlock_merge 48 16 16 s89Check s89Block48 s89Block64)) (@treeBlock_merge 80 32 25 s89Check (@treeBlock_merge 80 16 16 s89Check s89Block80 s89Block96) (@treeBlock_merge 112 16 9 s89Check s89Block112 s89Block128)))
theorem s89Blocks : treeBlock 0 137 s89Check = true := s89Verified
theorem s89Known : Known s89Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s79Stock) s78Stock) s77Stock) s76Stock) s75Stock) s74Stock) s73Stock) s70Stock) s66Stock) s64Stock) s51Stock) s18Stock) s88Stock) s87Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89Stock : Lower s89Mask s89StockWords s89Goal 11 := by
  apply lowerDag _ _ _ _ s89Autos _ _ _ s89Known _ s89Roots s89Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s89StockWords; decide +kernel
  · decide +kernel
  · simp only [s89Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
-- s90: 60_70 (lb=9, vars=6, kind=1)
def s90Mask : Word := 0xffffffffffffffff
abbrev s90Goal : Word := sGoal &&& s90Mask
abbrev s90StockWords : List Word := projectDAGStock s90Mask sBase [0, 1, 2, 3, 4, 5]
def s90Fact : Bound := (s90Mask, s90StockWords, 9, s90Goal)
def s90Witnesses := unpackWitnesses s90StockWords [1538, 263681, 526849, 791041, 1057281, 1327617]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s90Stock : Lower s90Mask s90StockWords s90Goal 9 := by
  apply essentialLift (witnesses := s90Witnesses) (cut := s18Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s18StockWords) (by decide +kernel)
  · exact s18Stock
  · decide +kernel
-- s91: 60_71 (lb=9, vars=6, kind=1)
def s91Mask : Word := 0xffffffffffffffff00000000000000000000000000000000
abbrev s91Goal : Word := sGoal &&& s91Mask
abbrev s91StockWords : List Word := projectDAGStock s91Mask sBase [0, 1, 2, 3, 4, 5]
def s91Fact : Bound := (s91Mask, s91StockWords, 9, s91Goal)
def s91Witnesses := unpackWitnesses s91StockWords [67202, 329345, 592513, 856705, 1122945, 1392768]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s91Stock : Lower s91Mask s91StockWords s91Goal 9 := by
  apply essentialLift (witnesses := s91Witnesses) (cut := s26Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s26StockWords) (by decide +kernel)
  · exact s26Stock
  · decide +kernel
-- s92: x6=0 (lb=11, vars=7, kind=2)
def s92Mask : Word := 0xffffffffffffffff0000000000000000ffffffffffffffff
abbrev s92Goal : Word := sGoal &&& s92Mask
abbrev s92StockWords : List Word := projectDAGStock s92Mask sBase [0, 1, 2, 3, 4, 5, 7]
def s92Fact : Bound := (s92Mask, s92StockWords, 11, s92Goal)
def s92Witnesses := unpackWitnesses s92StockWords [1538, 263681, 526849, 791041, 1057281, 1327617, 1654816]
def s92Cuts : List Bound := [s90Fact, s91Fact, s18Fact, s52Fact, s65Fact, s67Fact, s68Fact, s80Fact, s81Fact, s82Fact, s83Fact, s84Fact, s85Fact, s86Fact]
def s92Chart : Option RowChart := some ⟨[3, 5, 6, 9, 17, 24, 33, 160, 7, 11, 13, 14, 42, 44, 50, 52, 138, 140, 146, 148, 10, 12, 18, 20], rfl⟩
def s92Sample : DagSample := (0x68251a0e118a8140606018160a45838150a454381a0d928b41908c50291508c60311502c64331a0d460381a0985038160b46436492c8580e150385826462b0683c19098583c160b8542b40a0d02a11509914aa19068541a190e8542e40a45028540a24543a, 45)
def s92Links : DagLinks :=
  dagLookupLinks 0x2840a1028219f8a7e09f827e09f827e09f827e09f827e09f827e09f827e09f827c19f027c09f027c09f027c09f027c09e0a7429c866e29b066c09b02682990a640980a5c297025c097025c0949652094825209482520938a4a29282462908a42090824018f863c18e0a3618d823608c8a3208b8a2e08b822e08b822e08b062a18a822a0890e202868e1a08682162848a120848212084821208482120848212082920248081f667a99ea0790dceb7289ca06f1dbc06d11b406b8d98b660192364818c3630186361817a65e057615a1d680588d585548d4854e212e54b052a148151c24609180458516045810e443810e0420d08037d4b9328ac7380fe822e00c0001 0xc899a191624122660240c6147b1418f34011f278238cd046e2008dc3c8f40511ec0724602008c0289020522040444602608b0409000521fc044450260890409040689f80a03f00e1880401100689f40743e80888804c10e0809f00743e00888231c0fc6382100224302008602810b8782100a14200e084028106038208cf03d80e08104c1000801fc0a03f19807a01c0fa0985f01003e01a07a3340f66505e98d83d3154790420f20541e00483b807068c4c0ed8909d58a0ba9a01753350ea63a1201043901a9480292e403b14f1303a624073c400906981c8d02208140710588e00981c00a22319a84631d0de09a1b81323682146c0418d60801b40a83601486b0280d40101a253034ca4068c420cf87014c0d433018c4a02948a03a114044b28210650360c802418c0383102c16104c0c2080910ca42218e86004d0be098578108ae82095c0400bc06c1740d42e01a05b0088b587016a4b01d31015ac380b52580e588229b2605964809469814d9002c31e05463408a680124cd1208140570240a2c4914f10a2ae1e856c380a6c6a1558c82a3149483422a728414e4d8294961519420a326c1424b0a39a10473360a126013c0d01d80e14e04209c06c1340a82601484b0280958841158d424b1484834208e6321180c42181484101e28b2841164d82201284201d08003810ccd021194341642482c6c5041082081b04001c07a0800fc0f01e01a03e0300760384f59081eb1b03c62a0760224eb0e01d496039620071e890d310e16621037c3906d8700d590c1a31b82c635866c52891880199a103204306206e0700d41801982f03182c05287c07c0b00881100901401149bd1017621c26c3825b2864b250816c9b82c93605725a0aa4b290821c210370520560680a41401382702542a03a0540440800480900824b87009a4dc12c96124637048c5608d8801119bc2032b43c63e03cc540418a120f440438860830e08fca181f93703d25847590c8e32101d637038c6c06d8ac0d315019625030c4205d8808b1a101633602a65445010c0a01b81302b0240540380240680450ff4482188703f0e188ca1a1193741f25844590c08b1b81062b01ec41438d0e869a140e33781a66c838cad0699500e31f01a63d43010e8582140c03781606c8300ad0581500c01f01603d4230e204c9bc0892c614c6e8298ad0431010a337014656024c7c0418a50703780e05681c07c03809d04c3880b26f0124b18331ba0662b408c40418cdc0319580531f00862940c0de01815a0301f0060260080240080400007f 14 5 12 8 3 7
def s92Data : Forest := fun i => decodeNode 8 20 0x3308f3188093c7633476c3c7404c6d0406d04c670406704c5e0405e02857c3c560285101c5133c4b04c4704047028473304604c45034453284262a4102a370123700e37c483631d34c4833c403334033058310283104d3004c3002a300293002830008309482fc422dc382d0312d0362b0122b00e2b058290402904d2804c280362803528034280082892c246482263c200241fc381d6321d6291d9361b92c1b9361a93019034190361802a180291802818c421762917342173191703117936160251633415328140361301c1303c12030116360c62a0c0110c92c0962009f4407c3907c380764307637073420704307037070330703107c4306937069360692d0692c0602b0602706025069370592c0562b056200533705c4304c38049370492c04637046360462b0462a046250462104620043360432a040370402b0402a046370362b036200331f0331e0301f0301e0332b0231f02314020130232b0131f013140101301009010080107f00 i
def s92Tags := dagTraceTags s92Mask 45 (dagTagBases s92StockWords 0x10100088343b9ffbfcfee62b5c5d6140e97f892cdb8f9c0302b7f885001564f977e30a3f8801c0e 0x10100088343b7f7ffbbe5e390e5e6180a0378d0cf39a8f3302a5d800006560d127e200000000c0e 45) 10 s92Data
def s92States := dagTrace s92Mask s92StockWords 10 s92Data
def s92Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s92Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 5, 6, 7] 0 i.val)
def s92Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 4, 3, 5, 6, 7] 0 i.val)
def s92Move3Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 3, 4, 1, 2, 5, 6, 7] 0 i.val)
def s92Move4Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 3, 2, 1, 5, 6, 7] 0 i.val)
def s92MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s92Move0Map, s92Move0Map), ([([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)])], s92Move1Map, s92Move1Map), ([([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)]), ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s92Move2Map, s92Move2Map), ([([(0xcc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33, 0), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0x3300330033003300330033003300330033003300330033003300330033003300, 6)]), ([(0xf0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0f, 0), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000, 12)])], s92Move3Map, s92Move3Map), ([([(0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333, 0), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x3333000033330000333300003333000033330000333300003333000033330000, 14)]), ([(0xf00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f, 0), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 4)])], s92Move4Map, s92Move4Map)]
def s92Moves := dagMoves s92MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Autos : DagMovesOK s92Mask s92Goal 256 s92Moves := dagMovesOfCheck (by decide +kernel)
def s92Check := dagCheckNode s92Mask s92Goal s92Chart (dagKnownCloses s92Goal s92Cuts) 146 s92States s92Moves s92Links s92Sample s92Tags
def s92RootAt (token : Nat) : Bool :=
  let s := rootState s92StockWords 10 token
  !dagAllowedRoot s92Witnesses s.2.1 || dagLocal s92Mask s92Goal s92Chart (dagKnownCloses s92Goal s92Cuts) s ||
  dagRef 146 s92States s92Moves s92Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92RootBlock0 : treeBlock 0 64 s92RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92RootBlock64 : treeBlock 64 64 s92RootAt = true := by decide +kernel
theorem s92RootVerified : treeBlock 0 128 s92RootAt = true := (@treeBlock_merge 0 64 64 s92RootAt s92RootBlock0 s92RootBlock64)
theorem s92Roots : dagCheckRoots s92Mask s92Goal s92Chart (dagKnownCloses s92Goal s92Cuts) s92Witnesses (dagRef 146 s92States s92Moves s92Links 0) s92StockWords 10 = true := s92RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Block0 : treeBlock 0 16 s92Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Block16 : treeBlock 16 16 s92Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Block32 : treeBlock 32 16 s92Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Block48 : treeBlock 48 16 s92Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Block64 : treeBlock 64 16 s92Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Block80 : treeBlock 80 16 s92Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Block96 : treeBlock 96 16 s92Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Block112 : treeBlock 112 16 s92Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Block128 : treeBlock 128 16 s92Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Block144 : treeBlock 144 2 s92Check = true := by decide +kernel
theorem s92Verified : treeBlock 0 146 s92Check = true := (@treeBlock_merge 0 80 66 s92Check (@treeBlock_merge 0 48 32 s92Check (@treeBlock_merge 0 32 16 s92Check (@treeBlock_merge 0 16 16 s92Check s92Block0 s92Block16) s92Block32) (@treeBlock_merge 48 16 16 s92Check s92Block48 s92Block64)) (@treeBlock_merge 80 48 18 s92Check (@treeBlock_merge 80 32 16 s92Check (@treeBlock_merge 80 16 16 s92Check s92Block80 s92Block96) s92Block112) (@treeBlock_merge 128 16 2 s92Check s92Block128 s92Block144)))
theorem s92Blocks : treeBlock 0 146 s92Check = true := s92Verified
theorem s92Known : Known s92Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s86Stock) s85Stock) s84Stock) s83Stock) s82Stock) s81Stock) s80Stock) s68Stock) s67Stock) s65Stock) s52Stock) s18Stock) s91Stock) s90Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Stock : Lower s92Mask s92StockWords s92Goal 11 := by
  apply lowerDag _ _ _ _ s92Autos _ _ _ s92Known _ s92Roots s92Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s92StockWords; decide +kernel
  · decide +kernel
  · simp only [s92Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
-- s93: x7=0 (lb=10, vars=7, kind=1)
def s93Mask : Word := 0xffffffffffffffffffffffffffffffff
abbrev s93Goal : Word := sGoal &&& s93Mask
abbrev s93StockWords : List Word := projectDAGStock s93Mask sBase [0, 1, 2, 3, 4, 5, 6]
def s93Fact : Bound := (s93Mask, s93StockWords, 10, s93Goal)
def s93Witnesses := unpackWitnesses s93StockWords [1538, 263681, 526849, 791041, 1057281, 1327617, 1606658]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s93Stock : Lower s93Mask s93StockWords s93Goal 10 := by
  apply essentialLift (witnesses := s93Witnesses) (cut := s18Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s18StockWords) (by decide +kernel)
  · exact s18Stock
  · decide +kernel
-- s94: x7=1 (lb=10, vars=7, kind=1)
def s94Mask : Word := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
abbrev s94Goal : Word := sGoal &&& s94Mask
abbrev s94StockWords : List Word := projectDAGStock s94Mask sBase [0, 1, 2, 3, 4, 5, 6]
def s94Fact : Bound := (s94Mask, s94StockWords, 10, s94Goal)
def s94Witnesses := unpackWitnesses s94StockWords [67202, 329345, 592513, 856705, 1122945, 1392768, 1671296]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94Stock : Lower s94Mask s94StockWords s94Goal 10 := by
  apply essentialLift (witnesses := s94Witnesses) (cut := s26Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s26StockWords) (by decide +kernel)
  · exact s26Stock
  · decide +kernel
-- s95: x3=0 (lb=10, vars=7, kind=1)
def s95Mask : Word := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
abbrev s95Goal : Word := sGoal &&& s95Mask
abbrev s95StockWords : List Word := projectDAGStock s95Mask sBase [0, 1, 2, 4, 5, 6, 7]
def s95Fact : Bound := (s95Mask, s95StockWords, 10, s95Goal)
def s95Witnesses := unpackWitnesses s95StockWords [1538, 263681, 526849, 795137, 1065473, 1344514, 1654816]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s95Stock : Lower s95Mask s95StockWords s95Goal 10 := by
  apply essentialLift (witnesses := s95Witnesses) (cut := s41Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s41StockWords) (by decide +kernel)
  · exact s41Stock
  · decide +kernel
-- s96: x4=0 (lb=10, vars=7, kind=1)
def s96Mask : Word := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
abbrev s96Goal : Word := sGoal &&& s96Mask
abbrev s96StockWords : List Word := projectDAGStock s96Mask sBase [0, 1, 2, 3, 5, 6, 7]
def s96Fact : Bound := (s96Mask, s96StockWords, 10, s96Goal)
def s96Witnesses := unpackWitnesses s96StockWords [1538, 263681, 526849, 791041, 1065473, 1344514, 1654816]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Stock : Lower s96Mask s96StockWords s96Goal 10 := by
  apply essentialLift (witnesses := s96Witnesses) (cut := s41Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s41StockWords) (by decide +kernel)
  · exact s41Stock
  · decide +kernel
-- s97: x1=0 (lb=9, vars=7, kind=2)
def s97Mask : Word := 0x3333333333333333333333333333333333333333333333333333333333333333
abbrev s97Goal : Word := sGoal &&& s97Mask
abbrev s97StockWords : List Word := projectDAGStock s97Mask sBase [0, 2, 3, 4, 5, 6, 7]
def s97Fact : Bound := (s97Mask, s97StockWords, 9, s97Goal)
def s97Witnesses := unpackWitnesses s97StockWords [2564, 264705, 528897, 795137, 1065473, 1409152, 1654816]
def s97Cuts : List Bound := [s68Fact, s69Fact, s47Fact]
def s97Chart : Option RowChart := some ⟨[5, 9, 17, 24, 33, 160, 192, 13, 21, 25, 28, 37, 108, 116, 44, 52, 76, 84, 100, 104, 112, 140, 148, 12], rfl⟩
def s97Sample : DagSample := (0x5, 1)
def s97Links : DagLinks :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 3
def s97Data : Forest := fun i => decodeNode 1 8 0x0 i
def s97Tags := dagTraceTags s97Mask 1 (dagTagBases s97StockWords 0x3 0x0 1) 8 s97Data
def s97States := dagTrace s97Mask s97StockWords 8 s97Data
def s97Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s97MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s97Move0Map, s97Move0Map)]
def s97Moves := dagMoves s97MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s97Autos : DagMovesOK s97Mask s97Goal 256 s97Moves := dagMovesOfCheck (by decide +kernel)
def s97Check := dagCheckNode s97Mask s97Goal s97Chart (dagKnownCloses s97Goal s97Cuts) 0 s97States s97Moves s97Links s97Sample s97Tags
def s97RootAt (token : Nat) : Bool :=
  let s := rootState s97StockWords 8 token
  !dagAllowedRoot s97Witnesses s.2.1 || dagLocal s97Mask s97Goal s97Chart (dagKnownCloses s97Goal s97Cuts) s ||
  dagRef 0 s97States s97Moves s97Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s97RootBlock0 : treeBlock 0 64 s97RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s97RootBlock64 : treeBlock 64 64 s97RootAt = true := by decide +kernel
theorem s97RootVerified : treeBlock 0 128 s97RootAt = true := (@treeBlock_merge 0 64 64 s97RootAt s97RootBlock0 s97RootBlock64)
theorem s97Roots : dagCheckRoots s97Mask s97Goal s97Chart (dagKnownCloses s97Goal s97Cuts) s97Witnesses (dagRef 0 s97States s97Moves s97Links 0) s97StockWords 8 = true := s97RootVerified
theorem s97Blocks : treeBlock 0 0 s97Check = true := rfl
theorem s97Known : Known s97Cuts := (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s47Stock) s69Stock) s68Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s97Stock : Lower s97Mask s97StockWords s97Goal 9 := by
  apply lowerDag _ _ _ _ s97Autos _ _ _ s97Known _ s97Roots s97Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s97StockWords; decide +kernel
  · decide +kernel
  · simp only [s97Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl <;> decide +kernel
-- s98: 00_31 (lb=6, vars=6, kind=1)
def s98Mask : Word := 0x5500550055005500550055005500550055005500550055005500550055005500
abbrev s98Goal : Word := sGoal &&& s98Mask
abbrev s98StockWords : List Word := projectDAGStock s98Mask sBase [1, 2, 4, 5, 6, 7]
def s98Fact : Bound := (s98Mask, s98StockWords, 6, s98Goal)
def s98Witnesses := unpackWitnesses s98StockWords [7180, 269322, 536584, 872584, 1086474, 1396776]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s98Stock : Lower s98Mask s98StockWords s98Goal 6 := by
  apply essentialLift (witnesses := s98Witnesses) (cut := s24Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s24StockWords) (by decide +kernel)
  · exact s24Stock
  · decide +kernel
-- s99: x0=0 (lb=7, vars=7, kind=2)
def s99Mask : Word := 0x5555555555555555555555555555555555555555555555555555555555555555
abbrev s99Goal : Word := sGoal &&& s99Mask
abbrev s99StockWords : List Word := projectDAGStock s99Mask sBase [1, 2, 3, 4, 5, 6, 7]
def s99Fact : Bound := (s99Mask, s99StockWords, 7, s99Goal)
def s99Witnesses := unpackWitnesses s99StockWords [3076, 265218, 536592, 798728, 1130624, 1344514, 1654816]
def s99Cuts : List Bound := [s3Fact, s98Fact]
def s99Chart : Option RowChart := some ⟨[6, 24, 66, 160, 192, 14, 22, 26, 28, 38, 56, 70, 108, 116, 42, 44, 50, 52, 76, 84, 100, 104, 112, 138], rfl⟩
def s99Sample : DagSample := (0x6, 1)
def s99Links : DagLinks :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 3
def s99Data : Forest := fun i => decodeNode 1 8 0x0 i
def s99Tags := dagTraceTags s99Mask 1 (dagTagBases s99StockWords 0x3 0x0 1) 6 s99Data
def s99States := dagTrace s99Mask s99StockWords 6 s99Data
def s99Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s99MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s99Move0Map, s99Move0Map)]
def s99Moves := dagMoves s99MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s99Autos : DagMovesOK s99Mask s99Goal 256 s99Moves := dagMovesOfCheck (by decide +kernel)
def s99Check := dagCheckNode s99Mask s99Goal s99Chart (dagKnownCloses s99Goal s99Cuts) 0 s99States s99Moves s99Links s99Sample s99Tags
def s99RootAt (token : Nat) : Bool :=
  let s := rootState s99StockWords 6 token
  !dagAllowedRoot s99Witnesses s.2.1 || dagLocal s99Mask s99Goal s99Chart (dagKnownCloses s99Goal s99Cuts) s ||
  dagRef 0 s99States s99Moves s99Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s99RootBlock0 : treeBlock 0 64 s99RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s99RootBlock64 : treeBlock 64 64 s99RootAt = true := by decide +kernel
theorem s99RootVerified : treeBlock 0 128 s99RootAt = true := (@treeBlock_merge 0 64 64 s99RootAt s99RootBlock0 s99RootBlock64)
theorem s99Roots : dagCheckRoots s99Mask s99Goal s99Chart (dagKnownCloses s99Goal s99Cuts) s99Witnesses (dagRef 0 s99States s99Moves s99Links 0) s99StockWords 6 = true := s99RootVerified
theorem s99Blocks : treeBlock 0 0 s99Check = true := rfl
theorem s99Known : Known s99Cuts := (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s98Stock) s3Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s99Stock : Lower s99Mask s99StockWords s99Goal 7 := by
  apply lowerDag _ _ _ _ s99Autos _ _ _ s99Known _ s99Roots s99Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s99StockWords; decide +kernel
  · decide +kernel
  · simp only [s99Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
-- s100: x6=1 (lb=8, vars=7, kind=1)
def s100Mask : Word := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
abbrev s100Goal : Word := sGoal &&& s100Mask
abbrev s100StockWords : List Word := projectDAGStock s100Mask sBase [0, 1, 2, 3, 4, 5, 7]
def s100Fact : Bound := (s100Mask, s100StockWords, 8, s100Goal)
def s100Witnesses := unpackWitnesses s100StockWords [35396, 296000, 559681, 823873, 1090113, 1360449, 1671232]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s100Stock : Lower s100Mask s100StockWords s100Goal 8 := by
  apply essentialLift (witnesses := s100Witnesses) (cut := s21Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s21StockWords) (by decide +kernel)
  · exact s21Stock
  · decide +kernel
-- s101: x3=1 (lb=7, vars=7, kind=1)
def s101Mask : Word := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
abbrev s101Goal : Word := sGoal &&& s101Mask
abbrev s101StockWords : List Word := projectDAGStock s101Mask sBase [0, 1, 2, 4, 5, 6, 7]
def s101Fact : Bound := (s101Mask, s101StockWords, 7, s101Goal)
def s101Witnesses := unpackWitnesses s101StockWords [4616, 269324, 531466, 798728, 1134728, 1348618, 1658920]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s101Stock : Lower s101Mask s101StockWords s101Goal 7 := by
  apply essentialLift (witnesses := s101Witnesses) (cut := s24Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s24StockWords) (by decide +kernel)
  · exact s24Stock
  · decide +kernel
-- s102: x4=1 (lb=7, vars=7, kind=1)
def s102Mask : Word := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
abbrev s102Goal : Word := sGoal &&& s102Mask
abbrev s102StockWords : List Word := projectDAGStock s102Mask sBase [0, 1, 2, 3, 5, 6, 7]
def s102Fact : Bound := (s102Mask, s102StockWords, 7, s102Goal)
def s102Witnesses := unpackWitnesses s102StockWords [8720, 273428, 535570, 798736, 1138832, 1352722, 1663024]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s102Stock : Lower s102Mask s102StockWords s102Goal 7 := by
  apply essentialLift (witnesses := s102Witnesses) (cut := s25Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s25StockWords) (by decide +kernel)
  · exact s25Stock
  · decide +kernel
-- s103: x0=1 (lb=6, vars=7, kind=0)
def s103Mask : Word := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
abbrev s103Goal : Word := sGoal &&& s103Mask
abbrev s103StockWords : List Word := projectDAGStock s103Mask sBase [1, 2, 3, 4, 5, 6, 7]
def s103Fact : Bound := (s103Mask, s103StockWords, 6, s103Goal)
def s103Witnesses := unpackWitnesses s103StockWords [1537, 264705, 528897, 795137, 1065473, 1409665, 1671745]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Stock : Lower s103Mask s103StockWords s103Goal 6 := by
  apply essentialLower (witnesses := s103Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s104: x1=1 (lb=6, vars=7, kind=0)
def s104Mask : Word := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
abbrev s104Goal : Word := sGoal &&& s104Mask
abbrev s104StockWords : List Word := projectDAGStock s104Mask sBase [0, 2, 3, 4, 5, 6, 7]
def s104Fact : Bound := (s104Mask, s104StockWords, 6, s104Goal)
def s104Witnesses := unpackWitnesses s104StockWords [1538, 265218, 537618, 799754, 1131650, 1344514, 1655842]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s104Stock : Lower s104Mask s104StockWords s104Goal 6 := by
  apply essentialLower (witnesses := s104Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s105: x2=1 (lb=6, vars=7, kind=0)
def s105Mask : Word := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
abbrev s105Goal : Word := sGoal &&& s105Mask
abbrev s105StockWords : List Word := projectDAGStock s105Mask sBase [0, 1, 3, 4, 5, 6, 7]
def s105Fact : Bound := (s105Mask, s105StockWords, 6, s105Goal)
def s105Witnesses := unpackWitnesses s105StockWords [2564, 265220, 538644, 800780, 1132676, 1411204, 1656868]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s105Stock : Lower s105Mask s105StockWords s105Goal 6 := by
  apply essentialLower (witnesses := s105Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s106: x5=1 (lb=6, vars=7, kind=0)
def s106Mask : Word := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
abbrev s106Goal : Word := sGoal &&& s106Mask
abbrev s106StockWords : List Word := projectDAGStock s106Mask sBase [0, 1, 2, 3, 4, 6, 7]
def s106Fact : Bound := (s106Mask, s106StockWords, 6, s106Goal)
def s106Witnesses := unpackWitnesses s106StockWords [16928, 281636, 543778, 815152, 1077288, 1360930, 1654816]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s106Stock : Lower s106Mask s106StockWords s106Goal 6 := by
  apply essentialLower (witnesses := s106Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s107: FULL_8515 (lb=13, vars=8, kind=2)
def s107Mask : Word := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
abbrev s107Goal : Word := sGoal &&& s107Mask
abbrev s107StockWords : List Word := projectDAGStock s107Mask sBase [0, 1, 2, 3, 4, 5, 6, 7]
def s107Fact : Bound := (s107Mask, s107StockWords, 13, s107Goal)
def s107Witnesses := unpackWitnesses s107StockWords [1538, 263681, 526849, 791041, 1057281, 1327617, 1606658, 1916960]
def s107Cuts : List Bound := [s63Fact, s92Fact, s89Fact, s95Fact, s97Fact, s96Fact, s94Fact, s93Fact, s99Fact, s101Fact, s103Fact, s104Fact, s102Fact, s100Fact, s106Fact, s105Fact, s42Fact, s43Fact, s64Fact, s66Fact, s65Fact, s67Fact, s18Fact]
def s107Chart : Option RowChart := some ⟨[3, 5, 6, 9, 17, 24, 33, 66, 160, 192, 7, 11, 108, 116, 42, 44, 50, 52, 76, 84, 100, 104, 112, 138], rfl⟩
def s107Sample : DagSample := (0x64b21502d241a40844d869360b524b24603854622080cd82e3a19864723a1f08211150986436361b5020540884641a150acd84e361a8d87c1506864263a1d914aa190e8540e2081454aa20884542e20984824940b04546a20914d86e2090c543a2094482c1, 45)
def s107Links : DagLinks :=
  dagLookupLinks 0xa9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a9a0a981a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a980a923a920a920a920a920a920a920a920a901a900a900a900a900a900a900a8e1a8e0a8e0a8e0a8e0a8e0a8e0a8e0a8e0a8e0a8e0a8e0a8e0a8e0a8e0a8e0a8e0a8e0a8e0a8e0a8e0a8e0a8e0a8e0a8c1a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8c0a8a1a8a0a8a0a8a0a8a0a8a0a8a0a8a0a8a0a8a0a8a0a8a0a8a0a8a0a8a0a805a800a7e1a7c1a7a1a781a704a684a604a584a504a408a384a2a7a262a1e4a126a120a0e2a0e0a0e0a0c1a025a0019fe19fe09fe09fe09fe09fe09fc19fc09fc09fc09fa19fa09f059f009ec29ea19e629e229da49d439ca59c059b659ac599c899c09925986697c596c896c096c0964496219620962096209620962095a495a095a095a095a095a09543952194e294a294a094a094a0948194809404940093a393a0936293419321930193009300930092e19207920091e191e091c191a1918191809123912090e290e090e090c190a190a090a090a090629060904190409021902090018fa38fa08fa08f818f618f608f608f608f418f408f408f218f018f008f008f008ee18ec18ea18dc78d828d618d418d408d028d008d008ca38ca08c818c808c808c238c018be18bc18b258b018ae18ac18aa18a818a808a23886e884188408821880187c287c087c087a187818780878087618760872286c386c086c086c086c086a186818680860485848523846683e4838382e5826481e481c181448121808580807fe57fc17fa17f057ee17e267e207e207e207e207e207e207da47d247d207d017c847c617c607be47b457aa57a8179e579c179c0792579017846784077c477a177a077a077a07724770176c276c076c076c076a176a076817680768076807680768076617660766076607660766075e475e075c175a17581758074e5746473e4736473607303728472807280728072807280726172607260726072607260726072607260726072607260726072607260722271e271e071e071e071e071e071e071e071e071e071c1718271807142712171207120712071207120712071207120712071207120712071207120712070286fc36e0e6de16da26d816c886a7169496867672a6628662065096465628f6242610a60e15fe85d935ca75bc75b065a2759095808570856465567542a532853205266516850a64e724d0b4c084bc24b25494f4848472946e245c9448a43e542e842a241a840893db73d433bcc3aa93a4338eb380736e9362634cb33a9320d31082fab2e0d2cca2be72ae82a072927280927e126aa2643250a242722cb22a121a82162208720421eeb1e261d281c091b271a4719861888178815ed13b2126a10130e8c0d690ad508540650037701ec002e0001 0x50693050405850204c5000285040405020405000404fe0284fc3644fa3584f83344f63283980104fcf444faf444f8f444f6f444f23644ec3584e03344d23284f40584f004c4e60284da01c4f40644ee04c4e40284d801c4f355c49031547e3143a00084f00644ee0584e20284d601c4ed55c4eaf454e8f4448e31547c314c6603546602939e0084e60644e40584e204c4d401c4e155c4de62048c31547a314c6403546402939c0084dc62048a3144da0644d80584d604c4d40284d355c4d03154ce314c6203546202939a008476c3836292c4cc0124ca04cc5c04045c0344c802841001c4c634040e01c41801e4c60404c43644c23584c034c4be33438e0104c4c3840a0104c2c384c0c384580284bec384080104b83644b03584a234c4963344b63584aa34c4943344ba0584b404c4a80404bc03449e0284ba0644b204c4a60403c603449c0284b955c4b6c384863144140123960084b40644b20584a40403c403449a0284b155c4aef454acf444aac384843144560294060113940084a80644a60584a404c3c20344980284a355c4a0c3848231445402940401139200849e06449c05849a04c4980403c003449755c494c3849262048031445202941201240201139000849036448e35848c33448a32848802848635848434c48234048032847e35847c34c47a328478028476f4435e92c47755c35c92c47434847555c44e620386314472008472040c7203439801247204047003444a04045e33146e34c46801e46f55c46cc3846a33345031544c3144000133f800f46804c44834044634044433446604c46402846201c460c3845c93445a33445e04c45c93c44203445ac3c44003445804045604c45404045202845004c43e34044e03c44c04043c33444894044a04044493444955c446c38c4492c44462044203543e00943c00844293444003443e94043c63443a62041031c43804c43603441801043403c43204043002838e01242c02842e34042801cc2c64242c636c0c34240c33642a32a428034424334422028420334426028c2604242603641a01e42555cc20c3842293742092cc1e63741e62bc1633741632b41c31f388314bfe0373fe02b38400936000841a03441801041602841405841202841033c40e01040c02840a05840801c40604c40404040202840004c3fe0283f03643e23583b63343fc0103ee6643e0658bd064c3b46403ea6583dc64c3b26403e83643da3583fa34c3aa3343f804c3f60103d8358bbe34c3be3403a83343d434cbbc3403a63343d234cbb83403b83343a23283f40103f355cbeef443eec3837c3143f355cbecf443ecc3837a3143f0f443ef55c3ed2503eac383783143e8c383e7250be0f443e0c383d831d3763143e755cbdef443dec383d631d3743143e52503e2f443e155c3def443dcc383d431d3723143dac383d955c3d6f44bd4c383d492c3d23143820083d0f443ccc383be31d3703143d155c3cac383bc31d36e3143ce0423cd55c3cac383ba31d36c3143c893c3c60583c404c3c20403c00283bf55c3bcc383ba92c3b8314380008bb4f443b4c383ae92c3a831d36a3143b6f443b555c3b2c383ac92c3a631d3683143b0c383af55cbacc383ac92c3a431d3663143aac383a955cba6c383a692c3a46203a231437e0083a035839e34c39c32839a31c39800839635839434c39234039032838e00838c02938a02838802838603c38403438234cb8034038033437e32838231c38031c37e31c37c664376658b7064c37064036a63437865837264cb6e64036863437d55c37b250b78c3837892c37755c374f44b72c3837292c37155c36ec3836c92c36b55cb68c3836892c36662036403c362f4435e92c36355c35c92c360028b5ef4435ec3835f55c35cc3835a02835725031e64d2c06202a834d33a349a8a34128a33511431434a6493463493580123578682d86212be620a8834128833523231f1da31b18431511231435401f35201e35001334e01234c00e34833c34b25034864c34403c34725034434ca8434028433434206434005833e02833c01c33b8682d66212bc620a8234128233518231433806533605933405833204d33004c32e02932c02832a01e32801d32601c324008322f44b209432d292d2b892caae64322e62b1d862717e62110e62032355c2d092d2b692c22c62b1d662717c62110c62032125031ef4e314f4430464e2ce6202283412f233d2723351fc31d10a314321868312f442cc6202263412f033d2703351fa31d10831431f86831cf442ca31422404131a03da6e03526e0291f801110600830264e2fe33d1f631d31804e316012315868312f44306643300642a8034326c33520231f1f431d17a31510431431004330e04230c01330a01230800eb07250306c38305868b02f45b00f4430292d30092c1f2041a660359f202926601d1020082fc0302fef442fc3402623341ec31c2fa0642f80582f604c2f40282f38682f0f442c86202603351fe31e1ea31d1783142ee0652ec0592ea0582e804d2e604c2e40422e20412e00401980352de0292dc0282da008ad32502d2f44ace94e2ce9421e86290fe6202c631a2d92502ca64c25e34d2d6349a583412583352d40482d38682d0f44acc9421e66290fc6202c431a2cf8682ccf442cac421e43352c83312563290fa3142c7868ac4f442c4c381e231d0de314ac20422c20361e201d146008ab8f442c0c432b8c38a526432526371726210f66202b431b2c18682bef4424e3412bc33da483352483290f43142ba03d2b955c2b6c38a506371706210f26202b231b2b5868ab2f442b2c3816e620ab00422b003611c0082af2502a8f4e2a4f4929cf4428ac4e22864127263525262024034e16a3142af86829af442266412706352506201683142ac03e2aa03c2a98682a6f4422434125e31524e3141660082a58682a2f4427a34127833d26a32925c31524c3141640082a2f4827663d23e34e2a004e29e04c12603429d86829af44286c4227c64326863525a62124a62024434323c3421e031f1d431b29804329604229404129204029003528e01f28c01e28b868288f4428692c26e34125831524831428403e28203d24203523a034162008281250224c4c27ec4827cc3826e94c9f2334266328a3804027ac48274330278f48276f4427464026463419a334273868270f4426ec4226cc3826a93d19a93126892c2663422643262563142380422620322600311dc01116000825ef4e25cf4925af44258c4e1e464025663423634e25403c253868250f4424ec4224cc3d24ac3824894223434215e314246031244c38242940241868a3cf4423e92d23c92c23a634a3803523801d236009234008a2f25022ef44a2894e22894221492c9fc64e1fc6421e86201d231915a31423325022464c2306482126201f834c22f86822cf44a2694221092c9fa6421e66201d031915831422af4421e620229868226f44224c42222c3d220c389f23421e4314156008a1e94e21e9429f064e1f064221c04e21a03521803421601d11a01c215868a10f44212c43210c38a006439ee6422006371ee63616c6209de3431de3371ce31915c3150f8314a0e043a0c04220e03720c03620a02920802820601f14601e20401d202f442006201fe03c1fd8681faf441f8c421f6c391f4c381f23421f03151ee3141ec0321ea0311dc0291540081e98689e6f441e6c389e46421e463616c6201523141e201a1e200e1e0f441de6201dc3349d92501d8f441d26291446201cc3641c23589b234e9a634c1b23421a63401943341db2501c80641ba0581ae04c9aa0401aa0341920281d98681d6f441d06291426201c63581b834c9b03429a43401903341d4f441c40641b605899c04c19a0341880281d38689d0f441d0c381ce6201503141b404c9a80429960401a80361960341860281cd55c1cb2509c6c381c89371c692c9c40371c402b14e0091400081c355c1c0f451bef449bcc439b8c381bc9431ba9371b892c9b60371b602b1b401114c00913e0081b38681b0f441aec421acc381aa94219a0291a801113c0081a755c1a4c381a29371a092d19e92c19c03719a02b19802719601114a00913a00819555c990c3819293719092c98e63718e62b18c62118a62098803718802b18601114800913800897f25017ef4417292c96a64e16a64215a62a14462693234e13234212232a18525016634c18234896234016233412e04c18004817f86817cf4417092c96864215862a14262693034212032a17af4415634017833c16033415431c11e04017603c15262892c34e12c34211c3280de01815c00e17400c173868970f44170c3895e64215e63692a34212a33616e01916c00d12603416b868168f44166c42164c3d16294215633516032915e31492804213402915c92c15031811a01c15b868958f44158c389566421566360f862095434215433615231412401115062814e36414c35894a34c14a340148334146010145868942f44142c3814035813e34c93c34293a34013c33613a334138328136011134334133868130f4412ec4211e33512c31512a31412804212602912431c118018123868920f44120c3891e64211e63611c31411a01111832811601c90ef44114c4310ec3890a64310a6370fe6210f66208ee3430ee3370e431f0da31b115868112f441063410f43140ea04111003d10f55c10cc389086370fc6210f26208ec3370e231f0d831b10b868108f44106c42104c381023420fa3140e00351000310d600d0ff8688fcf440fcc388fa6420fa6360dc31d0f800e0f755c8f2c380f49370f292c8e83370e832b0f000f0ef8680ecf440eac420e03350e83140e60420e58688e2f440e2c388e06420e06360de6200dc3140d400d0db8688d8f440d8c388d66420d66360d431d8d20420d20368c0f440d0c430c0c388bc6430bc6370a662109c62089434309433707431f05e31b04a3150283140d18680cef450ccf440ca3430b63410c833f0a431509a3140c604308e0410c403f0c203d88603508602907201305c00f0480090260080c155c0bec388ba6370a262109862089233707031f05a31b0463150243140bd8680baf440b8c430b6c420b4c390b2c380b03430ae3420a03148840430ac03706c0350aa0330a803107e0290660130640110440090220080a78688a2f440a4c430a2c388a06420a063687c34307c33706231d04231502031409e00e09d55c898c3809a93709892c87a33707a32b04031501e31409600f095868092f44090c4308ec4208cc3d08ac39088c3808694208434308233706c33508033307e32907c31507a31407804307604206001305800f03e00903c008075868870f44072c43070c3886e64386c64206e63706c63606a62106862086634386434206633706433606231486004306003705600d03a00903800805f86885af4405cc4305ac3885834305833705631d03631503431405405805204c85004284e04005003604e03404c02804b868846f44048c43046c3884464304463704262104062083e34383c34203e33703c33603a31f03831e03631b03431a83204383004203203703003602e01f02c01e02a01b02955c824c3802693702492c82233702232b02031501e31481c03701c02b01a01301800f01755c812c3801493701292c81033701032b00e31500c31480a03700a02b00801300600f0040090020080000ff 16 5 13 10 1 7
def s107Data : Forest := fun i => decodeNode 10 23 0x4984560407d4080f70101d6014366f44689e88d0bd11a07a233e064672ab8cd81919a02c33555c665e8accbd1199032330058660098cc55719731032e6206580c8ca81619502632a028656ab8ca0c559418a32801263c098c700a18e020304c385f9870beb0e17c61c2f60345e00c8bbd5717661c2ec0645d40b0bad571747a2ae8f445d1870ba01917202c2e404c5caab8b8b0e1710322e00585c0098b8010170aae2dec385bcc40b78d916c1ac2d83345b0650b600a16b1ac2ca34c594680b28ca1651ac2be34c57c650af80a15eaae2b955c558080a900d152aae294c38528666a5013148026284028508038a130e14002627893c4e18789b0101320262620404c40509881312e01e2520404980809055711e61c23c6204792688e80d11d4a023863446cc408c81311601a22c03c4500808880a1111a021e6364346548680d10c01b20d55c41526e82a4b105315a0a31f41406882004102014202058400050800cf0fd0081f80283e40b07b8070f70261ec0403d80507b0130f10141e00103b8698758130eb0081d60103a2ab8733d10e5aae1c92503918707230e0e3aae1c125037de886f5570dd7a21bac383758706e5570db7a21b692c36c6286dd570d30211a355c3418706824f0cf02c19a04c3340806680a0cdaae198c38331258660c50cc7a219555c32587064b0e0c8aae18c92c31987062d570c4496188620310628620d60c21a6184328308638610020c11ac17a34c2f46805e8ca0bd0041780292ec0505d80a0b701e16a0342bc638538c70a618e14b55c2864a050a4b0a1aae140f442812585055709e61c13c92c27aab84ea4b09d31013a03c25eab84380a07daae0f4c381e80503c804868c340ce01f19c03c33804c670090ce00e19e4a0329930659280c634c18c0c8318160630140c601c18f0d03101946202c8c405818809a310130620148c402818803c3100746200e0c400818aab83061a05ec340b8f4417007a2e01385b0090b7868169e882d010c5a0210b40131680242d00385a61c0b386816125a2c24b0587a20ac3401580c82b0160560260ac02815b0d02abd10550328aa0591540b02a8134550260aa0421540822a8100550148aa0281540102ac940531a48a604814f0d0293d1052c340a2f44145884288cc451c340a0c3814006c2861a04e7a209c33d13807a2755704d61c09b8681318702600d84cc3409403e1280782561a0487a209186811de902301384602608d868115e8822810c4502108a0411140802280d44500f88a01e1170d0223d104449608803e11007a22494043624086c3810d890213d20417a20826401070d0203d1040621080c3810127a2024b0401a10803261000642000c4407a707ef490fde881fb1383f31a07e03c0ff0d01f3d103e62107cc3d0f98701f25083e01887cc380f52801ee1a03c49687892c0f0c681e00743c0048780080f24a01d19203ac34072f440e5e881c61a0377a206ec420dd87a1bb0e0374a106c04e0d806a1b00d03600e86d8680d58861ab0e03501b86a0360d40521a80a03500f86a01d0d5e881a18803401e0698680cde8819b1083361c866c380cc684198c543318a0660320cc06219e1a03261c0646360c801c193d10313100623340c64a017e1a02e7a205cf440b70d01630e02c31005955c0ae4a015a4dc2b49605602b0aeab8153d142a7a20549430a926e1524b02a0158540110ab0d014bd1029621052c380a528414804429aae050c380a126e1424b4284960500370a005614009c2800885155c09d26e13a4b02731584e62109cc401380ac2700884f25009469012812025c34048f44091e88118cf02301e04600c08b0d010b0e02100c84200d0870d00fbd101f62103ec3d07d2840f8ca41f18a03e92c07b0d00eb0e01d31b03a3360746280e98a01c1b20383580706800e0cd01c00803986806d8700d8d601b1a603633606c6680d8ca01b00883633406b0d00cbd10196210323150646280c81081901483231c0630d00bb0e01731b02e31405c0220b8ca01600e02d868051e880a00f414aae026c3804f0d0093d1012621024c380486840900c412c34022c38044c6c08803811aae02093704125808003c10c3401ef4403d884078c500f02101f8680398700718d80e31001c31403b0d006b0e00d31b01a31d03406c06e1a00b7a2816f4402c686058cfc0b02181603f02c07a05d5700a61c015868025e8804b10c09621012c39025870048d0c091a10120370240660480c409c34010c430218700418d80800701155c01d26e03a4b00700780f868019e8803310c0662100cc3d0198720330e0064a100c34301866e030ccc0619480c31501862803010c0602100d86801588602b0e00531b80a636014c420298800519b80a3360146280280dc05c34008c43011870020cdc0418e8080580100980200d80401a0080280130d001b10c0361c00663700cc420198800319b80633600c63e018c780318d80631a00c06e0180d80300f80601e00c03601d5700249b80492c008656010c540218a00402b00802601003c02aae002937005258008cac0118a80231400405600804c010078020090040100083fc00 i
def s107Tags := dagTraceTags s107Mask 45 (dagTagBases s107StockWords 0x82000008840844e21c80fee3af756f3ca9641d11a80066d244fceaaa029af15990c38fe63dfa8b8b884e802bab 0x33003008040063b21c8acef32f73fda8a9443910680004da147caa2a069a21c800438a2631ba88820846002bab 45) 12 s107Data
def s107States := dagTrace s107Mask s107StockWords 12 s107Data
def s107Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s107MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s107Move0Map, s107Move0Map)]
def s107Moves := dagMoves s107MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Autos : DagMovesOK s107Mask s107Goal 256 s107Moves := dagMovesOfCheck (by decide +kernel)
def s107Check := dagCheckNode s107Mask s107Goal s107Chart (dagKnownCloses s107Goal s107Cuts) 644 s107States s107Moves s107Links s107Sample s107Tags
def s107RootAt (token : Nat) : Bool :=
  let s := rootState s107StockWords 12 token
  !dagAllowedRoot s107Witnesses s.2.1 || dagLocal s107Mask s107Goal s107Chart (dagKnownCloses s107Goal s107Cuts) s ||
  dagRef 644 s107States s107Moves s107Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107RootBlock0 : treeBlock 0 64 s107RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107RootBlock64 : treeBlock 64 64 s107RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107RootBlock128 : treeBlock 128 64 s107RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107RootBlock192 : treeBlock 192 64 s107RootAt = true := by decide +kernel
theorem s107RootVerified : treeBlock 0 256 s107RootAt = true := (@treeBlock_merge 0 128 128 s107RootAt (@treeBlock_merge 0 64 64 s107RootAt s107RootBlock0 s107RootBlock64) (@treeBlock_merge 128 64 64 s107RootAt s107RootBlock128 s107RootBlock192))
theorem s107Roots : dagCheckRoots s107Mask s107Goal s107Chart (dagKnownCloses s107Goal s107Cuts) s107Witnesses (dagRef 644 s107States s107Moves s107Links 0) s107StockWords 12 = true := s107RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block0 : treeBlock 0 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block16 : treeBlock 16 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block32 : treeBlock 32 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block48 : treeBlock 48 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block64 : treeBlock 64 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block80 : treeBlock 80 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block96 : treeBlock 96 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block112 : treeBlock 112 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block128 : treeBlock 128 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block144 : treeBlock 144 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block160 : treeBlock 160 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block176 : treeBlock 176 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block192 : treeBlock 192 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block208 : treeBlock 208 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block224 : treeBlock 224 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block240 : treeBlock 240 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block256 : treeBlock 256 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block272 : treeBlock 272 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block288 : treeBlock 288 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block304 : treeBlock 304 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block320 : treeBlock 320 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block336 : treeBlock 336 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block352 : treeBlock 352 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block368 : treeBlock 368 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block384 : treeBlock 384 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block400 : treeBlock 400 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block416 : treeBlock 416 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block432 : treeBlock 432 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block448 : treeBlock 448 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block464 : treeBlock 464 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block480 : treeBlock 480 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block496 : treeBlock 496 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block512 : treeBlock 512 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block528 : treeBlock 528 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block544 : treeBlock 544 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block560 : treeBlock 560 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block576 : treeBlock 576 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block592 : treeBlock 592 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block608 : treeBlock 608 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block624 : treeBlock 624 16 s107Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block640 : treeBlock 640 4 s107Check = true := by decide +kernel
theorem s107Verified : treeBlock 0 644 s107Check = true := (@treeBlock_merge 0 336 308 s107Check (@treeBlock_merge 0 176 160 s107Check (@treeBlock_merge 0 96 80 s107Check (@treeBlock_merge 0 48 48 s107Check (@treeBlock_merge 0 32 16 s107Check (@treeBlock_merge 0 16 16 s107Check s107Block0 s107Block16) s107Block32) (@treeBlock_merge 48 32 16 s107Check (@treeBlock_merge 48 16 16 s107Check s107Block48 s107Block64) s107Block80)) (@treeBlock_merge 96 48 32 s107Check (@treeBlock_merge 96 32 16 s107Check (@treeBlock_merge 96 16 16 s107Check s107Block96 s107Block112) s107Block128) (@treeBlock_merge 144 16 16 s107Check s107Block144 s107Block160))) (@treeBlock_merge 176 80 80 s107Check (@treeBlock_merge 176 48 32 s107Check (@treeBlock_merge 176 32 16 s107Check (@treeBlock_merge 176 16 16 s107Check s107Block176 s107Block192) s107Block208) (@treeBlock_merge 224 16 16 s107Check s107Block224 s107Block240)) (@treeBlock_merge 256 48 32 s107Check (@treeBlock_merge 256 32 16 s107Check (@treeBlock_merge 256 16 16 s107Check s107Block256 s107Block272) s107Block288) (@treeBlock_merge 304 16 16 s107Check s107Block304 s107Block320)))) (@treeBlock_merge 336 160 148 s107Check (@treeBlock_merge 336 80 80 s107Check (@treeBlock_merge 336 48 32 s107Check (@treeBlock_merge 336 32 16 s107Check (@treeBlock_merge 336 16 16 s107Check s107Block336 s107Block352) s107Block368) (@treeBlock_merge 384 16 16 s107Check s107Block384 s107Block400)) (@treeBlock_merge 416 48 32 s107Check (@treeBlock_merge 416 32 16 s107Check (@treeBlock_merge 416 16 16 s107Check s107Block416 s107Block432) s107Block448) (@treeBlock_merge 464 16 16 s107Check s107Block464 s107Block480))) (@treeBlock_merge 496 80 68 s107Check (@treeBlock_merge 496 48 32 s107Check (@treeBlock_merge 496 32 16 s107Check (@treeBlock_merge 496 16 16 s107Check s107Block496 s107Block512) s107Block528) (@treeBlock_merge 544 16 16 s107Check s107Block544 s107Block560)) (@treeBlock_merge 576 48 20 s107Check (@treeBlock_merge 576 32 16 s107Check (@treeBlock_merge 576 16 16 s107Check s107Block576 s107Block592) s107Block608) (@treeBlock_merge 624 16 4 s107Check s107Block624 s107Block640)))))
theorem s107Blocks : treeBlock 0 644 s107Check = true := s107Verified
theorem s107Known : Known s107Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s18Stock) s67Stock) s65Stock) s66Stock) s64Stock) s43Stock) s42Stock) s105Stock) s106Stock) s100Stock) s102Stock) s104Stock) s103Stock) s101Stock) s99Stock) s93Stock) s94Stock) s96Stock) s97Stock) s95Stock) s89Stock) s92Stock) s63Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Stock : Lower s107Mask s107StockWords s107Goal 13 := by
  apply lowerDag _ _ _ _ s107Autos _ _ _ s107Known _ s107Roots s107Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s107StockWords; decide +kernel
  · decide +kernel
  · simp only [s107Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

end PEqualNP.Outside.L_meta_8515

open PEqualNP.Outside.L_meta_8515 in
theorem PEqualNP.Outside.L_meta_8515 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 7) || (x 6 && x 7)) t → 13 ≤ t := by
  intro t h
  let raw : List (BitVec 256) := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
  let goal : BitVec 256 := 0xffffffffffffffffffffffffffeaeae8ffeeeeeeffeeeeecffeaeaeaffeaeae8
  have root : Lower (fullMask 256) (raw.map BitVec.toNat) goal.toNat 13 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) s107Stock
  exact hcsLower (n := 8) raw goal 13 _ (by decide +kernel) (by decide +kernel) root t h
