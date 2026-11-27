import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10578

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

def base : List Word := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000]
def goal : Word := 0xfffffffefffffefefffefffefefeeca0

def s234M : Word := 0x330033
abbrev s234G := goal &&& s234M
abbrev s234W : List Word := projectDAGStock s234M base [0, 2, 4]
def s234Fact : Bound := (s234M, s234W, 4, s234G)
def s234Witness := unpackWitnesses s234W [2564, 264705, 532993]
def s234Cuts : List Bound := []
def s234Chart : Option RowChart := some ⟨[5, 17, 20, 5, 17, 20, 5, 17, 20, 5, 17, 20, 1, 4, 16, 1, 4, 16, 1, 4, 16, 1, 4, 16], rfl⟩
def s234Sample : DagSample := (0x214020442005080500814080440211020140205, 9)
def s234Forest : Forest := fun i => decodeNode 1 4 0xe i
def s234Links : DagLinks := dagLookupLinks 0x9 0x7 2 1 3 1 1 2
def s234States := dagTrace s234M s234W 3 s234Forest
def s234Tags := dagTraceTags s234M 9 (dagTagBases s234W 0x6f2e6cf 0x1a12505 9) 3 s234Forest
def s234Moves := dagMoves ([] : List (DagMoveRecord 128))
def s234Check := dagCheckNode s234M s234G s234Chart (dagKnownCloses s234G s234Cuts) 1 s234States s234Moves s234Links s234Sample s234Tags
def s234RootAt (token : Nat) : Bool :=
  let st := rootState s234W 3 token
  !dagAllowedRoot s234Witness st.2.1 || dagLocal s234M s234G s234Chart (dagKnownCloses s234G s234Cuts) st || dagRef 1 s234States s234Moves s234Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s234Roots : dagCheckRoots s234M s234G s234Chart (dagKnownCloses s234G s234Cuts) s234Witness (dagRef 1 s234States s234Moves s234Links 0) s234W 3 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s234Blocks : treeBlock 0 1 s234Check = true := (by decide +kernel)
theorem s234Known : Known s234Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s234Lower : Lower s234M s234W s234G 4 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s234Known _ s234Roots s234Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s234W; decide +kernel
  · decide +kernel
  · simp only [s234Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro _ h; exact h.elim

def s236M : Word := 0x33003300
abbrev s236G := goal &&& s236M
abbrev s236W : List Word := projectDAGStock s236M base [0, 2, 4]
def s236Fact : Bound := (s236M, s236W, 4, s236G)
def s236Witness := unpackWitnesses s236W [6668, 268809, 537097]
def s236Cuts : List Bound := []
def s236Chart : Option RowChart := some ⟨[13, 25, 28, 13, 25, 28, 13, 25, 28, 13, 25, 28, 9, 12, 24, 9, 12, 24, 9, 12, 24, 9, 12, 24], rfl⟩
def s236Sample : DagSample := (0x121c06064300d0c070181c0c064121906034120d, 9)
def s236Forest : Forest := fun i => decodeNode 1 4 0xe i
def s236Links : DagLinks := dagLookupLinks 0x9 0x7 2 1 3 1 1 2
def s236States := dagTrace s236M s236W 3 s236Forest
def s236Tags := dagTraceTags s236M 9 (dagTagBases s236W 0x6f2e6cf 0x1a12505 9) 3 s236Forest
def s236Moves := dagMoves ([] : List (DagMoveRecord 128))
def s236Check := dagCheckNode s236M s236G s236Chart (dagKnownCloses s236G s236Cuts) 1 s236States s236Moves s236Links s236Sample s236Tags
def s236RootAt (token : Nat) : Bool :=
  let st := rootState s236W 3 token
  !dagAllowedRoot s236Witness st.2.1 || dagLocal s236M s236G s236Chart (dagKnownCloses s236G s236Cuts) st || dagRef 1 s236States s236Moves s236Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s236Roots : dagCheckRoots s236M s236G s236Chart (dagKnownCloses s236G s236Cuts) s236Witness (dagRef 1 s236States s236Moves s236Links 0) s236W 3 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s236Blocks : treeBlock 0 1 s236Check = true := (by decide +kernel)
theorem s236Known : Known s236Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s236Lower : Lower s236M s236W s236G 4 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s236Known _ s236Roots s236Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s236W; decide +kernel
  · decide +kernel
  · simp only [s236Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro _ h; exact h.elim

def s258M : Word := 0x3300000033
abbrev s258G := goal &&& s258M
abbrev s258W : List Word := projectDAGStock s258M base [0, 2, 5]
def s258Fact : Bound := (s258M, s258W, 4, s258G)
def s258Witness := unpackWitnesses s258W [2564, 264705, 541185]
def s258Cuts : List Bound := []
def s258Chart : Option RowChart := some ⟨[5, 33, 36, 5, 33, 36, 5, 33, 36, 5, 33, 36, 1, 4, 32, 1, 4, 32, 1, 4, 32, 1, 4, 32], rfl⟩
def s258Sample : DagSample := (0x224020844005100900824100840221020140205, 9)
def s258Forest : Forest := fun i => decodeNode 1 4 0xe i
def s258Links : DagLinks := dagLookupLinks 0x9 0x7 2 1 3 1 1 2
def s258States := dagTrace s258M s258W 3 s258Forest
def s258Tags := dagTraceTags s258M 9 (dagTagBases s258W 0x6f2e6cf 0x1a12505 9) 3 s258Forest
def s258Moves := dagMoves ([] : List (DagMoveRecord 128))
def s258Check := dagCheckNode s258M s258G s258Chart (dagKnownCloses s258G s258Cuts) 1 s258States s258Moves s258Links s258Sample s258Tags
def s258RootAt (token : Nat) : Bool :=
  let st := rootState s258W 3 token
  !dagAllowedRoot s258Witness st.2.1 || dagLocal s258M s258G s258Chart (dagKnownCloses s258G s258Cuts) st || dagRef 1 s258States s258Moves s258Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s258Roots : dagCheckRoots s258M s258G s258Chart (dagKnownCloses s258G s258Cuts) s258Witness (dagRef 1 s258States s258Moves s258Links 0) s258W 3 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s258Blocks : treeBlock 0 1 s258Check = true := (by decide +kernel)
theorem s258Known : Known s258Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s258Lower : Lower s258M s258W s258G 4 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s258Known _ s258Roots s258Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s258W; decide +kernel
  · decide +kernel
  · simp only [s258Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro _ h; exact h.elim

def s271M : Word := 0x50500000505
abbrev s271G := goal &&& s271M
abbrev s271W : List Word := projectDAGStock s271M base [1, 3, 5]
def s271Fact : Bound := (s271M, s271W, 4, s271G)
def s271Witness := unpackWitnesses s271W [5128, 267266, 541698]
def s271Cuts : List Bound := []
def s271Chart : Option RowChart := some ⟨[10, 34, 40, 10, 34, 40, 10, 34, 40, 10, 34, 40, 2, 8, 32, 2, 8, 32, 2, 8, 32, 2, 8, 32], rfl⟩
def s271Sample : DagSample := (0x42804088400a100a0102810088042204028040a, 9)
def s271Forest : Forest := fun i => decodeNode 1 4 0xe i
def s271Links : DagLinks := dagLookupLinks 0x9 0x7 2 1 3 1 1 2
def s271States := dagTrace s271M s271W 3 s271Forest
def s271Tags := dagTraceTags s271M 9 (dagTagBases s271W 0x6f2e6cf 0x1a12505 9) 3 s271Forest
def s271Moves := dagMoves ([] : List (DagMoveRecord 128))
def s271Check := dagCheckNode s271M s271G s271Chart (dagKnownCloses s271G s271Cuts) 1 s271States s271Moves s271Links s271Sample s271Tags
def s271RootAt (token : Nat) : Bool :=
  let st := rootState s271W 3 token
  !dagAllowedRoot s271Witness st.2.1 || dagLocal s271M s271G s271Chart (dagKnownCloses s271G s271Cuts) st || dagRef 1 s271States s271Moves s271Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s271Roots : dagCheckRoots s271M s271G s271Chart (dagKnownCloses s271G s271Cuts) s271Witness (dagRef 1 s271States s271Moves s271Links 0) s271W 3 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s271Blocks : treeBlock 0 1 s271Check = true := (by decide +kernel)
theorem s271Known : Known s271Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s271Lower : Lower s271M s271W s271G 4 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s271Known _ s271Roots s271Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s271W; decide +kernel
  · decide +kernel
  · simp only [s271Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro _ h; exact h.elim

def s306M : Word := 0x330000000000000033
abbrev s306G := goal &&& s306M
abbrev s306W : List Word := projectDAGStock s306M base [0, 2, 6]
def s306Fact : Bound := (s306M, s306W, 4, s306G)
def s306Witness := unpackWitnesses s306W [2564, 264705, 557569]
def s306Cuts : List Bound := []
def s306Chart : Option RowChart := some ⟨[5, 65, 68, 5, 65, 68, 5, 65, 68, 5, 65, 68, 1, 4, 64, 1, 4, 64, 1, 4, 64, 1, 4, 64], rfl⟩
def s306Sample : DagSample := (0x244021048005201100844201040241020140205, 9)
def s306Forest : Forest := fun i => decodeNode 1 4 0xe i
def s306Links : DagLinks := dagLookupLinks 0x9 0x7 2 1 3 1 1 2
def s306States := dagTrace s306M s306W 3 s306Forest
def s306Tags := dagTraceTags s306M 9 (dagTagBases s306W 0x6f2e6cf 0x1a12505 9) 3 s306Forest
def s306Moves := dagMoves ([] : List (DagMoveRecord 128))
def s306Check := dagCheckNode s306M s306G s306Chart (dagKnownCloses s306G s306Cuts) 1 s306States s306Moves s306Links s306Sample s306Tags
def s306RootAt (token : Nat) : Bool :=
  let st := rootState s306W 3 token
  !dagAllowedRoot s306Witness st.2.1 || dagLocal s306M s306G s306Chart (dagKnownCloses s306G s306Cuts) st || dagRef 1 s306States s306Moves s306Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s306Roots : dagCheckRoots s306M s306G s306Chart (dagKnownCloses s306G s306Cuts) s306Witness (dagRef 1 s306States s306Moves s306Links 0) s306W 3 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s306Blocks : treeBlock 0 1 s306Check = true := (by decide +kernel)
theorem s306Known : Known s306Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s306Lower : Lower s306M s306W s306G 4 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s306Known _ s306Roots s306Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s306W; decide +kernel
  · decide +kernel
  · simp only [s306Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro _ h; exact h.elim

def s308M : Word := 0x33000000000000003300
abbrev s308G := goal &&& s308M
abbrev s308W : List Word := projectDAGStock s308M base [0, 2, 6]
def s308Fact : Bound := (s308M, s308W, 4, s308G)
def s308Witness := unpackWitnesses s308W [6668, 268809, 561673]
def s308Cuts : List Bound := []
def s308Chart : Option RowChart := some ⟨[13, 73, 76, 13, 73, 76, 13, 73, 76, 13, 73, 76, 9, 12, 72, 9, 12, 72, 9, 12, 72, 9, 12, 72], rfl⟩
def s308Sample : DagSample := (0x124c06124900d24130184c24124124906034120d, 9)
def s308Forest : Forest := fun i => decodeNode 1 4 0xe i
def s308Links : DagLinks := dagLookupLinks 0x9 0x7 2 1 3 1 1 2
def s308States := dagTrace s308M s308W 3 s308Forest
def s308Tags := dagTraceTags s308M 9 (dagTagBases s308W 0x6f2e6cf 0x1a12505 9) 3 s308Forest
def s308Moves := dagMoves ([] : List (DagMoveRecord 128))
def s308Check := dagCheckNode s308M s308G s308Chart (dagKnownCloses s308G s308Cuts) 1 s308States s308Moves s308Links s308Sample s308Tags
def s308RootAt (token : Nat) : Bool :=
  let st := rootState s308W 3 token
  !dagAllowedRoot s308Witness st.2.1 || dagLocal s308M s308G s308Chart (dagKnownCloses s308G s308Cuts) st || dagRef 1 s308States s308Moves s308Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s308Roots : dagCheckRoots s308M s308G s308Chart (dagKnownCloses s308G s308Cuts) s308Witness (dagRef 1 s308States s308Moves s308Links 0) s308W 3 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s308Blocks : treeBlock 0 1 s308Check = true := (by decide +kernel)
theorem s308Known : Known s308Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s308Lower : Lower s308M s308W s308G 4 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s308Known _ s308Roots s308Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s308W; decide +kernel
  · decide +kernel
  · simp only [s308Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro _ h; exact h.elim

def s326M : Word := 0x300030000000000030003
abbrev s326G := goal &&& s326M
abbrev s326W : List Word := projectDAGStock s326M base [0, 4, 6]
def s326Fact : Bound := (s326M, s326W, 4, s326G)
def s326Witness := unpackWitnesses s326W [8720, 270849, 557569]
def s326Cuts : List Bound := []
def s326Chart : Option RowChart := some ⟨[17, 65, 80, 17, 65, 80, 17, 65, 80, 17, 65, 80, 1, 16, 64, 1, 16, 64, 1, 16, 64, 1, 16, 64], rfl⟩
def s326Sample : DagSample := (0x250081048011201402050201040241080440211, 9)
def s326Forest : Forest := fun i => decodeNode 1 4 0xe i
def s326Links : DagLinks := dagLookupLinks 0x9 0x7 2 1 3 1 1 2
def s326States := dagTrace s326M s326W 3 s326Forest
def s326Tags := dagTraceTags s326M 9 (dagTagBases s326W 0x6f2e6cf 0x1a12505 9) 3 s326Forest
def s326Moves := dagMoves ([] : List (DagMoveRecord 128))
def s326Check := dagCheckNode s326M s326G s326Chart (dagKnownCloses s326G s326Cuts) 1 s326States s326Moves s326Links s326Sample s326Tags
def s326RootAt (token : Nat) : Bool :=
  let st := rootState s326W 3 token
  !dagAllowedRoot s326Witness st.2.1 || dagLocal s326M s326G s326Chart (dagKnownCloses s326G s326Cuts) st || dagRef 1 s326States s326Moves s326Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s326Roots : dagCheckRoots s326M s326G s326Chart (dagKnownCloses s326G s326Cuts) s326Witness (dagRef 1 s326States s326Moves s326Links 0) s326W 3 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s326Blocks : treeBlock 0 1 s326Check = true := (by decide +kernel)
theorem s326Known : Known s326Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s326Lower : Lower s326M s326W s326G 4 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s326Known _ s326Roots s326Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s326W; decide +kernel
  · decide +kernel
  · simp only [s326Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro _ h; exact h.elim

def s329M : Word := 0x30003000000000003000300
abbrev s329G := goal &&& s329M
abbrev s329W : List Word := projectDAGStock s329M base [0, 4, 6]
def s329Fact : Bound := (s329M, s329W, 4, s329G)
def s329Witness := unpackWitnesses s329W [12824, 274953, 561673]
def s329Cuts : List Bound := []
def s329Chart : Option RowChart := some ⟨[25, 73, 88, 25, 73, 88, 25, 73, 88, 25, 73, 88, 9, 24, 72, 9, 24, 72, 9, 24, 72, 9, 24, 72], rfl⟩
def s329Sample : DagSample := (0x12580c12490192416030582412412490c0641219, 9)
def s329Forest : Forest := fun i => decodeNode 1 4 0xe i
def s329Links : DagLinks := dagLookupLinks 0x9 0x7 2 1 3 1 1 2
def s329States := dagTrace s329M s329W 3 s329Forest
def s329Tags := dagTraceTags s329M 9 (dagTagBases s329W 0x6f2e6cf 0x1a12505 9) 3 s329Forest
def s329Moves := dagMoves ([] : List (DagMoveRecord 128))
def s329Check := dagCheckNode s329M s329G s329Chart (dagKnownCloses s329G s329Cuts) 1 s329States s329Moves s329Links s329Sample s329Tags
def s329RootAt (token : Nat) : Bool :=
  let st := rootState s329W 3 token
  !dagAllowedRoot s329Witness st.2.1 || dagLocal s329M s329G s329Chart (dagKnownCloses s329G s329Cuts) st || dagRef 1 s329States s329Moves s329Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s329Roots : dagCheckRoots s329M s329G s329Chart (dagKnownCloses s329G s329Cuts) s329Witness (dagRef 1 s329States s329Moves s329Links 0) s329W 3 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s329Blocks : treeBlock 0 1 s329Check = true := (by decide +kernel)
theorem s329Known : Known s329Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s329Lower : Lower s329M s329W s329G 4 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s329Known _ s329Roots s329Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s329W; decide +kernel
  · decide +kernel
  · simp only [s329Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro _ h; exact h.elim

def s332M : Word := 0x500050000000000050005
abbrev s332G := goal &&& s332M
abbrev s332W : List Word := projectDAGStock s332M base [1, 4, 6]
def s332Fact : Bound := (s332M, s332W, 4, s332G)
def s332Witness := unpackWitnesses s332W [9232, 271362, 558082]
def s332Cuts : List Bound := []
def s332Chart : Option RowChart := some ⟨[18, 66, 80, 18, 66, 80, 18, 66, 80, 18, 66, 80, 2, 16, 64, 2, 16, 64, 2, 16, 64, 2, 16, 64], rfl⟩
def s332Sample : DagSample := (0x450081088012201402050201080442080480412, 9)
def s332Forest : Forest := fun i => decodeNode 1 4 0xe i
def s332Links : DagLinks := dagLookupLinks 0x9 0x7 2 1 3 1 1 2
def s332States := dagTrace s332M s332W 3 s332Forest
def s332Tags := dagTraceTags s332M 9 (dagTagBases s332W 0x6f2e6cf 0x1a12505 9) 3 s332Forest
def s332Moves := dagMoves ([] : List (DagMoveRecord 128))
def s332Check := dagCheckNode s332M s332G s332Chart (dagKnownCloses s332G s332Cuts) 1 s332States s332Moves s332Links s332Sample s332Tags
def s332RootAt (token : Nat) : Bool :=
  let st := rootState s332W 3 token
  !dagAllowedRoot s332Witness st.2.1 || dagLocal s332M s332G s332Chart (dagKnownCloses s332G s332Cuts) st || dagRef 1 s332States s332Moves s332Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s332Roots : dagCheckRoots s332M s332G s332Chart (dagKnownCloses s332G s332Cuts) s332Witness (dagRef 1 s332States s332Moves s332Links 0) s332W 3 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s332Blocks : treeBlock 0 1 s332Check = true := (by decide +kernel)
theorem s332Known : Known s332Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s332Lower : Lower s332M s332W s332G 4 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s332Known _ s332Roots s332Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s332W; decide +kernel
  · decide +kernel
  · simp only [s332Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro _ h; exact h.elim

def s337M : Word := 0x1100110000000000110011
abbrev s337G := goal &&& s337M
abbrev s337W : List Word := projectDAGStock s337M base [2, 4, 6]
def s337Fact : Bound := (s337M, s337W, 4, s337G)
def s337Witness := unpackWitnesses s337W [10256, 272388, 559108]
def s337Cuts : List Bound := []
def s337Chart : Option RowChart := some ⟨[20, 68, 80, 20, 68, 80, 20, 68, 80, 20, 68, 80, 4, 16, 64, 4, 16, 64, 4, 16, 64, 4, 16, 64], rfl⟩
def s337Sample : DagSample := (0x850081108014201402050201100844080500814, 9)
def s337Forest : Forest := fun i => decodeNode 1 4 0xe i
def s337Links : DagLinks := dagLookupLinks 0x9 0x7 2 1 3 1 1 2
def s337States := dagTrace s337M s337W 3 s337Forest
def s337Tags := dagTraceTags s337M 9 (dagTagBases s337W 0x6f2e6cf 0x1a12505 9) 3 s337Forest
def s337Moves := dagMoves ([] : List (DagMoveRecord 128))
def s337Check := dagCheckNode s337M s337G s337Chart (dagKnownCloses s337G s337Cuts) 1 s337States s337Moves s337Links s337Sample s337Tags
def s337RootAt (token : Nat) : Bool :=
  let st := rootState s337W 3 token
  !dagAllowedRoot s337Witness st.2.1 || dagLocal s337M s337G s337Chart (dagKnownCloses s337G s337Cuts) st || dagRef 1 s337States s337Moves s337Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s337Roots : dagCheckRoots s337M s337G s337Chart (dagKnownCloses s337G s337Cuts) s337Witness (dagRef 1 s337States s337Moves s337Links 0) s337W 3 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s337Blocks : treeBlock 0 1 s337Check = true := (by decide +kernel)
theorem s337Known : Known s337Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s337Lower : Lower s337M s337W s337G 4 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s337Known _ s337Roots s337Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s337W; decide +kernel
  · decide +kernel
  · simp only [s337Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro _ h; exact h.elim

def s340M : Word := 0x110011000000000011001100
abbrev s340G := goal &&& s340M
abbrev s340W : List Word := projectDAGStock s340M base [2, 4, 6]
def s340Fact : Bound := (s340M, s340W, 4, s340G)
def s340Witness := unpackWitnesses s340W [14360, 276492, 563212]
def s340Cuts : List Bound := []
def s340Chart : Option RowChart := some ⟨[28, 76, 88, 28, 76, 88, 28, 76, 88, 28, 76, 88, 12, 24, 72, 12, 24, 72, 12, 24, 72, 12, 24, 72], rfl⟩
def s340Sample : DagSample := (0x18580c130901c24160305824130184c0c070181c, 9)
def s340Forest : Forest := fun i => decodeNode 1 4 0xe i
def s340Links : DagLinks := dagLookupLinks 0x9 0x7 2 1 3 1 1 2
def s340States := dagTrace s340M s340W 3 s340Forest
def s340Tags := dagTraceTags s340M 9 (dagTagBases s340W 0x6f2e6cf 0x1a12505 9) 3 s340Forest
def s340Moves := dagMoves ([] : List (DagMoveRecord 128))
def s340Check := dagCheckNode s340M s340G s340Chart (dagKnownCloses s340G s340Cuts) 1 s340States s340Moves s340Links s340Sample s340Tags
def s340RootAt (token : Nat) : Bool :=
  let st := rootState s340W 3 token
  !dagAllowedRoot s340Witness st.2.1 || dagLocal s340M s340G s340Chart (dagKnownCloses s340G s340Cuts) st || dagRef 1 s340States s340Moves s340Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s340Roots : dagCheckRoots s340M s340G s340Chart (dagKnownCloses s340G s340Cuts) s340Witness (dagRef 1 s340States s340Moves s340Links 0) s340W 3 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s340Blocks : treeBlock 0 1 s340Check = true := (by decide +kernel)
theorem s340Known : Known s340Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s340Lower : Lower s340M s340W s340G 4 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s340Known _ s340Roots s340Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s340W; decide +kernel
  · decide +kernel
  · simp only [s340Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro _ h; exact h.elim

def s379M : Word := 0xff00ff
abbrev s379G := goal &&& s379M
abbrev s379W : List Word := projectDAGStock s379M base [0, 1, 2, 4]
def s379Fact : Bound := (s379M, s379W, 5, s379G)
def s379Witness := unpackWitnesses s379W [2564, 271376, 526849, 795137]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s379Lower : Lower s379M s379W s379G 5 := by
  apply essentialLift (witnesses := s379Witness) (cut := s234M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s234W) (by decide +kernel)
  · exact s234Lower
  · decide +kernel

def s380M : Word := 0xff00ff00
abbrev s380G := goal &&& s380M
abbrev s380W : List Word := projectDAGStock s380M base [0, 1, 2, 4]
def s380Fact : Bound := (s380M, s380W, 5, s380G)
def s380Witness := unpackWitnesses s380W [6668, 267272, 530953, 799241]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s380Lower : Lower s380M s380W s380G 5 := by
  apply essentialLift (witnesses := s380Witness) (cut := s236M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s236W) (by decide +kernel)
  · exact s236Lower
  · decide +kernel

def s392M : Word := 0xff000000ff
abbrev s392G := goal &&& s392M
abbrev s392W : List Word := projectDAGStock s392M base [0, 1, 2, 5]
def s392Fact : Bound := (s392M, s392W, 5, s392G)
def s392Witness := unpackWitnesses s392W [2564, 279584, 526849, 803329]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s392Lower : Lower s392M s392W s392G 5 := by
  apply essentialLift (witnesses := s392Witness) (cut := s258M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s258W) (by decide +kernel)
  · exact s258Lower
  · decide +kernel

def s396M : Word := 0xf0f00000f0f
abbrev s396G := goal &&& s396M
abbrev s396W : List Word := projectDAGStock s396M base [0, 1, 3, 5]
def s396Fact : Bound := (s396M, s396W, 5, s396G)
def s396Witness := unpackWitnesses s396W [16928, 267272, 529410, 803329]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s396Lower : Lower s396M s396W s396G 5 := by
  apply essentialLift (witnesses := s396Witness) (cut := s271M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s271W) (by decide +kernel)
  · exact s271Lower
  · decide +kernel

def s400M : Word := 0x333300003333
abbrev s400G := goal &&& s400M
abbrev s400W : List Word := projectDAGStock s400M base [0, 2, 3, 5]
def s400Fact : Bound := (s400M, s400W, 5, s400G)
def s400Witness := unpackWitnesses s400W [2564, 264705, 544800, 803329]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s400Lower : Lower s400M s400W s400G 5 := by
  apply essentialLift (witnesses := s400Witness) (cut := s258M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s258W) (by decide +kernel)
  · exact s258Lower
  · decide +kernel

def s404M : Word := 0x555500005555
abbrev s404G := goal &&& s404M
abbrev s404W : List Word := projectDAGStock s404M base [1, 2, 3, 5]
def s404Fact : Bound := (s404M, s404W, 5, s404G)
def s404Witness := unpackWitnesses s404W [5128, 280608, 529410, 803842]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s404Lower : Lower s404M s404W s404G 5 := by
  apply essentialLift (witnesses := s404Witness) (cut := s271M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s271W) (by decide +kernel)
  · exact s271Lower
  · decide +kernel

def s412M : Word := 0x33003300330033
abbrev s412G := goal &&& s412M
abbrev s412W : List Word := projectDAGStock s412M base [0, 2, 4, 5]
def s412Fact : Bound := (s412M, s412W, 5, s412G)
def s412Witness := unpackWitnesses s412W [2564, 264705, 532993, 803329]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s412Lower : Lower s412M s412W s412G 5 := by
  apply essentialLift (witnesses := s412Witness) (cut := s234M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s234W) (by decide +kernel)
  · exact s234Lower
  · decide +kernel

def s414M : Word := 0x3300330033003300
abbrev s414G := goal &&& s414M
abbrev s414W : List Word := projectDAGStock s414M base [0, 2, 4, 5]
def s414Fact : Bound := (s414M, s414W, 5, s414G)
def s414Witness := unpackWitnesses s414W [6668, 268809, 537097, 806920]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s414Lower : Lower s414M s414W s414G 5 := by
  apply essentialLift (witnesses := s414Witness) (cut := s236M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s236W) (by decide +kernel)
  · exact s236Lower
  · decide +kernel

def s423M : Word := 0x505050505050505
abbrev s423G := goal &&& s423M
abbrev s423W : List Word := projectDAGStock s423M base [1, 3, 4, 5]
def s423Fact : Bound := (s423M, s423W, 5, s423G)
def s423Witness := unpackWitnesses s423W [5128, 267266, 533506, 803842]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s423Lower : Lower s423M s423W s423G 5 := by
  apply essentialLift (witnesses := s423Witness) (cut := s271M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s271W) (by decide +kernel)
  · exact s271Lower
  · decide +kernel

def s430M : Word := 0xff00000000000000ff
abbrev s430G := goal &&& s430M
abbrev s430W : List Word := projectDAGStock s430M base [0, 1, 2, 6]
def s430Fact : Bound := (s430M, s430W, 5, s430G)
def s430Witness := unpackWitnesses s430W [2564, 296000, 526849, 819713]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s430Lower : Lower s430M s430W s430G 5 := by
  apply essentialLift (witnesses := s430Witness) (cut := s306M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s306W) (by decide +kernel)
  · exact s306Lower
  · decide +kernel

def s431M : Word := 0xff00000000000000ff00
abbrev s431G := goal &&& s431M
abbrev s431W : List Word := projectDAGStock s431M base [0, 1, 2, 6]
def s431Fact : Bound := (s431M, s431W, 5, s431G)
def s431Witness := unpackWitnesses s431W [6668, 267272, 530953, 823817]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s431Lower : Lower s431M s431W s431G 5 := by
  apply essentialLift (witnesses := s431Witness) (cut := s308M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s308W) (by decide +kernel)
  · exact s308Lower
  · decide +kernel

def s443M : Word := 0xf000f00000000000f000f
abbrev s443G := goal &&& s443M
abbrev s443W : List Word := projectDAGStock s443M base [0, 1, 4, 6]
def s443Fact : Bound := (s443M, s443W, 5, s443G)
def s443Witness := unpackWitnesses s443W [8720, 271376, 532993, 819713]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s443Lower : Lower s443M s443W s443G 5 := by
  apply essentialLift (witnesses := s443Witness) (cut := s326M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s326W) (by decide +kernel)
  · exact s326Lower
  · decide +kernel

def s444M : Word := 0xf000f00000000000f000f00
abbrev s444G := goal &&& s444M
abbrev s444W : List Word := projectDAGStock s444M base [0, 1, 4, 6]
def s444Fact : Bound := (s444M, s444W, 5, s444G)
def s444Witness := unpackWitnesses s444W [12824, 267272, 537097, 823817]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s444Lower : Lower s444M s444W s444G 5 := by
  apply essentialLift (witnesses := s444Witness) (cut := s329M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s329W) (by decide +kernel)
  · exact s329Lower
  · decide +kernel

def s447M : Word := 0x3300330000000000330033
abbrev s447G := goal &&& s447M
abbrev s447W : List Word := projectDAGStock s447M base [0, 2, 4, 6]
def s447Fact : Bound := (s447M, s447W, 7, s447G)
def s447Witness := unpackWitnesses s447W [2564, 264705, 532993, 819713]
def s447Cuts : List Bound := [s234Fact, s306Fact, s326Fact, s337Fact]
def s447Chart : Option RowChart := some ⟨[5, 17, 20, 65, 68, 80, 5, 17, 20, 65, 68, 80, 1, 4, 16, 64, 1, 4, 16, 64, 1, 4, 16, 64], rfl⟩
def s447Sample : DagSample := (0x21400250081100244081040841200500214200440811200142005201402050201100844201040241080500814080440211020140205, 24)
def s447Forest : Forest := fun i => decodeNode 6 18 0x24b0162b064b1e620058a5c32b058d9832864cd9831f064b1562054c50162948ca5202b058d8d31d34ca0e0363407c133618ca86028240d8601c1c0a86013064b0262008c5020080403c0 i
def s447Links : DagLinks := dagLookupLinks 0xe0f44d0313c06c4ac6b0a8664982608ce21845d4705b16c1a159151505404c530484e4380e0380b306801 0x7a4b0b310043143865268c7498149001d3d25855880198a1931c38c5260c7890148b0113265064ca0d31b183361e03a28044b496156200462838070480813629246523407840090e0280e02038ca0831b0f31d1a06c1804848140701c120501c070599b0a32a1006c180a824960362004628824b0fb159d620366565cc7ca18a1102b1803e1404c08040000f 10 4 12 6 1 5
def s447States := dagTrace s447M s447W 6 s447Forest
def s447Tags := dagTraceTags s447M 24 (dagTagBases s447W 0xfc0fc0c3cc3c3333330cf0cf 0x2aa80281428844112510045 24) 6 s447Forest
def s447Moves := dagMoves ([] : List (DagMoveRecord 128))
def s447Check := dagCheckNode s447M s447G s447Chart (dagKnownCloses s447G s447Cuts) 33 s447States s447Moves s447Links s447Sample s447Tags
def s447RootAt (token : Nat) : Bool :=
  let st := rootState s447W 6 token
  !dagAllowedRoot s447Witness st.2.1 || dagLocal s447M s447G s447Chart (dagKnownCloses s447G s447Cuts) st || dagRef 33 s447States s447Moves s447Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s447Roots : dagCheckRoots s447M s447G s447Chart (dagKnownCloses s447G s447Cuts) s447Witness (dagRef 33 s447States s447Moves s447Links 0) s447W 6 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s447Blocks : treeBlock 0 33 s447Check = true := (@treeBlock_merge 0 32 1 s447Check (@treeBlock_merge 0 16 16 s447Check (@treeBlock_merge 0 8 8 s447Check (by decide +kernel) (by decide +kernel)) (@treeBlock_merge 16 8 8 s447Check (by decide +kernel) (by decide +kernel))) (by decide +kernel))
theorem s447Known : Known s447Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s337Lower) s326Lower) s306Lower) s234Lower)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s447Lower : Lower s447M s447W s447G 7 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s447Known _ s447Roots s447Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s447W; decide +kernel
  · decide +kernel
  · simp only [s447Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel

def s449M : Word := 0x330033000000000033003300
abbrev s449G := goal &&& s449M
abbrev s449W : List Word := projectDAGStock s449M base [0, 2, 4, 6]
def s449Fact : Bound := (s449M, s449W, 7, s449G)
def s449Witness := unpackWitnesses s449W [6668, 268809, 537097, 823817]
def s449Cuts : List Bound := [s236Fact, s308Fact, s329Fact, s340Fact]
def s449Chart : Option RowChart := some ⟨[13, 25, 28, 73, 76, 88, 13, 25, 28, 73, 76, 88, 9, 12, 24, 72, 9, 12, 24, 72, 9, 12, 24, 72], rfl⟩
def s449Sample : DagSample := (0x616012580c130124c0c124184924070121c24064181924034300d24160305824130184c2412412490c070181c0c064121906034120d, 24)
def s449Forest : Forest := fun i => decodeNode 6 18 0x24b0162b064b1e620058a5c32b058d9832864cd9831f064b1562054c50162948ca5202b058d8d31d34ca0e0363407c133618ca86028240d8601c1c0a86013064b0262008c5020080403c0 i
def s449Links : DagLinks := dagLookupLinks 0xe0f44d0313c06c4ac6b0a8664982608ce21845d4705b16c1a159151505404c530484e4380e0380b306801 0x7a4b0b310043143865268c7498149001d3d25855880198a1931c38c5260c7890148b0113265064ca0d31b183361e03a28044b496156200462838070480813629246523407840090e0280e02038ca0831b0f31d1a06c1804848140701c120501c070599b0a32a1006c180a824960362004628824b0fb159d620366565cc7ca18a1102b1803e1404c08040000f 10 4 12 6 1 5
def s449States := dagTrace s449M s449W 6 s449Forest
def s449Tags := dagTraceTags s449M 24 (dagTagBases s449W 0xfc0fc0c3cc3c3333330cf0cf 0x2aa80281428844112510045 24) 6 s449Forest
def s449Moves := dagMoves ([] : List (DagMoveRecord 128))
def s449Check := dagCheckNode s449M s449G s449Chart (dagKnownCloses s449G s449Cuts) 33 s449States s449Moves s449Links s449Sample s449Tags
def s449RootAt (token : Nat) : Bool :=
  let st := rootState s449W 6 token
  !dagAllowedRoot s449Witness st.2.1 || dagLocal s449M s449G s449Chart (dagKnownCloses s449G s449Cuts) st || dagRef 33 s449States s449Moves s449Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s449Roots : dagCheckRoots s449M s449G s449Chart (dagKnownCloses s449G s449Cuts) s449Witness (dagRef 33 s449States s449Moves s449Links 0) s449W 6 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s449Blocks : treeBlock 0 33 s449Check = true := (@treeBlock_merge 0 32 1 s449Check (@treeBlock_merge 0 16 16 s449Check (@treeBlock_merge 0 8 8 s449Check (by decide +kernel) (by decide +kernel)) (@treeBlock_merge 16 8 8 s449Check (by decide +kernel) (by decide +kernel))) (by decide +kernel))
theorem s449Known : Known s449Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s340Lower) s329Lower) s308Lower) s236Lower)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s449Lower : Lower s449M s449W s449G 7 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s449Known _ s449Roots s449Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s449W; decide +kernel
  · decide +kernel
  · simp only [s449Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel

def s451M : Word := 0x5500550000000000550055
abbrev s451G := goal &&& s451M
abbrev s451W : List Word := projectDAGStock s451M base [1, 2, 4, 6]
def s451Fact : Bound := (s451M, s451W, 5, s451G)
def s451Witness := unpackWitnesses s451W [9232, 272400, 533506, 820226]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s451Lower : Lower s451M s451W s451G 5 := by
  apply essentialLift (witnesses := s451Witness) (cut := s332M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s332W) (by decide +kernel)
  · exact s332Lower
  · decide +kernel

def s452M : Word := 0x550055000000000055005500
abbrev s452G := goal &&& s452M
abbrev s452W : List Word := projectDAGStock s452M base [1, 2, 4, 6]
def s452Fact : Bound := (s452M, s452W, 5, s452G)
def s452Witness := unpackWitnesses s452W [5128, 276504, 538636, 825356]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s452Lower : Lower s452M s452W s452G 5 := by
  apply essentialLift (witnesses := s452Witness) (cut := s340M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s340W) (by decide +kernel)
  · exact s340Lower
  · decide +kernel

def s457M : Word := 0x50505050000000005050505
abbrev s457G := goal &&& s457M
abbrev s457W : List Word := projectDAGStock s457M base [1, 3, 4, 6]
def s457Fact : Bound := (s457M, s457W, 5, s457G)
def s457Witness := unpackWitnesses s457W [5128, 267266, 533506, 820226]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s457Lower : Lower s457M s457W s457G 5 := by
  apply essentialLift (witnesses := s457Witness) (cut := s332M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s332W) (by decide +kernel)
  · exact s332Lower
  · decide +kernel

def s467M : Word := 0x33000000330000003300000033
abbrev s467G := goal &&& s467M
abbrev s467W : List Word := projectDAGStock s467M base [0, 2, 5, 6]
def s467Fact : Bound := (s467M, s467W, 5, s467G)
def s467Witness := unpackWitnesses s467W [2564, 264705, 541185, 819713]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s467Lower : Lower s467M s467W s467G 5 := by
  apply essentialLift (witnesses := s467Witness) (cut := s258M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s258W) (by decide +kernel)
  · exact s258Lower
  · decide +kernel

def s469M : Word := 0x3300000033000000330000003300
abbrev s469G := goal &&& s469M
abbrev s469W : List Word := projectDAGStock s469M base [0, 2, 5, 6]
def s469Fact : Bound := (s469M, s469W, 5, s469G)
def s469Witness := unpackWitnesses s469W [6668, 268809, 544776, 823817]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s469Lower : Lower s469M s469W s469G 5 := by
  apply essentialLift (witnesses := s469Witness) (cut := s308M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s308W) (by decide +kernel)
  · exact s308Lower
  · decide +kernel

def s478M : Word := 0x505000005050000050500000505
abbrev s478G := goal &&& s478M
abbrev s478W : List Word := projectDAGStock s478M base [1, 3, 5, 6]
def s478Fact : Bound := (s478M, s478W, 5, s478G)
def s478Witness := unpackWitnesses s478W [5128, 267266, 541698, 820226]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s478Lower : Lower s478M s478W s478G 5 := by
  apply essentialLift (witnesses := s478Witness) (cut := s271M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s271W) (by decide +kernel)
  · exact s271Lower
  · decide +kernel

def s485M : Word := 0x30003000300030003000300030003
abbrev s485G := goal &&& s485M
abbrev s485W : List Word := projectDAGStock s485M base [0, 4, 5, 6]
def s485Fact : Bound := (s485M, s485W, 5, s485G)
def s485Witness := unpackWitnesses s485W [8720, 270849, 541185, 819713]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s485Lower : Lower s485M s485W s485G 5 := by
  apply essentialLift (witnesses := s485Witness) (cut := s326M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s326W) (by decide +kernel)
  · exact s326Lower
  · decide +kernel

def s488M : Word := 0x3000300030003000300030003000300
abbrev s488G := goal &&& s488M
abbrev s488W : List Word := projectDAGStock s488M base [0, 4, 5, 6]
def s488Fact : Bound := (s488M, s488W, 5, s488G)
def s488Witness := unpackWitnesses s488W [12824, 274953, 544776, 823817]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s488Lower : Lower s488M s488W s488G 5 := by
  apply essentialLift (witnesses := s488Witness) (cut := s329M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s329W) (by decide +kernel)
  · exact s329Lower
  · decide +kernel

def s490M : Word := 0x50005000500050005000500050005
abbrev s490G := goal &&& s490M
abbrev s490W : List Word := projectDAGStock s490M base [1, 4, 5, 6]
def s490Fact : Bound := (s490M, s490W, 5, s490G)
def s490Witness := unpackWitnesses s490W [9232, 271362, 541698, 820226]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s490Lower : Lower s490M s490W s490G 5 := by
  apply essentialLift (witnesses := s490Witness) (cut := s332M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s332W) (by decide +kernel)
  · exact s332Lower
  · decide +kernel

def s494M : Word := 0x110011001100110011001100110011
abbrev s494G := goal &&& s494M
abbrev s494W : List Word := projectDAGStock s494M base [2, 4, 5, 6]
def s494Fact : Bound := (s494M, s494W, 5, s494G)
def s494Witness := unpackWitnesses s494W [10256, 272388, 542724, 821252]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s494Lower : Lower s494M s494W s494G 5 := by
  apply essentialLift (witnesses := s494Witness) (cut := s337M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s337W) (by decide +kernel)
  · exact s337Lower
  · decide +kernel

def s497M : Word := 0x11001100110011001100110011001100
abbrev s497G := goal &&& s497M
abbrev s497W : List Word := projectDAGStock s497M base [2, 4, 5, 6]
def s497Fact : Bound := (s497M, s497W, 5, s497G)
def s497Witness := unpackWitnesses s497W [14360, 276492, 544776, 825356]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s497Lower : Lower s497M s497W s497G 5 := by
  apply essentialLift (witnesses := s497Witness) (cut := s340M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s340W) (by decide +kernel)
  · exact s340Lower
  · decide +kernel

def s503M : Word := 0xffffffff
abbrev s503G := goal &&& s503M
abbrev s503W : List Word := projectDAGStock s503M base [0, 1, 2, 3, 4]
def s503Fact : Bound := (s503M, s503W, 7, s503G)
def s503Witness := unpackWitnesses s503W [2564, 267272, 526849, 791554, 1057281]
def s503Cuts : List Bound := [s379Fact, s380Fact, s234Fact]
def s503Chart : Option RowChart := some ⟨[5, 10, 17, 18, 20, 5, 10, 17, 18, 20, 5, 10, 3, 6, 9, 12, 24, 3, 6, 9, 12, 24, 3, 6], rfl⟩
def s503Sample : DagSample := (0x48500614060481212060440c110c0143014060500c140c0480c120184830110484406110c028180a048280c0a018281805048140c0501814301c06070301a0c0641219030582014020500613080480412080440211060380c0e06034120d0482c060b04028040a0301c0607020140205, 50)
def s503Forest : Forest := fun i => decodeNode 3 15 0xc382c40402080f8 i
def s503Links : DagLinks := dagLookupLinks 0x10840e1 0x78709880804001f 5 2 12 2 1 3
def s503States := dagTrace s503M s503W 6 s503Forest
def s503Tags := dagTraceTags s503M 50 (dagTagBases s503W 0x3f7fc01fff0000000f87c03fc30f001f8e0f0f3038f812733f0381c1e3133cf 0xc920164a000bba6e67c02e80b341548a0e0a4459198251173402caa1111c5 50) 6 s503Forest
def s503Moves := dagMoves ([] : List (DagMoveRecord 128))
def s503Check := dagCheckNode s503M s503G s503Chart (dagKnownCloses s503G s503Cuts) 4 s503States s503Moves s503Links s503Sample s503Tags
def s503RootAt (token : Nat) : Bool :=
  let st := rootState s503W 6 token
  !dagAllowedRoot s503Witness st.2.1 || dagLocal s503M s503G s503Chart (dagKnownCloses s503G s503Cuts) st || dagRef 4 s503States s503Moves s503Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s503Roots : dagCheckRoots s503M s503G s503Chart (dagKnownCloses s503G s503Cuts) s503Witness (dagRef 4 s503States s503Moves s503Links 0) s503W 6 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s503Blocks : treeBlock 0 4 s503Check = true := (by decide +kernel)
theorem s503Known : Known s503Cuts := (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s234Lower) s380Lower) s379Lower)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s503Lower : Lower s503M s503W s503G 7 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s503Known _ s503Roots s503Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s503W; decide +kernel
  · decide +kernel
  · simp only [s503Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl <;> decide +kernel

def s505M : Word := 0xffff0000ffff
abbrev s505G := goal &&& s505M
abbrev s505W : List Word := projectDAGStock s505M base [0, 1, 2, 3, 5]
def s505Fact : Bound := (s505M, s505W, 8, s505G)
def s505Witness := unpackWitnesses s505W [2564, 267272, 526849, 791554, 1065473]
def s505Cuts : List Bound := [s392Fact, s396Fact, s400Fact, s404Fact]
def s505Chart : Option RowChart := some ⟨[5, 10, 33, 34, 36, 40, 5, 10, 33, 34, 36, 40, 3, 6, 9, 12, 32, 3, 6, 9, 12, 32, 3, 6], rfl⟩
def s505Sample : DagSample := (0x30a00628048900624060881222060840c21100284005060a01228060900c2403088062204884062106028120a03028060a060141205030140605060b01229100a01028030984024020900623100880422100840221060380c0e06034120d0482c060b04028040a0301c0607020140205, 50)
def s505Forest : Forest := fun i => decodeNode 5 17 0x61c870e0326e1c38bc96058dc2c561c38949649880266e132b098f870e17258b620598a040dc2056101f0809870e052582620118a08020203e0 i
def s505Links : DagLinks := dagLookupLinks 0x94109210420748e81d03a0740c9190320640c8190320548a81502a0540a81502a054089018001 0x17c384e4b0d62014c517c384a4b0c62010c513c384a4b0b6200cc50dc38324b0b62008c505c38124b0362008c51ac39670e189375a4b15637518ad162040cdcf32b38c7ca314240dc802b1c07c601304020001f 11 5 12 5 1 6
def s505States := dagTrace s505M s505W 7 s505Forest
def s505Tags := dagTraceTags s505M 50 (dagTagBases s505W 0x3fcff00fff000c0b03c3c03fc0c1300f8e0f0f0c833c02733f00d030f4133cf 0x3000024a0002e38b33402e822cb8aa8a0e0ad1074cc251171d047554111c5 50) 7 s505Forest
def s505Moves := dagMoves ([] : List (DagMoveRecord 128))
def s505Check := dagCheckNode s505M s505G s505Chart (dagKnownCloses s505G s505Cuts) 27 s505States s505Moves s505Links s505Sample s505Tags
def s505RootAt (token : Nat) : Bool :=
  let st := rootState s505W 7 token
  !dagAllowedRoot s505Witness st.2.1 || dagLocal s505M s505G s505Chart (dagKnownCloses s505G s505Cuts) st || dagRef 27 s505States s505Moves s505Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s505Roots : dagCheckRoots s505M s505G s505Chart (dagKnownCloses s505G s505Cuts) s505Witness (dagRef 27 s505States s505Moves s505Links 0) s505W 7 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s505Blocks : treeBlock 0 27 s505Check = true := (@treeBlock_merge 0 16 11 s505Check (@treeBlock_merge 0 8 8 s505Check (by decide +kernel) (by decide +kernel)) (@treeBlock_merge 16 8 3 s505Check (by decide +kernel) (by decide +kernel)))
theorem s505Known : Known s505Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s404Lower) s400Lower) s396Lower) s392Lower)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s505Lower : Lower s505M s505W s505G 8 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s505Known _ s505Roots s505Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s505W; decide +kernel
  · decide +kernel
  · simp only [s505Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel

def s514M : Word := 0x3333333333333333
abbrev s514G := goal &&& s514M
abbrev s514W : List Word := projectDAGStock s514M base [0, 2, 3, 4, 5]
def s514Fact : Bound := (s514M, s514W, 7, s514G)
def s514Witness := unpackWitnesses s514W [2564, 264705, 544800, 795137, 1065473]
def s514Cuts : List Bound := [s400Fact, s412Fact, s414Fact, s234Fact]
def s514Chart : Option RowChart := some ⟨[5, 17, 20, 33, 36, 40, 5, 17, 20, 33, 36, 40, 9, 12, 24, 48, 9, 12, 24, 48, 9, 12, 24, 48], rfl⟩
def s514Sample : DagSample := (0xc09012240c0841821048501811180143005180a03028060a012281809018241808412211805030140605060110c0441211060141205180e03038180d06031060b01229100a010281009008241008402210c070181c0c064121908050081408044021106034120d020140205, 48)
def s514Forest : Forest := fun i => decodeNode 3 13 0xc5082640820f8 i
def s514Links : DagLinks := dagLookupLinks 0x10840e1 0x78a204c81001f 5 2 10 2 1 3
def s514States := dagTrace s514M s514W 6 s514Forest
def s514Tags := dagTraceTags s514M 48 (dagTagBases s514W 0xf0ff00fff0000c00fcf00ff000f000cf0f0ccb0ce328cccf37031f14333f 0x28a90b2a000a3cad8f00aa0fd756f4d0f0c14242208444a481105041115 48) 6 s514Forest
def s514Moves := dagMoves ([] : List (DagMoveRecord 128))
def s514Check := dagCheckNode s514M s514G s514Chart (dagKnownCloses s514G s514Cuts) 4 s514States s514Moves s514Links s514Sample s514Tags
def s514RootAt (token : Nat) : Bool :=
  let st := rootState s514W 6 token
  !dagAllowedRoot s514Witness st.2.1 || dagLocal s514M s514G s514Chart (dagKnownCloses s514G s514Cuts) st || dagRef 4 s514States s514Moves s514Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s514Roots : dagCheckRoots s514M s514G s514Chart (dagKnownCloses s514G s514Cuts) s514Witness (dagRef 4 s514States s514Moves s514Links 0) s514W 6 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s514Blocks : treeBlock 0 4 s514Check = true := (by decide +kernel)
theorem s514Known : Known s514Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s234Lower) s414Lower) s412Lower) s400Lower)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s514Lower : Lower s514M s514W s514G 7 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s514Known _ s514Roots s514Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s514W; decide +kernel
  · decide +kernel
  · simp only [s514Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel

def s520M : Word := 0xffff000000000000ffff
abbrev s520G := goal &&& s520M
abbrev s520W : List Word := projectDAGStock s520M base [0, 1, 2, 3, 6]
def s520Fact : Bound := (s520M, s520W, 7, s520G)
def s520Witness := unpackWitnesses s520W [2564, 267272, 526849, 791554, 1081857]
def s520Cuts : List Bound := [s430Fact, s431Fact, s306Fact]
def s520Chart : Option RowChart := some ⟨[5, 10, 65, 66, 68, 5, 10, 65, 66, 68, 5, 10, 3, 6, 9, 12, 72, 3, 6, 9, 12, 72, 3, 6], rfl⟩
def s520Sample : DagSample := (0x49100644061081242061040c41240149044061100c44241080c4201908904104904064124028180a048280c0a018281805048140c0501814904c06130904a241241249031188044021100643201080442201040241060380c0e06034120d0482c060b04028040a0301c0607020140205, 50)
def s520Forest : Forest := fun i => decodeNode 3 15 0xc382c40402080f8 i
def s520Links : DagLinks := dagLookupLinks 0x10840e1 0x78709880804001f 5 2 12 2 1 3
def s520States := dagTrace s520M s520W 6 s520Forest
def s520Tags := dagTraceTags s520M 50 (dagTagBases s520W 0x3f7fc01fff0000000f87c03fc30f001f8e0f0f3038f812733f0381c1e3133cf 0xc920164a000bba6e67c02e80b341548a0e0a4459198251173402caa1111c5 50) 6 s520Forest
def s520Moves := dagMoves ([] : List (DagMoveRecord 128))
def s520Check := dagCheckNode s520M s520G s520Chart (dagKnownCloses s520G s520Cuts) 4 s520States s520Moves s520Links s520Sample s520Tags
def s520RootAt (token : Nat) : Bool :=
  let st := rootState s520W 6 token
  !dagAllowedRoot s520Witness st.2.1 || dagLocal s520M s520G s520Chart (dagKnownCloses s520G s520Cuts) st || dagRef 4 s520States s520Moves s520Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s520Roots : dagCheckRoots s520M s520G s520Chart (dagKnownCloses s520G s520Cuts) s520Witness (dagRef 4 s520States s520Moves s520Links 0) s520W 6 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s520Blocks : treeBlock 0 4 s520Check = true := (by decide +kernel)
theorem s520Known : Known s520Cuts := (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s306Lower) s431Lower) s430Lower)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s520Lower : Lower s520M s520W s520G 7 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s520Known _ s520Roots s520Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s520W; decide +kernel
  · decide +kernel
  · simp only [s520Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl <;> decide +kernel

def s522M : Word := 0xff00ff0000000000ff00ff
abbrev s522G := goal &&& s522M
abbrev s522W : List Word := projectDAGStock s522M base [0, 1, 2, 4, 6]
def s522Fact : Bound := (s522M, s522W, 8, s522G)
def s522Witness := unpackWitnesses s522W [2564, 271376, 526849, 795137, 1081857]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s522Lower : Lower s522M s522W s522G 8 := by
  apply essentialLift (witnesses := s522Witness) (cut := s447M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s447W) (by decide +kernel)
  · exact s447Lower
  · decide +kernel

def s523M : Word := 0xff00ff0000000000ff00ff00
abbrev s523G := goal &&& s523M
abbrev s523W : List Word := projectDAGStock s523M base [0, 1, 2, 4, 6]
def s523Fact : Bound := (s523M, s523W, 8, s523G)
def s523Witness := unpackWitnesses s523W [6668, 267272, 530953, 799241, 1085961]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s523Lower : Lower s523M s523W s523G 8 := by
  apply essentialLift (witnesses := s523Witness) (cut := s449M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s449W) (by decide +kernel)
  · exact s449Lower
  · decide +kernel

def s525M : Word := 0xf0f0f0f000000000f0f0f0f
abbrev s525G := goal &&& s525M
abbrev s525W : List Word := projectDAGStock s525M base [0, 1, 3, 4, 6]
def s525Fact : Bound := (s525M, s525W, 7, s525G)
def s525Witness := unpackWitnesses s525W [8720, 267272, 529410, 795137, 1081857]
def s525Cuts : List Bound := [s443Fact, s444Fact, s457Fact, s326Fact]
def s525Chart : Option RowChart := some ⟨[10, 17, 18, 65, 66, 80, 10, 17, 18, 65, 66, 80, 3, 9, 24, 72, 3, 9, 24, 72, 3, 9, 24, 72], rfl⟩
def s525Sample : DagSample := (0x494006500c10812420c104901204848901124140305024108064224104124101904301201848301104844061124028300a04828060a2416030582014020502412890490492406432010804422010402410c06830190486406130804804120804402110482c060b04028040a, 48)
def s525Forest : Forest := fun i => decodeNode 3 15 0xc38326e64b080f8 i
def s525Links : DagLinks := dagLookupLinks 0x10840e1 0x7870a4dcc96001f 5 2 12 2 1 3
def s525States := dagTrace s525M s525W 6 s525Forest
def s525Tags := dagTraceTags s525M 48 (dagTagBases s525W 0xf8fe00fff000c7c1f0f00ff000000fce0e0f36318f09c9cf090e7007373c 0x5a808aca000284144500ca0bfed6ece0e0a401291014145d216b303131c 48) 6 s525Forest
def s525Moves := dagMoves ([] : List (DagMoveRecord 128))
def s525Check := dagCheckNode s525M s525G s525Chart (dagKnownCloses s525G s525Cuts) 4 s525States s525Moves s525Links s525Sample s525Tags
def s525RootAt (token : Nat) : Bool :=
  let st := rootState s525W 6 token
  !dagAllowedRoot s525Witness st.2.1 || dagLocal s525M s525G s525Chart (dagKnownCloses s525G s525Cuts) st || dagRef 4 s525States s525Moves s525Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s525Roots : dagCheckRoots s525M s525G s525Chart (dagKnownCloses s525G s525Cuts) s525Witness (dagRef 4 s525States s525Moves s525Links 0) s525W 6 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s525Blocks : treeBlock 0 4 s525Check = true := (by decide +kernel)
theorem s525Known : Known s525Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s326Lower) s457Lower) s444Lower) s443Lower)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s525Lower : Lower s525M s525W s525G 7 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s525Known _ s525Roots s525Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s525W; decide +kernel
  · decide +kernel
  · simp only [s525Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel

def s530M : Word := 0x555555550000000055555555
abbrev s530G := goal &&& s530M
abbrev s530W : List Word := projectDAGStock s530M base [1, 2, 3, 4, 6]
def s530Fact : Bound := (s530M, s530W, 7, s530G)
def s530Witness := unpackWitnesses s530W [5128, 272400, 529410, 795650, 1082370]
def s530Cuts : List Bound := [s451Fact, s452Fact, s457Fact, s337Fact]
def s530Chart : Option RowChart := some ⟨[10, 18, 20, 66, 68, 80, 10, 18, 20, 66, 68, 80, 6, 12, 24, 72, 6, 12, 24, 72, 6, 12, 24, 72], rfl⟩
def s530Sample : DagSample := (0x61400c500c1103042061089014240481812241403050241101844031109042031083014060500c140c0480c1224028300a060280c0a24160305820140205024130184c241280c462011008442010804420c070181c0c0680c16080500814080480412060380c0e04028040a, 48)
def s530Forest : Forest := fun i => decodeNode 3 15 0xc38326e64b080f8 i
def s530Links : DagLinks := dagLookupLinks 0x10840e1 0x7870a4dcc96001f 5 2 12 2 1 3
def s530States := dagTrace s530M s530W 6 s530Forest
def s530Tags := dagTraceTags s530M 48 (dagTagBases s530W 0xf8fe00fff000c7c1f0f00ff000000fce0e0f2439c00dcdcc1b063f03333f 0x6a408aaa000304124500aa0bff5aece0e0ac91ad305454c400a51011115 48) 6 s530Forest
def s530Moves := dagMoves ([] : List (DagMoveRecord 128))
def s530Check := dagCheckNode s530M s530G s530Chart (dagKnownCloses s530G s530Cuts) 4 s530States s530Moves s530Links s530Sample s530Tags
def s530RootAt (token : Nat) : Bool :=
  let st := rootState s530W 6 token
  !dagAllowedRoot s530Witness st.2.1 || dagLocal s530M s530G s530Chart (dagKnownCloses s530G s530Cuts) st || dagRef 4 s530States s530Moves s530Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s530Roots : dagCheckRoots s530M s530G s530Chart (dagKnownCloses s530G s530Cuts) s530Witness (dagRef 4 s530States s530Moves s530Links 0) s530W 6 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s530Blocks : treeBlock 0 4 s530Check = true := (by decide +kernel)
theorem s530Known : Known s530Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s337Lower) s457Lower) s452Lower) s451Lower)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s530Lower : Lower s530M s530W s530G 7 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s530Known _ s530Roots s530Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s530W; decide +kernel
  · decide +kernel
  · simp only [s530Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel

def s539M : Word := 0x3333000033330000333300003333
abbrev s539G := goal &&& s539M
abbrev s539W : List Word := projectDAGStock s539M base [0, 2, 3, 5, 6]
def s539Fact : Bound := (s539M, s539W, 7, s539G)
def s539Witness := unpackWitnesses s539W [2564, 264705, 544800, 803329, 1081857]
def s539Cuts : List Bound := [s400Fact, s467Fact, s469Fact, s306Fact]
def s539Chart : Option RowChart := some ⟨[5, 33, 36, 40, 65, 68, 5, 33, 36, 40, 65, 68, 9, 12, 72, 96, 9, 12, 72, 96, 9, 12, 72, 96], rfl⟩
def s539Sample : DagSample := (0x4910184124090122424084182130014900530110904406110c041241041241300a09028060a01228300901824300841221060141205301a0906830190c06124130184c241241249201100844201040241060b01229100a0102810090082410084022106034120d020140205, 48)
def s539Forest : Forest := fun i => decodeNode 3 13 0xc5082640820f8 i
def s539Links : DagLinks := dagLookupLinks 0x10840e1 0x78a204c81001f 5 2 10 2 1 3
def s539States := dagTrace s539M s539W 6 s539Forest
def s539Tags := dagTraceTags s539M 48 (dagTagBases s539W 0xc0fc00fff0003c03fcf00ff00003c0cf0f0cb3e0332cc8cf4f1c0f13343f 0x2bdb28faa000029228b002a0fd6dd74f0d0c44209204484a900445011415 48) 6 s539Forest
def s539Moves := dagMoves ([] : List (DagMoveRecord 128))
def s539Check := dagCheckNode s539M s539G s539Chart (dagKnownCloses s539G s539Cuts) 4 s539States s539Moves s539Links s539Sample s539Tags
def s539RootAt (token : Nat) : Bool :=
  let st := rootState s539W 6 token
  !dagAllowedRoot s539Witness st.2.1 || dagLocal s539M s539G s539Chart (dagKnownCloses s539G s539Cuts) st || dagRef 4 s539States s539Moves s539Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s539Roots : dagCheckRoots s539M s539G s539Chart (dagKnownCloses s539G s539Cuts) s539Witness (dagRef 4 s539States s539Moves s539Links 0) s539W 6 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s539Blocks : treeBlock 0 4 s539Check = true := (by decide +kernel)
theorem s539Known : Known s539Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s306Lower) s469Lower) s467Lower) s400Lower)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s539Lower : Lower s539M s539W s539G 7 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s539Known _ s539Roots s539Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s539W; decide +kernel
  · decide +kernel
  · simp only [s539Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel

def s548M : Word := 0x330033003300330033003300330033
abbrev s548G := goal &&& s548M
abbrev s548W : List Word := projectDAGStock s548M base [0, 2, 4, 5, 6]
def s548Fact : Bound := (s548M, s548W, 8, s548G)
def s548Witness := unpackWitnesses s548W [2564, 264705, 532993, 803329, 1081857]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s548Lower : Lower s548M s548W s548G 8 := by
  apply essentialLift (witnesses := s548Witness) (cut := s447M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s447W) (by decide +kernel)
  · exact s447Lower
  · decide +kernel

def s550M : Word := 0x33003300330033003300330033003300
abbrev s550G := goal &&& s550M
abbrev s550W : List Word := projectDAGStock s550M base [0, 2, 4, 5, 6]
def s550Fact : Bound := (s550M, s550W, 8, s550G)
def s550Witness := unpackWitnesses s550W [6668, 268809, 537097, 806920, 1085961]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s550Lower : Lower s550M s550W s550G 8 := by
  apply essentialLift (witnesses := s550Witness) (cut := s449M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s449W) (by decide +kernel)
  · exact s449Lower
  · decide +kernel

def s554M : Word := 0x3030303030303030303030303030303
abbrev s554G := goal &&& s554M
abbrev s554W : List Word := projectDAGStock s554M base [0, 3, 4, 5, 6]
def s554Fact : Bound := (s554M, s554W, 7, s554G)
def s554Witness := unpackWitnesses s554W [8720, 282656, 532993, 803329, 1081857]
def s554Cuts : List Bound := [s485Fact, s488Fact, s326Fact]
def s554Chart : Option RowChart := some ⟨[17, 33, 40, 65, 80, 17, 33, 40, 65, 80, 17, 33, 9, 24, 48, 72, 96, 9, 24, 48, 72, 96, 9, 24], rfl⟩
def s554Sample : DagSample := (0x494060410c10490210c084c01124044c0502414060500c140c041241041241300a09028180a03028048a0c02118084122118044301104844c070181c0c068241a0c061241603058201402050241241249201040241180e03038180c41229100a010281008402210c0641219080440211, 50)
def s554Forest : Forest := fun i => decodeNode 3 15 0xc382c40402080f8 i
def s554Links : DagLinks := dagLookupLinks 0x10840e1 0x78709880804001f 5 2 12 2 1 3
def s554States := dagTrace s554M s554W 6 s554Forest
def s554Tags := dagTraceTags s554M 50 (dagTagBases s554W 0x387f001fff0001803fc7c03fc21f800f8f0e0f0003e01b33731f8707e10f33f 0x5e6c417aa00045529a7402a81a1832c850e0abaad658b31532001092005115 50) 6 s554Forest
def s554Moves := dagMoves ([] : List (DagMoveRecord 128))
def s554Check := dagCheckNode s554M s554G s554Chart (dagKnownCloses s554G s554Cuts) 4 s554States s554Moves s554Links s554Sample s554Tags
def s554RootAt (token : Nat) : Bool :=
  let st := rootState s554W 6 token
  !dagAllowedRoot s554Witness st.2.1 || dagLocal s554M s554G s554Chart (dagKnownCloses s554G s554Cuts) st || dagRef 4 s554States s554Moves s554Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s554Roots : dagCheckRoots s554M s554G s554Chart (dagKnownCloses s554G s554Cuts) s554Witness (dagRef 4 s554States s554Moves s554Links 0) s554W 6 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s554Blocks : treeBlock 0 4 s554Check = true := (by decide +kernel)
theorem s554Known : Known s554Cuts := (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s326Lower) s488Lower) s485Lower)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s554Lower : Lower s554M s554W s554G 7 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s554Known _ s554Roots s554Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s554W; decide +kernel
  · decide +kernel
  · simp only [s554Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl <;> decide +kernel

def s556M : Word := 0x5050505050505050505050505050505
abbrev s556G := goal &&& s556M
abbrev s556W : List Word := projectDAGStock s556M base [1, 3, 4, 5, 6]
def s556Fact : Bound := (s556M, s556W, 8, s556G)
def s556Witness := unpackWitnesses s556W [5128, 267266, 533506, 803842, 1082370]
def s556Cuts : List Bound := [s423Fact, s457Fact, s478Fact, s490Fact]
def s556Chart : Option RowChart := some ⟨[10, 18, 34, 40, 66, 80, 10, 18, 34, 40, 66, 80, 2, 24, 48, 72, 96, 2, 24, 48, 72, 96, 2, 24], rfl⟩
def s556Sample : DagSample := (0x18108304224088302230048901230028600a011400428301409050181403050301089042300a09028180a0302830088602218048301224028300a301c06070301a090683018890580c160805008140904a201080442180e03038180c84028040a0402201088301a08048041204028040a, 50)
def s556Forest : Forest := fun i => decodeNode 5 17 0x61c064dc3871892c0b1b858ac3871392c9b1004cdc2656131f0e1c324b18c40c314081b840ac203e10130804870e052582620118a08020203e0 i
def s556Links : DagLinks := dagLookupLinks 0x849082103a4740e81d03a0648c8190320640c81902a4540a81502a0540a81502a054089018001 0x18c38524b0e62014c518c384e4b0d62010c514c384e4b0c6200cc50ec38364b0c62008c505c38124b0362008c51ac38664dd792c598dd562b49881133740cacf31f2cc50a037240ac801f1c04c600904020001f 11 5 12 5 1 6
def s556States := dagTrace s556M s556W 7 s556Forest
def s556Tags := dagTraceTags s556M 50 (dagTagBases s556W 0x302fc00fff0003040fc3e03f8032f00cc78e1c0340f0cd9364ffc0c3f08727f 0xb8cf22bd60008b2aae3a02d034430dd428e18741551c591248030000001025 50) 7 s556Forest
def s556Moves := dagMoves ([] : List (DagMoveRecord 128))
def s556Check := dagCheckNode s556M s556G s556Chart (dagKnownCloses s556G s556Cuts) 27 s556States s556Moves s556Links s556Sample s556Tags
def s556RootAt (token : Nat) : Bool :=
  let st := rootState s556W 7 token
  !dagAllowedRoot s556Witness st.2.1 || dagLocal s556M s556G s556Chart (dagKnownCloses s556G s556Cuts) st || dagRef 27 s556States s556Moves s556Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s556Roots : dagCheckRoots s556M s556G s556Chart (dagKnownCloses s556G s556Cuts) s556Witness (dagRef 27 s556States s556Moves s556Links 0) s556W 7 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s556Blocks : treeBlock 0 27 s556Check = true := (@treeBlock_merge 0 16 11 s556Check (@treeBlock_merge 0 8 8 s556Check (by decide +kernel) (by decide +kernel)) (@treeBlock_merge 16 8 3 s556Check (by decide +kernel) (by decide +kernel)))
theorem s556Known : Known s556Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s490Lower) s478Lower) s457Lower) s423Lower)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s556Lower : Lower s556M s556W s556G 8 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s556Known _ s556Roots s556Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s556W; decide +kernel
  · decide +kernel
  · simp only [s556Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel

def s559M : Word := 0x11111111111111111111111111111111
abbrev s559G := goal &&& s559M
abbrev s559W : List Word := projectDAGStock s559M base [2, 3, 4, 5, 6]
def s559Fact : Bound := (s559M, s559W, 7, s559G)
def s559Witness := unpackWitnesses s559W [10256, 282656, 534532, 804868, 1083396]
def s559Cuts : List Bound := [s494Fact, s497Fact, s337Fact]
def s559Chart : Option RowChart := some ⟨[20, 36, 40, 68, 80, 20, 36, 40, 68, 80, 20, 36, 12, 24, 48, 72, 96, 12, 24, 48, 72, 96, 12, 24], rfl⟩
def s559Sample : DagSample := (0x614060440c11090240c090c01424050c0502414060500c140c044241101844300a09028180a03028060a0c02418090182418050301406050c070181c0c068241a0c06424160305820140205024130184c201100844180e03038180d0182c100a010281009008240c070181c080500814, 50)
def s559Forest : Forest := fun i => decodeNode 3 15 0xc382c40402080f8 i
def s559Links : DagLinks := dagLookupLinks 0x10840e1 0x78709880804001f 5 2 12 2 1 3
def s559States := dagTrace s559M s559W 6 s559Forest
def s559Tags := dagTraceTags s559M 50 (dagTagBases s559W 0x387f001fff0001803fc7c03fc21f800f8f0e0f0003e01b33731f8707e10f33f 0x5e6c417aa00045529a7402a81a1832c850e0abaad658b31532001092005115 50) 6 s559Forest
def s559Moves := dagMoves ([] : List (DagMoveRecord 128))
def s559Check := dagCheckNode s559M s559G s559Chart (dagKnownCloses s559G s559Cuts) 4 s559States s559Moves s559Links s559Sample s559Tags
def s559RootAt (token : Nat) : Bool :=
  let st := rootState s559W 6 token
  !dagAllowedRoot s559Witness st.2.1 || dagLocal s559M s559G s559Chart (dagKnownCloses s559G s559Cuts) st || dagRef 4 s559States s559Moves s559Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s559Roots : dagCheckRoots s559M s559G s559Chart (dagKnownCloses s559G s559Cuts) s559Witness (dagRef 4 s559States s559Moves s559Links 0) s559W 6 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s559Blocks : treeBlock 0 4 s559Check = true := (by decide +kernel)
theorem s559Known : Known s559Cuts := (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s337Lower) s497Lower) s494Lower)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s559Lower : Lower s559M s559W s559G 7 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s559Known _ s559Roots s559Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s559W; decide +kernel
  · decide +kernel
  · simp only [s559Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl <;> decide +kernel

def s561M : Word := 0xffffffffffffffff
abbrev s561G := goal &&& s561M
abbrev s561W : List Word := projectDAGStock s561M base [0, 1, 2, 3, 4, 5]
def s561Fact : Bound := (s561M, s561W, 9, s561G)
def s561Witness := unpackWitnesses s561W [2564, 267272, 526849, 791554, 1057281, 1327617]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s561Lower : Lower s561M s561W s561G 9 := by
  apply essentialLift (witnesses := s561Witness) (cut := s505M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s505W) (by decide +kernel)
  · exact s505Lower
  · decide +kernel

def s563M : Word := 0xffffffff00000000ffffffff
abbrev s563G := goal &&& s563M
abbrev s563W : List Word := projectDAGStock s563M base [0, 1, 2, 3, 4, 6]
def s563Fact : Bound := (s563M, s563W, 10, s563G)
def s563Witness := unpackWitnesses s563W [2564, 267272, 526849, 791554, 1057281, 1344001]
def s563Cuts : List Bound := [s522Fact, s523Fact, s447Fact, s503Fact, s520Fact, s525Fact, s530Fact]
def s563Chart : Option RowChart := some ⟨[5, 10, 17, 18, 20, 65, 66, 68, 80, 5, 10, 17, 3, 6, 9, 12, 24, 72, 3, 6, 9, 12, 24, 72], rfl⟩
def s563Sample : DagSample := (0x614012500314006500c11012440191030420610812420c1041841031049014048500614240481812048489011060440c11240143005241403050241101844031109042031080642241041241019043014060500c140c0480c1201848301104844061124028300a06028120a03028060a06014120503014060524160305820140205024130184c241289049049240c462011008440190c804201108804100904301c06070301a0c0641219030582014020500613080480412080440211060380c0e06034120d0482c060b04028040a0301c0607020140205, 96)
def s563Forest : Forest := fun i => decodeNode 6 19 0x1e880c943a327f404fe98860bd13861c03250d1883a30e3432183250b5e9d6bd12d6275a940b8c9d698dc17a250c43a1e894b0e283100325089883130e22320c4620880860c94197a732f446589cc98d59310329406809cc80dc192818f4f31e8862538c4a11892c30c9c61908c1a01e04e3066868108c00f82f440988613d10861c0464308c6e13d10361c0662008010080fc0 i
def s563Links : DagLinks := dagLookupLinks 0x1bdb786f0de18f3095b6b61686d0519a2144288501a013c634c42881102113c6780ec5d83a1740c6588310620c0578af05e0b852ca504a0941282504a090518a304428810897a2a4540a81322604c0981302242d80d001 0x70f44649435692c403432e32b14314792507664f6264d6a6415e635546207404f3e04d4a0413a0352c01f1200852c381062070f44689435092c483432a32b0e3145c6346d25062c4d6ac4168c385a6362804d460412201d0c0085c6405c9406525062f4e60f445ec4e5a64e26041380352001d0a00852f440862052f440662056f4454c4350c38443433633704314340341e01c4d2503ec4d4ac4148c382864d4664144620320361c01e340401a01c34940412503ef4e3cf443ac4e2664138635366203204e1801e1e0401a0341e3401a3342f2502cf4f2af442894e269422492c2264e206421c04e1804210f440892c10f440692c08f4406c3814f4412c430ec380c6430a637046207af4472c436ec3866643586374e62042043300371601f020080003f 11 4 13 6 1 5
def s563States := dagTrace s563M s563W 9 s563Forest
def s563Tags := dagTraceTags s563M 96 (dagTagBases s563W 0xfff800ffe00003fffe000000f007fcc01ff003c001fff00000000000000fc33e01f00ff00e0703381c003c31c18e0f0f01c0e007038fc0093849ccfc00381f00e0703c06263133cf 0x492a4800802ac9400000009200140124401400164a000cdf6fbf4da6f333e01f00ba0a0984c1a0d02a811408a0e0a3209040b2590cc012809445c5643200160b15402221111c5 96) 9 s563Forest
def s563Moves := dagMoves ([] : List (DagMoveRecord 128))
def s563Check := dagCheckNode s563M s563G s563Chart (dagKnownCloses s563G s563Cuts) 62 s563States s563Moves s563Links s563Sample s563Tags
def s563RootAt (token : Nat) : Bool :=
  let st := rootState s563W 9 token
  !dagAllowedRoot s563Witness st.2.1 || dagLocal s563M s563G s563Chart (dagKnownCloses s563G s563Cuts) st || dagRef 62 s563States s563Moves s563Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s563Roots : dagCheckRoots s563M s563G s563Chart (dagKnownCloses s563G s563Cuts) s563Witness (dagRef 62 s563States s563Moves s563Links 0) s563W 9 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s563Blocks : treeBlock 0 62 s563Check = true := (@treeBlock_merge 0 32 30 s563Check (@treeBlock_merge 0 16 16 s563Check (@treeBlock_merge 0 8 8 s563Check (by decide +kernel) (by decide +kernel)) (@treeBlock_merge 16 8 8 s563Check (by decide +kernel) (by decide +kernel))) (@treeBlock_merge 32 16 14 s563Check (@treeBlock_merge 32 8 8 s563Check (by decide +kernel) (by decide +kernel)) (@treeBlock_merge 48 8 6 s563Check (by decide +kernel) (by decide +kernel))))
theorem s563Known : Known s563Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s530Lower) s525Lower) s520Lower) s503Lower) s447Lower) s523Lower) s522Lower)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s563Lower : Lower s563M s563W s563G 10 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s563Known _ s563Roots s563Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s563W; decide +kernel
  · decide +kernel
  · simp only [s563Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def s565M : Word := 0xffff0000ffff0000ffff0000ffff
abbrev s565G := goal &&& s565M
abbrev s565W : List Word := projectDAGStock s565M base [0, 1, 2, 3, 5, 6]
def s565Fact : Bound := (s565M, s565W, 9, s565G)
def s565Witness := unpackWitnesses s565W [2564, 267272, 526849, 791554, 1065473, 1344001]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s565Lower : Lower s565M s565W s565G 9 := by
  apply essentialLift (witnesses := s565Witness) (cut := s505M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s505W) (by decide +kernel)
  · exact s505Lower
  · decide +kernel

def s567M : Word := 0xff00ff00ff00ff00ff00ff00ff00ff
abbrev s567G := goal &&& s567M
abbrev s567W : List Word := projectDAGStock s567M base [0, 1, 2, 4, 5, 6]
def s567Fact : Bound := (s567M, s567W, 9, s567G)
def s567Witness := unpackWitnesses s567W [2564, 271376, 526849, 795137, 1065473, 1344001]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s567Lower : Lower s567M s567W s567G 9 := by
  apply essentialLift (witnesses := s567Witness) (cut := s522M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s522W) (by decide +kernel)
  · exact s522Lower
  · decide +kernel

def s568M : Word := 0xff00ff00ff00ff00ff00ff00ff00ff00
abbrev s568G := goal &&& s568M
abbrev s568W : List Word := projectDAGStock s568M base [0, 1, 2, 4, 5, 6]
def s568Fact : Bound := (s568M, s568W, 9, s568G)
def s568Witness := unpackWitnesses s568W [6668, 267272, 530953, 799241, 1069064, 1348105]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s568Lower : Lower s568M s568W s568G 9 := by
  apply essentialLift (witnesses := s568Witness) (cut := s523M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s523W) (by decide +kernel)
  · exact s523Lower
  · decide +kernel

def s569M : Word := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
abbrev s569G := goal &&& s569M
abbrev s569W : List Word := projectDAGStock s569M base [0, 1, 3, 4, 5, 6]
def s569Fact : Bound := (s569M, s569W, 9, s569G)
def s569Witness := unpackWitnesses s569W [8720, 267272, 529410, 795137, 1065473, 1344001]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s569Lower : Lower s569M s569W s569G 9 := by
  apply essentialLift (witnesses := s569Witness) (cut := s556M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s556W) (by decide +kernel)
  · exact s556Lower
  · decide +kernel

def s571M : Word := 0x33333333333333333333333333333333
abbrev s571G := goal &&& s571M
abbrev s571W : List Word := projectDAGStock s571M base [0, 2, 3, 4, 5, 6]
def s571Fact : Bound := (s571M, s571W, 10, s571G)
def s571Witness := unpackWitnesses s571W [2564, 264705, 544800, 795137, 1065473, 1344001]
def s571Cuts : List Bound := [s548Fact, s550Fact, s447Fact, s514Fact, s539Fact, s554Fact, s559Fact]
def s571Chart : Option RowChart := some ⟨[5, 17, 20, 33, 36, 40, 65, 68, 80, 5, 17, 20, 9, 12, 24, 48, 72, 96, 9, 12, 24, 48, 72, 96], rfl⟩
def s571Sample : DagSample := (0x614012501811030440491060410c10418412409030240489090210c084182130050901404850c01124044181130014900518014300530140905018140305030110904406110c041241041241300a09028180a03028060a0122830090602406090c0211808412211805030140605060110c0441211060141205301c06070301a0906830190c06124160305820140205024130184c241241249201100844201040241180e03038180d06031060b01229100a010281009008241008402210c070181c0c064121908050081408044021106034120d020140205, 96)
def s571Forest : Forest := fun i => decodeNode 6 19 0x1e880c943c4a182f44e92580c94364a0ec92cd86860c942f6275ec38bd29d7990301a75e32b05e895250ea7a25692ca86280c94244a0c892c9068320c524021832506d89cdb0e1b4a7363296c628d9901c0273602b064a06313cc61c1864f30c9c618dcc31b186203069c60cd8c0201e04e30050680d8c00982f440928613d108496043430865613d1034960631408010080fc0 i
def s571Links : DagLinks := dagLookupLinks 0x1bdb7865ac6575ae85c1b814e698530a614869051191318a30460884f99f03d17a0f05e0339660cc198321622c41883014f29c1382704e09c1382704e098528a504829011897c2a4540a81322604c0981302242d80d001 0x74c38686375a620443373231f14314792506634d6e34162329583144204d4e0413e02930013120085692c1062074f446c643546204c3432e31f0e31460328712506694d6e9416c92c5e32a2a04d4a041220110c00860340606406925066c4e64c386294e5e34e260353c029200110a00856c380862056f44066205af44589435492c483433a32b04314380281e010512504294d4e9414c92c2a34d4a341483143602a1c012380401a010386404525042c4e40c383e94e263353c3293a3143604e180121e0401a0281e0401a0283325030c4f2ec382c64f2a64e2863726636246202234e203361c04e1803610c380862010f440662008f440692c14f44129430e92c0c3430a32b043147af44769437292c6a3435c32b52314460433402b16013020080003f 11 4 13 6 1 5
def s571States := dagTrace s571M s571W 9 s571Forest
def s571Tags := dagTraceTags s571M 96 (dagTagBases s571W 0xff0000ffc00003ffff00000000fc00003ffc03f000fff000c003f0f00003f30f00f00ff0000000003f0000ccf0cf0f0c38e38f0e00e38c20cc28cccf071c7f01c01c7c103314333f 0x936ccdb09002faaa00000024024aa928da43b000b2a000364803300c4b610500f00aa0dbfdb556d725bc4cf04d0f0c81041002022088004408444a482080004104140011041115 96) 9 s571Forest
def s571Moves := dagMoves ([] : List (DagMoveRecord 128))
def s571Check := dagCheckNode s571M s571G s571Chart (dagKnownCloses s571G s571Cuts) 62 s571States s571Moves s571Links s571Sample s571Tags
def s571RootAt (token : Nat) : Bool :=
  let st := rootState s571W 9 token
  !dagAllowedRoot s571Witness st.2.1 || dagLocal s571M s571G s571Chart (dagKnownCloses s571G s571Cuts) st || dagRef 62 s571States s571Moves s571Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s571Roots : dagCheckRoots s571M s571G s571Chart (dagKnownCloses s571G s571Cuts) s571Witness (dagRef 62 s571States s571Moves s571Links 0) s571W 9 = true := (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s571Blocks : treeBlock 0 62 s571Check = true := (@treeBlock_merge 0 32 30 s571Check (@treeBlock_merge 0 16 16 s571Check (@treeBlock_merge 0 8 8 s571Check (by decide +kernel) (by decide +kernel)) (@treeBlock_merge 16 8 8 s571Check (by decide +kernel) (by decide +kernel))) (@treeBlock_merge 32 16 14 s571Check (@treeBlock_merge 32 8 8 s571Check (by decide +kernel) (by decide +kernel)) (@treeBlock_merge 48 8 6 s571Check (by decide +kernel) (by decide +kernel))))
theorem s571Known : Known s571Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s559Lower) s554Lower) s539Lower) s514Lower) s447Lower) s550Lower) s548Lower)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s571Lower : Lower s571M s571W s571G 10 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s571Known _ s571Roots s571Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s571W; decide +kernel
  · decide +kernel
  · simp only [s571Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def s573M : Word := 0x55555555555555555555555555555555
abbrev s573G := goal &&& s573M
abbrev s573W : List Word := projectDAGStock s573M base [1, 2, 3, 4, 5, 6]
def s573Fact : Bound := (s573M, s573W, 9, s573G)
def s573Witness := unpackWitnesses s573W [5128, 272400, 529410, 795650, 1065986, 1344514]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s573Lower : Lower s573M s573W s573G 9 := by
  apply essentialLift (witnesses := s573Witness) (cut := s556M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s556W) (by decide +kernel)
  · exact s556Lower
  · decide +kernel

def s575M : Word := 0xffffffffffffffffffffffffffffffff
abbrev s575G := goal &&& s575M
abbrev s575W : List Word := projectDAGStock s575M base [0, 1, 2, 3, 4, 5, 6]
def s575Fact : Bound := (s575M, s575W, 12, s575G)
def s575Witness := unpackWitnesses s575W [2564, 267272, 526849, 791554, 1057281, 1327617, 1606145]
def s575Cuts : List Bound := [s563Fact, s571Fact, s561Fact, s565Fact, s567Fact, s568Fact, s569Fact, s573Fact]
def s575Chart : Option RowChart := some ⟨[5, 10, 17, 18, 20, 33, 34, 36, 40, 65, 66, 68, 3, 6, 9, 12, 24, 48, 72, 96, 3, 6, 9, 12], rfl⟩
def s575Sample : DagSample := (0x61401250031400650181103044049100644181083042061081242181043041061040c41030a00628240903024048900624240883022060881222240843021060840c21300509014048500614300489012060481212300449011060440c1130028600a300149005180143005301409050181403050301109044061100c44301089042031080642301049041049040641300a09028180a03028060a01228300906024060900c24300886022030880622300846021048840621180503014060500c1418048301203048061218044301104844061124028300a06028120a03028060a060141205030140605301c06070301a0906830190c0623018490580c160805008140904c06130904a241241249031188044021100643201080442201040241180e03038180d06032180c4182c048a44028040a00c261009008240188c402201088402100884301c06070301a0c0641219030582014020500613080480412080440211060380c0e06034120d0482c060b04028040a0301c0607020140205, 170)
def s575Forest : Forest := fun i => decodeNode 9 22 0x24a00101549802526aaec800552300948eab92032dc800b7206278064a11e61c0064a118aae46d89f1892846587118496006abb0802145002514aae4218b708aae4424a110626c22ab90e61c422ab90a626c298710a4964200b708327806ab8eb7adbaeabb03aae40deb4eb7a2baeab8fe02d3f8024fe7a23aeab8fb61c3ed8b4ebaae3d9eb4f67a23d98b4f64963aeab8ed61c3b64a0f07a23c1258f04a63b5298ee3103b4cb4eb021bacc6e01928382ab8e8627b824a0e661c3824a0e1627b864a0e261c385258e0310006ababd021370054dcaae2f58b6bdaae3624a0d8626af6ab8d661c2f6ab8d2626b49870d24962f4cb6bdaae3324a0cc61c331258cc326af5e98c91a0325ec0c37ac30c668c66243158b0c332c30cc6ebdaae2f989abe61c2f9258be3102f409e01aae20deb683aaeae2ab8b87ad20de8a83aae2cc0b4b30152cde8883aae2c1870b062d20eab8ab7ad2ade88ab62d2ad258837a62a0680a87b028deb0a319a295890a462c28ccb683321a0eab8997ad265e889962d265870994962652989a32d264c6a83aae24deb4937a224d8b49349624cc4083aae21187084928235e888d496235298844a622cc40841a6a11898871a621c652844a62146288402d20c06e01aae0892987f1941fd2c07e7ad88aab87c7a208aab8797a21e587022c341dd2b622aae1c989a7261c1c9258724ad08a4a0704a188aab86a7ad1a9e886a62d1a92586a4a10880cc6702719d25a22aae185e886161c1840b46102118525822aae16589a5961c165258594a616cc6c59310164cb422aae141eb4507a21418b4504961412985232d140c405032108aab83b6268ed8703b4960ed2984a31b0ecc403b928109e8842496108c4042195108628421a60ed8804062a0f18983c49e0f52983c19b0ec0b422aae08deb4237a208d8b42349608d2983432d08cc40236200c58a82d6260b52782e4a60b46b42392809189c2461c09129c24496090c40241a70906282419a08c0842200f8064a002aae07d89e029280758700292806189e189280658701849600aab81362684d8701349604cc9e02aae02deb40b7a202d8b40b49602d2980c32d02cc6e0292800d89e0392801d870039280118700449600cc40020040040fe00 i
def s575Links : DagLinks := dagLookupLinks 0xb35ecd0b342cb2b2c2cb0b0a6c20b082b4eac12a97a8daa30a6a6982a49a88aa202880a2027f99fc27e19f467499d026e69b826d19b42649990256e941a50094025009222480920248092023f98f863d18d263408d023408cc62a98a462818a022808a0220888021f185a6160823a0448101fe67f09f847d89f607d81f427b99e7779c1e7079c1de97781dd17705d3974c1cd67341cc17301c3970c1c217045c016fc5b696d45b416c11ae26b81ac26a11a5366e99b066859a0668194661b9806600180060017885e017805e017805be56e15b456495901640590163156a55915605544548952054094c450a942050453f24f853c24ec53a14e813734ba52e04b812e04b452d049d92614945250494125047611d047051934641190458d16045450c93fb8f863e00f803d88eca3b00e663980e603764dd03704dc03688da03680d3734c0d213480d203480d023400c973240c9031c8c7031c0c7031c0c702fa4bd12e8cb912e04b802d88b512b24ab12a48a81294ca412900a22284498925c494324c4921248090223c48f023c08f023c08f023c087821c0852214085021048041de47611d087311c0c6f11bc06d21b046c01a886a01a80691195065019406501940650194065019405d8152446e10904200f183a20d903420d003400c882c60b002b10ac02b0095825009402500904240090023107581b206c01b00648190064017204d00c7006c001 0x479e888e30e1064a19d292c2ec686408cac2018a24e02a4980248db0e1114ac9f89413a12586c8d64b11a083e31449005491804925aaea4555c46925890996d0232ca1e64d3e8c6a7398812002d96e05935c09a5780d47d00f83c008465e887330e07c31b83a62047a4a08c30e10d4a79ca92c35469e3d8cac1c18a232f443e58867230e0ae3218f463706cc408dd570f84aca1694d3d926a71a4b0ad1ac9a634d2ac66a0d0c50e27a203292c4664a085313ce161c1a464f1e4c6e0c18811c928234c4f46187084a53cf549b9c092c34469e550cdc7819582e314441eb2873d110c61c1e894233c6b22f8ca41618a22a042450024792500f14a022355c4424a085a4b0ef31a14c0591d009a5180d45e00e82a00843aab88530e0731ac99a34d1746520a0c50ee49a21955c3e18b285b1350a61c1da9361c86b2660d345c19482631445aaba89d5711262da04c5943d89a86b0e1094961d86364200b6388164cb02694403716003a090021009281f2c381b869a500d0457194822314412aba81d570f84960da05931c09a4f80d45600e820008402ab87dbd68f761c1e695a2786822a8ca40f18a1fe05a3f8024792560f04a61f955c3ed8707b24b0ef32613a05931009a3580d45400e81c0083b92987cd570f87ad1eef443d98b476a5686a1a093633514c652068c50f162c1e0c4c3ca4a078bd10f04961dc62026809a2901045b0148180083b92987a5570f361c1de94c3b4c40288164c30268b403526405205802106aae20af5b409eb480bd14fd7a21f4c5a3d5258761968c202d9d60431a40824c00d44f00e814008399e887230e0973218126203a2ab871a4b0961ac98034d25066a040c50e27a200e92c39a4a070b0e0bf32780c620389e8802a4b0e292800892c3924a071b13ce161c17c64f24cc6e019880e99281cec4f3958707024b0bd1a79243370086286c3d64d67a21a8c383392b260a4b0911a109c32a3740846e00a88f1a011c340366ab86c4940d349618e6591d0c9a6218d4c031011803413403c6b5570d261c0e695933529a5fa4b04c195116334352ab856b164d36269a4c381c92b2662534be49611433612c654238ca04619408a32811065067d570ce92818ec5929989a66b0e0cc49618663622406c2080704000e18c94c329e9862b160c91a007e01c2200681f0070c619a07a01c3158902919304a01a07801c2692982180d0870140daf64321ec063bd609d632188c58144cc86199604902010c0340ec038428cd0c1aae12cc5930189a5fb0e0be49610833637aaba6dd570da62d96ec5935d89a6ab0e0d14961a065b1c4cb2659934c231b97a62020c06c1d0078b592815cc381b929a5025049749607232a2e6aba5c5570ad4960da659298c9a4e98d49631007001e2d6ab8583d68ac61c138941255258480d683719516805a2cc054478d608d1a616355c2c187055a4b09f32c94664d1acc6a4a18808c02606c01e22c698575570ad7ad158f442ad8b43525049b49a92692c2286b41a8ca83100e14a94c2a5e98523160a81a006001c268c68178070a519a05c01c2918902d98d03402605a01c1b5ec853bd80a67ac13ec6428d8b02d19009931a0660642240b01600702b19411004c0a8038148ca09a32605001c09c650130ca09a4a604a05821c0985055709f7ad13cf442758b44e30e09b49613265a2180b4118070851a612f55c259eb44abd109462d12692c2106b44731608d62611f250239e8846a4b08b31011034d0d0682250ca48518a11694c2212b0218cd087194110c4c0946b0438d30854a612355c2418704625308a31006635922469a248cd4861949083142eeab85d3d6cb77ad16cf452c9e8857b168aa49614465b284c863499049831a92462020c0b41100787c9280f4f441b989c32b0e0574a707234e2012983f8ca06d4b20fc9601d12b035a500563320bc658150c801c01904d02c06c0401f2ab83cbd107362d0c8c381752b4260d687aaae0f2f441c98b43531086361c0b895a14d284258d68351a10ef868148c681a00d075aae0dac591d189a39b0e0724960a26360cc06c3849405b32609404c1baab836bd686c7a20d6c5a1a92582d19684902d0d006619c09c32d570647a20c6c381652b4282508481ad0643421880b4308108471ac0b66340bc0b01680d0451a608834c16d298218130421a60bf55c1598b22f31345d61c0b892c168c6c2c9880410260580360ac6801f01302a01a052340148c981401603c02604c3341492981280a02419a0af55c159eb42abd105462d0a692c144cb42818803b02d046034118cb02518d03e1ac078334114c982219304a4a608634c108c9823c940467a207c94d0bd28222a4b04431008632a1086282031003d4a607a93c0fd8a81f3130284ac07894c13aab81c31644d626898c3812d2582498d84831008234c0ec66c1599002f1a605033409cc801a19302a1ac05a34c098c681a2530251940486340c58801725302e49e060c540bd8981525602d4a60572500a989c14b0e0284a704e92c098c40128d382418a07355c0e1eb41bbd103662d06a92c0cccb41918802c1ad046334206ab83ebd6c7b7a20f0c381d92b638a5686f4a18d294219925a3024b05832d09e6420e80b41101081d7a2036c3804528604a4b01faae03492c040cb20a99340e31a810620065e8803b0e01d928030c3805129e0324b0197a200ac380664a00230e01b928034c4f06187009a53c0d49b80692c030c680b55701062c82ac4d05187009a4b00b31b01864c03129808d570107ad01ef440398b406a4b00b32d00ef4401587003c9400461c00b25001187004c9400862780cc3800d2581049401e627838c3805d25809193c0a31b8046204a24a08fb13d1d61c22e92c41cc9e7518dcdf31017804f20806e10807c0100400007f 14 4 13 9 1 5
def s575States := dagTrace s575M s575W 11 s575Forest
def s575Tags := dagTraceTags s575M 170 (dagTagBases s575W 0x3fffc00000003fffc0000000003fffffc00000000000000fffc00000000ffffc00000fe0000ffff8000003c000000fff03c0000000fff003078003e001fff0000000c00000300000fc000003f0319f00c7807c03fc03c00f00f003c3c000f00f0003c20638091c18e0f0f00f003c03c3000f0003c03c3f004049c104e12733f0003c00f00f3c003c000f00f03c080c4c28263133cf 0x888cccb333330888000802fd5928000000000008880002223aa888a333222000ee0000b925000000033304440004cc000c444ccc401028003e00164a000c6763bf99d8556465c80991bcc119f0046807c02e82808e023023000c8023203202a800228011408a0e0a3101c40440400131004c44c433000094004a02511714c4131031000004c101301315400044408221111c5 170) 11 s575Forest
def s575Moves := dagMoves ([] : List (DagMoveRecord 128))
def s575Check := dagCheckNode s575M s575G s575Chart (dagKnownCloses s575G s575Cuts) 297 s575States s575Moves s575Links s575Sample s575Tags
def s575RootAt (token : Nat) : Bool :=
  let st := rootState s575W 11 token
  !dagAllowedRoot s575Witness st.2.1 || dagLocal s575M s575G s575Chart (dagKnownCloses s575G s575Cuts) st || dagRef 297 s575States s575Moves s575Links 0 token st
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s575Roots : dagCheckRoots s575M s575G s575Chart (dagKnownCloses s575G s575Cuts) s575Witness (dagRef 297 s575States s575Moves s575Links 0) s575W 11 = true := (@treeBlock_merge 0 64 64 s575RootAt (by decide +kernel) (by decide +kernel))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s575Blocks : treeBlock 0 297 s575Check = true := (@treeBlock_merge 0 256 41 s575Check (@treeBlock_merge 0 128 128 s575Check (@treeBlock_merge 0 64 64 s575Check (@treeBlock_merge 0 32 32 s575Check (@treeBlock_merge 0 16 16 s575Check (@treeBlock_merge 0 8 8 s575Check (by decide +kernel) (by decide +kernel)) (@treeBlock_merge 16 8 8 s575Check (by decide +kernel) (by decide +kernel))) (@treeBlock_merge 32 16 16 s575Check (@treeBlock_merge 32 8 8 s575Check (by decide +kernel) (by decide +kernel)) (@treeBlock_merge 48 8 8 s575Check (by decide +kernel) (by decide +kernel)))) (@treeBlock_merge 64 32 32 s575Check (@treeBlock_merge 64 16 16 s575Check (@treeBlock_merge 64 8 8 s575Check (by decide +kernel) (by decide +kernel)) (@treeBlock_merge 80 8 8 s575Check (by decide +kernel) (by decide +kernel))) (@treeBlock_merge 96 16 16 s575Check (@treeBlock_merge 96 8 8 s575Check (by decide +kernel) (by decide +kernel)) (@treeBlock_merge 112 8 8 s575Check (by decide +kernel) (by decide +kernel))))) (@treeBlock_merge 128 64 64 s575Check (@treeBlock_merge 128 32 32 s575Check (@treeBlock_merge 128 16 16 s575Check (@treeBlock_merge 128 8 8 s575Check (by decide +kernel) (by decide +kernel)) (@treeBlock_merge 144 8 8 s575Check (by decide +kernel) (by decide +kernel))) (@treeBlock_merge 160 16 16 s575Check (@treeBlock_merge 160 8 8 s575Check (by decide +kernel) (by decide +kernel)) (@treeBlock_merge 176 8 8 s575Check (by decide +kernel) (by decide +kernel)))) (@treeBlock_merge 192 32 32 s575Check (@treeBlock_merge 192 16 16 s575Check (@treeBlock_merge 192 8 8 s575Check (by decide +kernel) (by decide +kernel)) (@treeBlock_merge 208 8 8 s575Check (by decide +kernel) (by decide +kernel))) (@treeBlock_merge 224 16 16 s575Check (@treeBlock_merge 224 8 8 s575Check (by decide +kernel) (by decide +kernel)) (@treeBlock_merge 240 8 8 s575Check (by decide +kernel) (by decide +kernel)))))) (@treeBlock_merge 256 32 9 s575Check (@treeBlock_merge 256 16 16 s575Check (@treeBlock_merge 256 8 8 s575Check (by decide +kernel) (by decide +kernel)) (@treeBlock_merge 272 8 8 s575Check (by decide +kernel) (by decide +kernel))) (@treeBlock_merge 288 8 1 s575Check (by decide +kernel) (by decide +kernel))))
theorem s575Known : Known s575Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s573Lower) s569Lower) s568Lower) s567Lower) s565Lower) s561Lower) s571Lower) s563Lower)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem s575Lower : Lower s575M s575W s575G 12 := by
  apply lowerDag _ _ _ _ (dagMovesOfCheck (cert := ([] : List (DagMoveRecord 128))) (by decide +kernel)) _ _ _ s575Known _ s575Roots s575Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s575W; decide +kernel
  · decide +kernel
  · simp only [s575Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def edgeFunction (x : Fin 7 → Bool) : Bool := (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 edgeFunction t → 12 ≤ t := by
  let raw : List (BitVec 128) := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000]
  let target : BitVec 128 := 0xfffffffefffffefefffefffefefeeca0
  have root : Lower (fullMask 128) (raw.map BitVec.toNat) target.toNat 12 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) s575Lower
  exact hcsLower raw target 12 edgeFunction (by decide +kernel) (by decide +kernel) root

def edgeFn (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem edgeFn_eq : ∀ x : Fin 7 → Bool, edgeFn x = edgeFunction x := by
  decide +kernel

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or,[0,2]⟩,
    ⟨.or,[4,6]⟩,
    ⟨.or,[7,1]⟩,
    ⟨.or,[8,5]⟩,
    ⟨.and,[9,10]⟩,
    ⟨.and,[0,2]⟩,
    ⟨.and,[4,6]⟩,
    ⟨.or,[1,5]⟩,
    ⟨.and,[3,14]⟩,
    ⟨.or,[11,12]⟩,
    ⟨.or,[13,15]⟩,
    ⟨.or,[16,17]⟩], 18⟩

def aoCheck (g : PEqualNP.CircuitLowerBounds.Gate) : Bool :=
  match g.op with
  | .and | .or => decide (g.inputs.length ≤ 2)
  | _ => false

theorem witnessAO : ∀ g ∈ witness.gates,
    (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  have allOK : witness.gates.all aoCheck = true := by decide +kernel
  have h := List.all_eq_true.mp allOK g hg
  cases he : g.op <;> simp [aoCheck, he] at h ⊢ <;> exact h

theorem witnessSize : witness.gates.length = 12 := rfl

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem witnessEval : ∀ x : Fin 7 → Bool, witness.eval (List.ofFn x) = edgeFn x := by
  decide +kernel

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hfan _hone heval
  have hcs : PEqualNP.MetaComplexity.HasCircuitSize 7 edgeFunction gates.length := by
    refine ⟨⟨gates, o⟩, ?_, Nat.le_refl _, ?_⟩
    · intro g hg
      have h := hfan g hg
      exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact h.1, h.2⟩
    · intro x
      exact (heval x).trans (edgeFn_eq x)
  have h12 : 12 ≤ gates.length := lower gates.length hcs
  exact ⟨witness.gates, witness.output, witnessAO, witnessSize ▸ h12, witnessEval⟩

end PEqualNP.Outside.L_meta_10578

theorem PEqualNP.Outside.L_meta_10578 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  PEqualNP.Outside.L_meta_10578.main
