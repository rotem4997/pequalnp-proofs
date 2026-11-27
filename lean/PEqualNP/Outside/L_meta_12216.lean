import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12216

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

theorem hcsEvalWord {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n)) 
    (f : (Fin n → Bool) → Bool)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin n => r.testBit j.val) n 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f (fun j : Fin n => r.testBit j.val)) n 0 = true)
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hev : ∀ x, C.eval (List.ofFn x) = f x) :
    (C.gates.foldl hcsStep raw).getD C.output 0 = goal := by
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

theorem hcsLower {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n)) (min : Nat)
    (f : (Fin n → Bool) → Bool)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin n => r.testBit j.val) n 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f (fun j : Fin n => r.testBit j.val)) n 0 = true)
    (claim : Lower (fullMask (2 ^ n)) (raw.map BitVec.toNat) goal.toNat min)
    (t : Nat) (h : PEqualNP.MetaComplexity.HasCircuitSize n f t) : min ≤ t := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  obtain ⟨vs, len, built, sub⟩ := hcsBuilds raw C.gates hfan
  let eb := C.gates.foldl hcsStep raw
  have same : eb.getD C.output 0 = goal := hcsEvalWord raw goal f hRaw hGoal C hfan hev
  have av : AvailableWord (fullMask (2 ^ n)) (vs ++ raw.map BitVec.toNat) goal.toNat := by
    rw [← same, List.getD_eq_getElem?_getD]
    cases h : eb[C.output]? with
    | none => exact Or.inl rfl
    | some v => exact Or.inr (Or.inr (sub v (List.mem_of_getElem? h)))
  have lb := claim vs built av
  have hs : C.gates.length ≤ t := hsz
  omega

def moveStage0 : WordMoveStep := ([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)])
def moveStage1 : WordMoveStep := ([(0xf00ff00ff00ff00f, 0), (0xf000f000f000f0, 4)], [(0xf000f000f000f00, 4)])
def moveStage2 : WordMoveStep := ([(0xf0f00f0ff0f00f0f, 0), (0xf0f00000f0f0, 12)], [(0xf0f00000f0f0000, 12)])
def moveStage3 : WordMoveStep := ([(0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)])
def moveStage4 : WordMoveStep := ([(0xcc33cc33cc33cc33, 0), (0xcc00cc00cc00cc, 6)], [(0x3300330033003300, 6)])
def moveStage5 : WordMoveStep := ([(0xcccc3333cccc3333, 0), (0xcccc0000cccc, 14)], [(0x3333000033330000, 14)])
def moveStage6 : WordMoveStep := ([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])
def moveStage7 : WordMoveStep := ([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])
def moveStage8 : WordMoveStep := ([(0xaa55aa55aa55aa55, 0), (0xaa00aa00aa00aa, 7)], [(0x5500550055005500, 7)])
def moveStage9 : WordMoveStep := ([(0xaaaa5555aaaa5555, 0), (0xaaaa0000aaaa, 15)], [(0x5555000055550000, 15)])
def moveStage10 : WordMoveStep := ([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])
def moveStages : Array WordMoveStep := #[moveStage0, moveStage1, moveStage2, moveStage3, moveStage4, moveStage5, moveStage6, moveStage7, moveStage8, moveStage9, moveStage10]
def sBase : List Word := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def sGoal : Word := 0xe880e880e8808000
def s0Mask : Word := 0xffffffff
abbrev s0Goal : Word := sGoal &&& s0Mask
abbrev s0StockWords : List Word := projectDAGStock s0Mask sBase [0, 1, 2, 3, 4]
def s0Fact : Bound := (s0Mask, s0StockWords, 9, s0Goal)
def s0Cuts : List Bound := []
def s0Chart : Option RowChart := some ⟨[15, 23, 27, 29, 30, 15, 15, 15, 15, 15, 15, 15, 7, 11, 13, 14, 19, 21, 22, 25, 26, 28, 7, 7], rfl⟩
def s0Sample : DagSample := (0xe07c321f0e078341e0b0781c1e0e074321d0a8741a1d0d06c321b0986c161b0b05c2a170985c0e170703c1a0f0583c0e0f, 22)
def s0Witnesses := unpackWitnesses s0StockWords [14876, 277532, 539674, 801814, 1063950]
def s0Links : DagLinks := 
  dagLookupLinks 0x30040000000bf0afa1be06f23bc06ee1b7a00000002d640002d03b386c83b186c410002c21aca2895a0127e100027c19d8e6680000000980e5c2000000096080000002504000000093080000000000911228e0002242888400000021c3000218283180000000000818e04180080007e8dee66fe00006e89b816d85b036b859e800019645b556a1589000058055a352a0000510c0000001402000138400011ce46091610000000440d04600000003f8cfc13360000318c000000000027d09c10000944000090223840000000845000000000000001e943fe00f8001 0xf4c3c05b62406933007c03007ac3c07903005a318059318076c3c05831806c030057624056624074c3807392c2ee6202de31a05e31905531806e31400f0080546240f10400710340700100ee93c06e9300683240533180ec93c06c93005231805162405062404f3180e9c3806992c2e86202dd31a05d31904e3180683140670080fbf4407bc380f89420f793e0f593d0f293c07893607793207593107293006f92c2ed6202dc31a05c31904d31806d31403802906b02606a02506602400d0085619484e193c1e164816163c05b934062c3c1486280483282c831c161c3e06193e06093014762804733404a31c3af0312af0250de93c05e93005d0240d793005032405993005302405792c05662004231400c0080d36300536240d092c05062004131404f0080dbc3805b92c0da6320d86310d563005a62605862505562405462004031405201a05101904e01800b0082c96240493242c86240499300486240460242c662404632404bc3c2ca6302c762404a3300473240450300c26300426240413180406282bd02403d00c0bd33003d32429d3180be63c03e63079f62461f3182bc02403c00c0e3f44064c3f063c3835f93e2df9322cc92c0df63e05f6322dc62a05c62904d62804c6200c43420c333e04433604333203f31442e03f3ae0337aa02562a01903b01101a00d00a0080b993c03993002700c02600c0b693c03693002500c02431888fc3880f92c03462061531462900e02900d02300c0150080223181b204013203403202888df4480dc3878d92c1b86421b763e1b563d1b363c13863613763213563113363003862a03762603562503362403162061431462800e02800d02100c01400812d33012f63c02f6303ac33c2ac33002d93029d31c01d01c61d01032c93e2ac9320ac63e02c63202b62429c31c01c02801f0101a963c1296300296240a663002662488c92c80c62002431401900888bc3880b92c78b6201a73321a53311a333012732612532512332402731a02531902331802231401800861e31801e01861d31809e63001e62401d3180a093c02093061f32461c31801f02401c01819933011932401931801831c88af4422ec3f80ac380ae93f02e93378a92c72a63e6aa63262a6266136201aa33e12a33202a32662831e02831d02131c01331419b04219a03e11b03611a03201b02a01a02601700819563c115630015624889f44809c3878992c60962041434241333e39433639333229432a29332601431e01331a41204241103e39203639103229202a29102601201e01101a00c31808f93c00f93000b31800e02408c63000c62400b628188c3810892c008620603314003008883c3880392c783620603314003008409c39407c3858d93758a93338992d38792c50d63750a63348d62b48a62728962128762018d33718a33310d32b10a32700d31f00a31b00931500731440603740503338602b38502728601f28501b00601300500f004009002008890c39881c385e59375ba93381092d80192c56563753a6334e562b4ba6277906217816201e53371ba33316532b13a32706531f03a31b6103156013144300374160333b002b3960272b001f29601b03001301600f01000900100800001f 14 5 12 7 5 5
def s0Data : Forest := fun i => decodeNode 7 19 0x187cc38cd879e40c3cc9b66932cd879da4c7361c7392ce7261980d380087092ccd261b8c5334986c026cc04b9a4b3398a67008ce04998c7c0e1fbbc38778798a4fb0498606327726174092eb14bb92c9cc4d3a4c2cb12ce92cacc415989273104e624a60353806673104f0089e031398a1db103bc3c8a661164c24312483248a649180c2299b3b33276c4904c620b144031476c60f0c91e8063c01176636064c1cb153162663260d98958b103462462050c98818809816305f2665e4c16b192b6245664c5d891498e9731a44c4898c65118a243184462888c70bc981c02438c4874c60e80c1c02a2e04c5cc60c98e180082e01e05890a98f1131a2203c440688804819301c04838c7c13120c6281663608c54131008314040260803c1004820080601008020080f80 i
def s0Tags := dagTraceTags s0Mask 22 (dagTagBases s0StockWords 0x3ffff0fffc3fff0fffc3fff0ffff 0x3eeee0f7743abb0dd1c2eed07777 22) 8 s0Data
def s0States := dagTrace s0Mask s0StockWords 8 s0Data
def s0Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 3, 5] 0 i.val)
def s0Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 3, 5] 0 i.val)
def s0Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s0Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s0Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 2, 3, 5] 0 i.val)
def s0Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 4, 2, 5] 0 i.val)
def s0Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 4, 2, 5] 0 i.val)
def s0Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 2, 3, 5] 0 i.val)
def s0Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)
def s0Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)
def s0Move5Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 1, 4, 3, 5] 0 i.val)
def s0Move5Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 1, 4, 3, 5] 0 i.val)
def s0Move6Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 3, 1, 2, 4, 5] 0 i.val)
def s0Move6Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 3, 1, 4, 5] 0 i.val)
def s0Move7Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 1, 2, 3, 5] 0 i.val)
def s0Move7Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 3, 4, 1, 5] 0 i.val)
def s0Move8Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 3, 1, 4, 5] 0 i.val)
def s0Move8Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 3, 1, 2, 4, 5] 0 i.val)
def s0Move9Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 4, 1, 3, 5] 0 i.val)
def s0Move9Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 3, 1, 4, 2, 5] 0 i.val)
def s0Move10Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 3, 4, 1, 2, 5] 0 i.val)
def s0Move10Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 3, 4, 1, 2, 5] 0 i.val)
def s0Move11Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s0Move11Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s0Move12Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val)
def s0Move12Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val)
def s0Move13Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 4, 2, 3, 5] 0 i.val)
def s0Move13Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 3, 4, 2, 5] 0 i.val)
def s0Move14Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 0, 1, 3, 4, 5] 0 i.val)
def s0Move14Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 2, 0, 3, 4, 5] 0 i.val)
def s0Move15Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 0, 1, 2, 4, 5] 0 i.val)
def s0Move15Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 2, 3, 0, 4, 5] 0 i.val)
def s0Move16Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 0, 1, 2, 3, 5] 0 i.val)
def s0Move16Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 2, 3, 4, 0, 5] 0 i.val)
def s0MoveCert : List (DagMoveRecord 64) := [((moveSchedule moveStages [0]), s0Move0Map, s0Move0Inverse), ((moveSchedule moveStages [1]), s0Move1Map, s0Move1Inverse), ((moveSchedule moveStages [2, 0]), s0Move2Map, s0Move2Inverse), ((moveSchedule moveStages [1, 0]), s0Move3Map, s0Move3Inverse), ((moveSchedule moveStages [3]), s0Move4Map, s0Move4Inverse), ((moveSchedule moveStages [3, 0]), s0Move5Map, s0Move5Inverse), ((moveSchedule moveStages [4, 1]), s0Move6Map, s0Move6Inverse), ((moveSchedule moveStages [5, 2, 0]), s0Move7Map, s0Move7Inverse), ((moveSchedule moveStages [3, 1]), s0Move8Map, s0Move8Inverse), ((moveSchedule moveStages [3, 2, 0]), s0Move9Map, s0Move9Inverse), ((moveSchedule moveStages [4, 2]), s0Move10Map, s0Move10Inverse), ((moveSchedule moveStages [6]), s0Move11Map, s0Move11Inverse), ((moveSchedule moveStages [6, 1]), s0Move12Map, s0Move12Inverse), ((moveSchedule moveStages [6, 2, 0]), s0Move13Map, s0Move13Inverse), ((moveSchedule moveStages [7, 3]), s0Move14Map, s0Move14Inverse), ((moveSchedule moveStages [8, 4, 1]), s0Move15Map, s0Move15Inverse), ((moveSchedule moveStages [9, 5, 2, 0]), s0Move16Map, s0Move16Inverse)]
def s0Moves := dagMoves s0MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Autos : DagMovesOK s0Mask s0Goal 64 s0Moves := dagMovesOfCheck (by decide +kernel)
def s0Check := dagCheckNode s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) 125 s0States s0Moves s0Links s0Sample s0Tags
def s0RootAt (token : Nat) : Bool :=
  let s := rootState s0StockWords 8 token
  !dagAllowedRoot s0Witnesses s.2.1 || dagLocal s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) s ||
  dagRef 125 s0States s0Moves s0Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0RootBlock0 : treeBlock 0 32 s0RootAt = true := by decide +kernel
theorem s0Roots : dagCheckRoots s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) s0Witnesses (dagRef 125 s0States s0Moves s0Links 0) s0StockWords 8 = true := s0RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Block0 : treeBlock 0 16 s0Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Block16 : treeBlock 16 16 s0Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Block32 : treeBlock 32 16 s0Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Block48 : treeBlock 48 16 s0Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Block64 : treeBlock 64 16 s0Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Block80 : treeBlock 80 16 s0Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Block96 : treeBlock 96 16 s0Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Block112 : treeBlock 112 13 s0Check = true := by decide +kernel
theorem s0Verified : treeBlock 0 125 s0Check = true := (@treeBlock_merge 0 64 61 s0Check (@treeBlock_merge 0 32 32 s0Check (@treeBlock_merge 0 16 16 s0Check s0Block0 s0Block16) (@treeBlock_merge 32 16 16 s0Check s0Block32 s0Block48)) (@treeBlock_merge 64 32 29 s0Check (@treeBlock_merge 64 16 16 s0Check s0Block64 s0Block80) (@treeBlock_merge 96 16 13 s0Check s0Block96 s0Block112)))
theorem s0Blocks : treeBlock 0 125 s0Check = true := s0Verified
theorem s0Known : Known s0Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Stock : Lower s0Mask s0StockWords s0Goal 9 := by
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
def s1Mask : Word := 0xffff0000ffff
abbrev s1Goal : Word := sGoal &&& s1Mask
abbrev s1StockWords : List Word := projectDAGStock s1Mask sBase [0, 1, 2, 3, 5]
def s1Fact : Bound := (s1Mask, s1StockWords, 9, s1Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Stock : Lower s1Mask s1StockWords s1Goal 9 := dagShiftLower (width := 64) (moveSchedule moveStages [10]) s0Stock (by decide +kernel)
def s2Mask : Word := 0xffffffffffffffff
abbrev s2Goal : Word := sGoal &&& s2Mask
abbrev s2StockWords : List Word := projectDAGStock s2Mask sBase [0, 1, 2, 3, 4, 5]
def s2Cuts : List Bound := [s0Fact, s1Fact]
def s2Chart : Option RowChart := some ⟨[15, 23, 27, 29, 30, 39, 43, 45, 46, 15, 15, 15, 51, 53, 54, 57, 58, 60, 7, 11, 13, 14, 51, 51], rfl⟩
def s2Sample : DagSample := (0x1e0fc743f1c8fc1c3f068fc783e1d0f86c3e068f8783d1d0f4723d1a8f41c3d1e0ec743b1c8ec663b070ec78371b0dc6a37198dc1c371d0b86c2e160b8542e070b8722d1a8b4582d148b41a2d1d0ac662b150ac522b058ac6c271989c0e271d0786c1e0e078341e07078721d1a874381d0c8741a1d1d06c661b0d06c321b0586c6c171985c0e171e03c1c0f0683c180f0583c0e0f, 66)
def s2Witnesses := unpackWitnesses s2StockWords [31292, 293948, 556090, 818230, 1063950, 1334286]
def s2Links : DagLinks := 
  dagLookupLinks 0xcca8600003306900000cc00797d0c000065ad2c9be80000324e864981000000000324a0e4550c7cb98f5131d84e3ac100000000031d01e38c5000018e00f1be0e31d8c61898bd18000062e83c5b878a25713c262606c4b838940f1202623c1c448d8860f10a0e20c2c41038800b0fe080000c3b91876070e426185100001860070b62e1681c203583f0707a100000000018371b06a160c05c170582d07052260944c12020000303a3dff60bfb8d7f50afe02dfb82bf48b7df2af57a5ea030000000000000000000bc9ab7910af182de243bbe1b7589000005d5430000175406ea2180000ba78574c0c000000000ba09773e0c00005cf020000173a0ae68300000b988771c5400005c6c1000017190ae2c180000b85976f656de6180000b760e00000000000000000016e032dba1db605000016d60ada6180000b688400002da0080000b678200002d96200000b64856bc3400005aad1b55036a70ed4c080000b520569f1400005a703b4d836980ed08a597e5b2d8800002cb01d9543b288965006c9e0d92c4000016490ac843d8e88b1b0963506c5a458ac2b148562416c460d8842b0b1600002c24200000b070800002c161800000000160908000058144000015f73abea100000af9855ee16ba4e57441ae7075cd06b902d70c5adc955b806b6e0d6cc4ad8855b006b5c100000ad6055a716b481d668a0000000002b2c256541ac90600002b1e1d63420000000002b1220000000001585100000560c20000000002b00180000000015713eae00800000000156f06aaec548f4a82bd50406a00200000a7c8f4f8069ea1d3c83000014ed169b2a53505a668f4c81697c552e06a5a874b11295c1d29c7000014a40e934552584a480c000029162d2203000014870400000000000001482168e8751cc1a380746c128d60d1a42a320b45f168bc080000a2d87456168aa0d0edaa1b8942646848150882a0e8b41b0a8340d0584a0909411068143d0202a018b3e3827bc2cf7029eb0d3d40a79e2cf3429e40b3be2a77814ee829db873b50a75e34ea859bb69371166ce54d9429af0f3571e69c4cd2849a4053421a6820ccf4499c893341400004cc82000013310400004cc010000132b1663a70000098e0331b0400004c68100001319066300800009898a000026240cc3459840a0000260e080000983032ff1e5ea54bd01978092ef065d81cbac1974852e60e5c424b84196e0b2da0a5aa2cb5019678b2ce0400004b2c39630b2c5065880cb00495e092a26a54014a6c594b0b295065202ca2c5945032880a4e6ac9c819378726e064d8149ac193485268064c04493d19270324c0a49414924192385246064881490829208323922462448c019160922b0645214894490c1b217064203c8382906052071640c0c8141900891fd123f6147e428fa0b1f20a3e20c7c018f6091e8123cc1479028ef8a000000000477038ed051ba82370146cc58d8851ae0e3522c69c28d3031a40a3402467c18cd89197123281c64c18c885190063123c60878b5af1651a2b84c55868a71114a122920c51c28a1891420627c244f4189d851371225a544b018940800000000044943886b110a0c00004414500000000022002c3e86000010f9061ec18000087a82000021e80c3bc5000010ea161ca2c3883000010e10400004380186d8b0da061b014301885d8b0b12a15e142a858528a0000214614284284d8d0951a126142385846050890e1082c1ec982b4b055040000000008261304b0400000000081ba9032160620c0bc281588000020501c08c580f890152a01e3000000000100e060122c020180286ffb29ff40800007fc82ff5100000000007f984ff205fe013fb047f192fc771f8a13f0057df0400001f761800007db8800001f546bea027d304fa505f4223e64800000f9415f1e2bdcdc00000f72040000000007b78600001ed81bda8200000f66100000000007b2040000000003d80400000f5239ea20bd3c200000f4d09e5323c944791840000000003c80378c1000001e2823c40478704f0915e0e10000078284efa2ddf013bd8277986eee15dda080000772900000000003b8830000000001dbc20000000000edc0800000000076c0800001dac1000007690800001d9e1bb04e752b8ea309d440ba7c374a9400001d2223a3c27460600001d121ba08700000e7241c7da38e4571c02e3609c64238c4171688e2719c3a53870100000e1b05c2c28000070986e100dc1820000070582e0711c081b7f4700000dfc05bec33769c6eb08dcd25b884b6ad96d484da415b441367c36cd0a00001b301000006ca86d8835b0a1b604400000d8005aea5b5c446b802d6f05ad2335a016b10cd600800000000000000d5e09aba0800006ae02d5811aa04353c16a68400001a941800006a404d4411a4123478268d8600001a2640000068902d1009a1a1b43016840800001a0e0b418168108cfb1c000033d8500000cf5059e02b3b4300000ce910000033a0100000ce609994e32d9464e340000193218000064c02c950d926132403647040000000003230264096c7e0d8f618000063c84c7318000031c0362daac580d8a820000062904000018a20b13c2000000000000003134200000c422c00003104161c12c3704000030d8161a04c310d85e130a4600000c260d84618000061084c1f0800003074200000c1c0583413054500000c120c00003044160706bfe4000002fec35fb88000017ea12fcc25f398be3117be22f6c45ea0ebd3057a212f4015e704bc91577e52ef035db8a0000176a12ec8300000bb10575c1aeb4100000b9c4573412e34d5c602b8b057101ae1c100000b85097002800005be86b7c056f21ad9545b088b5d1000002d6c25aa0eb50116962ad2425a384b421567052c4e558788b0c0d60a3ac10158008afc115f60abdc457988aed1800002bb0100000000015d60ab98556e14ada095aa28000056a02ad30559e22b20756286ac40557e28000055e06ab90d56a200000559060000156010000055782aad0955418000000000aa90554c1aa94100000aa30954018000054f82a9c0d5168aa28154386a840d5060aa04253f06000014f8129e8253b08000014ea0a9a4c00000a670800002998100000a650400002984452a1a000014a60a948100000a510400002940152782000014962291c400000a450800002910152104a3924000028d8351a82a340546218000000000a2f094542a8a4151402a250d44808000000000a220943a2a870150d82a180d42e0a858100000000014281283c54fda89fa053ee1a7d814fa049f10d3e00800004f7829ea14000027a02000009e7053ca127844000009e0040000277434ed069d9053ac1a75414e9849d00d3866a70424dd0e9b809368226c43000009b00535a1800004d506000013520a6983000009a50533a4000004ce02000013206000004c7820000131c0800004c682000013180800004c58297f312ccca58844ad10956112a22a53c24a606000012921800004a4020000128e0a51034a00893d0d26c3a4d414988892d112580a4a43493069250524222480148f0491a10000024602000009170522a1243c64839000001202300000000008fe0d1f8123dc547a848ea2d19ce0000046586000011940a31c3462848c20d180122ec545b0a8b4091525a29c2452068992d12a20000044a02000011260a2346445848861510812204343f8487c0c000021e4343b06871150e00a1b8243682865210ba40000042d06000010b20a158300000852100000214410000085005098221282000008480800002110441b1c0000106a0800004198483108000020b440000082c05050200000413820000104a10000041202822080000208410000081d1103222038b3fb307f40800001fcc13f9027f008fcc51f9023f0867e00400001f7c13ee847d91000001f5833ea827d014f9c11f3413e4887bf28f7c09ee843db087b30c00001ec813d7087ad0400001eb013d38a7a604f4811e8043cf8200000f3c09e6453cc0279608f2421e2c73c48478804f0c11e1413c08800000efe11df423be0200000ef609de423ba887720cee209db833b68276b08ed211d9c23b10a00000ec011d7820000075c08eb41000003ac0400000eae09d5423a88874e0ce8e3800003a28474110e7c19cf020000000000e7219cc870000073104e4281c74438d847180ce2629c4033848e70708e081800003808600000e0009bf4337b0e6f50400001bd013788600000de009b94b3710600000dbc20000036e8200000db809b60436a086d304da4080000367866cd0800000000035ab06b308d6409ac02000006ad0c00001ab01354866a60c00001a884000006a10400001a80134e0869a0800001a602000006950cd0c7800003428200000d061000003410268008000019f430000067c04cf218000033c0200000cee099acc0000066a04000019a413340266608ca4a18b653160262810c4040000000000000000000187433052660904c100800003008e00000000017f44000005f910000017c092f70400000bd03179432f08800000bbc180000000005dd040000175c6000005c254000016fc3000005bc0c000016ec12dc845b804000016d822d90800000b3aa800000000059a0cb2e1800000000000000b2c0965412ca0259010000015f920000000000af6195e030000057704000015d032b80800000ada1800002ada4527d0a4c0947c728f0251c08a360946420000051804a2239420900000504100000140c100000502049fc20000027d08000009f2093d44000004f4049d4513888270824df089b620000026d024d4189964932422618c4c10897c192e06000004b50c000012c83000004af0c000012a4624a2a000009221800002480248d0c000012301000004890c00001220124286000008fe30000023f02478188ee091cc42390247008000011b430000046c048d219194400000464048a68914030000044d0c00001130122486445100000110c2221020000000001100221e08000000000109d5212844220c8420800002100241e0883a09064420c024160800001050200000413048221103440000040c040000102c11fd223f70c00000fd81000003f30c00000fc811f7863eb1000000fa811f4823e510000000000000003e20c7c208f3d21e7023ca1079208f1c21e188000007840800001e0823c00400000ef43000003bc0477218edc21db023b40876608ebc41d7023ac087502000001d3823983c72a1800001ca02000007260800001c8060000071e08e3031c40800000000000000000003764800000dd411ba023720800000dc4100000370046de08dac41b5023680800000d94300000364046c218d7440000035a0c00000d6411ab06000006aa08d18f190ca000000000000000000031e0c6169800000000030a04000000000183082ec6800000bac1173882e40c5c608b80316f82000005bc08b5c716b022d30c000000000000002ce14574a0000015b08000005681000001590400000562080000157840000000000ab03000002aa0853c60a74114d84000005321000001498c0000052210a4010000027c500000000000000027b044d680000000000000004d408000012d2023e70000008e840000000000470108dc111a0623304458388614000002160800000854110984212044201083c1106062090c410088047100021fe083ee387cc4000001f204000007c410f8021ee083d03079c10f2061e3043c2107783000001dd04000007605000001d7043a42870900e0821be0c0000000000de041b81036c106d4100000000003661000000d68c00000332a065440c90618e103122800000c3840000030c0861020c182000003021000000bf0617230000005c410000016f082da1000000b506000002d20859830b282000002c808588200000160080000057c10ae84154242a41053060a582149080000051c200000146042881000000a18213d18000004f0109d820000027210000009c02136082681000000998212340000000000000001200c0000000000000010d4c000004283000001090400000420108286000002080800000818200000204080000080820fe0c000003f41000000fc041ee283a0f000000e6081ca08000007088000001c00837c1000000000018ad03101060080000017e082ec405d0200000172082e0105b040000016a0800000598400000164082c02057820ad08152200000054020000014e080000053020a01811e8800000470208b0c00000000004484088040f080000003b82076040e6181c810380406d0c000001b010000006b040d408000003404000000ce08194203184000000c408154d00000054040000014c100000043400000010810000004104080080f820000003d04000000f0101d8200000074080e020000003704000000d810149a0164c002a80001 0x78f32403b78d301e2c0189272c384139496189c9880085c67c0e7833d1e9c19b0fc68cc85a706542f1a326069c18f03c68c6808e46280ee4042073c01e8ec080c8560404c0b0201a00f7004268fb0f1147d2786a3e63c073d32403c58c701e280989e7cc3d493861c239f24f504e12586e7c63d313831003b70d041adc67c0200314020a02103b701047e2006c3afe03217880150abf80981e2003c0afe01a022a00427b8b10d3db58829e7ec3f4f3a61ea52630e524d18708ee2943476d4a0a39fa4fd1ce927b0d34937857e499a12624b504d12586ee2643376d3209b9f98fcdce8c7add346376d7e319b34d18ad95f8c4e6498621313431003b88d0c1db46820e7e33f073a19e8f4d0cdc75f86662d3432b157e193834d0c7c15f86360498315013418a27c700dd3e3006c9f120334f8701923c700ad1e300548f1202747870131bc7007cde3003c6f1201b378700d03c7004c1e300240f1200f07870072499bd1104cd870626692c1e983210fc298f85a60c6c2f0a632069831503c298980838c403afa33e157d19902be8c98092c6280f0400e078100682d4804016a40489264f44413261c189924b00928c403f0633e178319903c18c981e0863c0f0231d1f800210ebd80f85e0006c2af6032078001502bd80980868010948cc39492d61c434a24de15e9266848c92d412d496374a18ddb5e8c66cd2862b657a31399231884c4b4c403d283371d7a1998b4a0cac55e864e0d2831f057a18d81230c5404b46289f080374f7f019a3c200ad1dfc04e6f0801f377f00d83c2004c1dfc01e3ece93c176731e18c30cf01c600603eccc4817664a403b319201c58678042a0401f7d01a0bbe80a01df40380ee4010022819e038a8cf03de40680ef2028024861c249624b104b0c4060303140136004038a0cf03dd80680eec028022819e0123bd1124a9870825492c312a31003988cf81c7c67a0e2233c013518a011501081dec0823ef40361f7801a8fbb80d07dd40642ef402a17780148bbb80a05dd404c0ef401e077800e83bb80701dd4034040e01207740088faaa4f05d54c780eaa33c020b0180faa31205d512900ea8648073019e010d81201dc80203ea6c3c175349e03a998f07d498782ea493c075231e0123bd107a0d8823ecac3e1f5a61e8fa8b0f124a58702d06941176549f0bad24f45d45278825292c068332083b298f81d68c7a0ea263c3129310011b0c501db807c0ee003d076f00883b700387d91278830c63c076a19e038800c03db12903ec693c076c3240bb198f01da46780e1e030070e01807b524f01da8c780e1a0301f606240bb025201da4c980e1803c070b01803850cf008580801ece0340767014188f00701d540201ebec3c075f49e03a900f01c240600ec893c0708018038380c01d892780e0c030070501e03afb0e124a12582eba620075d18a039780c81c780620e08030023500403818cc03d752780eba63c0702198180c00f01d99e880ecac380f634a087b0a4f83d8127a1ebc93c492749603b199041d84c7c0ec063d075e31e209398801d706280e5c032071d018838080c008d0010caea318614c49e03aca4c0cd48648cae8318614a01203800cf01d69e88924cc388579499a09324b0dd08c846a6a63e6e9131b36b998c99a44c54cae6626324431003a30d08c85c67c1eb03366d7219903ac0ca995c864c0eae314072d01f038e00f41bfc0780cb401d353200c832f004405b801a0466008318201803960cf01d54020924ac38412549603a4988008c46280ea6011075200703a68c601bf8060ccd693c075049803a60c601bf4078cbc60248578498037e00f01bec048c87a630074d312037d00c18f080310aee932074e31903a618a01be40780df033c074961c249224b10490c400e56332071b198837b8cc008c06280ea8c39075161c0fa224dd3ce5266948a92d49234960ba218dd1ce4c670d2662b8576313a1229885048cc406a42337353519987a78cac3d2c64e0e9e31f074b18d83a50c541d206280e68033072a019038d00c41bd00603cc002b1d5c0138b30007c55700366d9a0133532007811d002408bc010955693c42ab31e18c30cf0d488660030c03c05220181f940cc01ca00600e8a93c42ab31e1b948cc01d0c0780e4e030372619820c100c03d0d2780e8663c052319e1b928cc0082c0600cbef4c07467a41fa225203d112786e88648074431e1ba10cf0dc906600e84048072401803be3d141dcde880ee2c39076d61c0fb5a50c79f12823ed093f1f5b49f0fab24f47d1d2783e829374f38499a52124b524712582ed6643167c3208bb418fc5d6cc7c2eac63d174731e0ba098dd1ce0c670d2062b8571313a12118850470c400ed6343067c1a083b40cfc1d6c67c0eac33d074719e03a08cdcdce0666dd2032b6d71193b3480c7d95c46366484315311c18a039980cc1c840640e3203106f30180f2c80ac756c04e2cb201f155b00d832c804c156c01e0470009022d004039819301adc030040e010491b7a2208db0e0c46d2583aa663e155331902a99898089cc403dcc3421d0519f0b730cd854146640dcc32a050519301248c507cf807c2e7c032073e013039e00781cf40320e78012073b0089b9198f01ca46801e72c4807394a41b9118f014d46900e48340654e49e0aa70cf015386481e6ef4907376249b912531b54927ccaa493207221a60ea90cf855486640a9a32436da18e036d00a01b940380aaa018491a7a24347b10e15c187e8234c386d5a49fb6a7a4f99569266ca9e9323226496376598fdb410c7ccd9663365043191b599880756867e3a9e33e155a1998aa78cc8153064c6a98325054b1921b780c78db6063a6da231c022618a0f6580fc741007c2d960331504019036c00a81bc00520da2028365800f032c00741b900380d660081f346240b9a25201cd0c900e640101f2c61e0b9624f01cb0c781e5e93c072f31e03929900d4d8c780a44340072c61c0f93a4d47c8d262923292c172731a8b9198c50464c400a20335353619883958c501ac80101e5093012a931803930cc01ca126025526300f26498039318c014898781e5293c0f27498039498f01c9cc600e4a3300f2361e0391a4f0d4d8c780e62f44073061c0f9724f87cb527a3e5493c1f2449a8f9124c524612582e5c63e172d31e8b9518f05c90c6a2e44631411831003970cf81cb467a0e5433c072419a83910cc4c4606280d600080720008078f30f01c792780caa3280530192032b0c71245d870822e92c071b3100f2b8cd875646642cae32a15591931b670c7814c0634045831406af004038fbd107c7587c3e38c3d1f1a61e248b30e05c7527c2e3893d171a49e208b24b01c74c7c0e3863d071a31e188b1880795066c3ab033216541950aac0c98195063c0ab031a022b18a035680207c2d2602e1663031821980f8530f05c292780e1463c1f1801a0b8c00a01c600380e2e010491461c208a24b0c450c4002603141f1501a8f8a00c85c540522e28026071500e838a00681c4c0240e240111f0949820c118c01c386601e2093c1f08498038818f05c20c600e1a3300f0e498038718c07c158782e0a93c070d320078580d01c2c0500e1293007074982489a4b05c0cc400e0631406ac0040781a4c01c0cc600e14c380f0849a878324c83c152621e089304912496038418d41c18c640e0a6310704318208918801c086280d56008491161c42b7a4cd0445258dd186366d6b319334618a995acc4c64806206d6a19932b50c981c006283d9403316ca013837480741b1c0320ddc01106aa004037d8c601bf92600df431865df01242b724c01becc48c77c018856d499037e18c81be8c502d92025656600ca48824b10440c400d5231403b5006077b18c01bd8c48085400c4a41496a487a4b21a38c570ad86274241310a08798803bf46561df232706fd18f837c8c6c1be062a0dee3141eef0158f64009c5bbc03e2d9001b06f50098363803c1ae80120d50008071661c8388b0e07c3d26e3e189331f014990f7fa4c47bd1260947e92d490c4960b8798dc5c30c662e0263216ff3188b7a18c21a2cc570ad2627423f310a08618801c3c66e0e183330701199037f8cc41bd0660dd1632b6d69193b3458c7d95a4636647e315310c18a0f7400ac7b1804e2dd001f16c600d8374004c1b1801e0d7000906a5004037898f01bac6800a8a31806c100c0778a4f01bc52600a6c3240eed318037618901b000181dd863006ec31218c10c6010a80180d7e00c03b50060376a4c01bb0c600dd433006be006077518c01ba8c481ddec3c06ef49e037718f03bacc600dd662406e919e035e803019612901de493c06f2498037819201ba06980a6a324054418c035e00603b812780dc0930051f19202a18c6015080189216c38410b49602d99880c57c6280a9000e354800682a08030057c0100dae33c0540006036b0cc014fc0186cc693c06e2498036a8cf01b400480a7c00c053d18c036a18c014f06300dc0c38490a496036f98801b6c6640db233106d3198191f0c50151c01c0aae00d053b006011280201b48c780a743180edd01a036e80a0c82cc801db663006db3121a8e00603b652780db29303519012036b24c01b3c048921292c06d43101b5a8c5008900109210c384108496076b98c83b54c621da663006d7313036a98941b4cc480da462036b418a03670068d43c0326a1c018022300403678cc0d1f00181d9e63006cf3121b2d98f03b40c600da062406ce19e1a4600301b99e88920cc384106496190519081b94c7c6cc463d06e431e374498d83b8cc641dc26310ede318334498a81b8cc4c0dc262506de312036e18801b6867c0db033d06d119e191e8c50052c03a0d9a01a052000c828f0060151801c0aac00d0539006011100205528c78cace63065663120b620cc1958c648dad063206c931307628cc85b1064c0d8031c6d6631932b318983b106640d88326042a18e076530f43b218780d9493d06c849e036398f1b594c64caca6260ec319903618c981af4638cac862465633120362b0f05b112780d8863c656231232b0a4c01b0cc980d7c3340ebf19201da8c601afcc48076a3240ec0498036018c010a86601d7c32406be18c076098c01b04c480d7a3400ecb7a48365b125b58127ccac093206c63260ea498f85524c641d8433e06c2199035e0ca07ae98782d7493c06ba31e035c80f0082c0800d7064c020d024035b80603ad4c600d6a624023218c029c0c901ad06383d6493c16b231e03590cf01ac40783d5ec3c16af49e035798f01ab80781d5893006ac3182482a4b10414c400d52314013061c0f55a4c87aa92623d5093049044960b5598c85aa8c622d50630410431003558cc81aa86620d50330310418a035380c81a98062046e01c02370200124bd107acd87a9206c3816b349ea081a4b01accc7a620662006b01a103568d041a946803a6e3321537193029b8c6804dc628047203e06a401e8f5180d87a880642d4602a16a2013035180781a88034043600e06a1006839fbd141ce9e883e70c431f3661f8f9ab0f528ed8729202c3817384a18b9b24fc5cd527b0d10937855d499a11da4b504052580e70643073631f839a98f5ba20c6edaba6336688315b2ae989cc8ecc42620262007331a183908d081c646820de63401e5319b8eaa0ccc74d06642ca632b15541938a9a0c98194c63e0aa831b053418d01148c5408806283dce0371ecc01b0f5d80cc73f40642dce02b16cc0150b5d809c53f404c0dce01f06cc00f035d806c13f40340d6c00906a000403c330e41df98709e809374e9f499a502a4b523d52588e80637469f319c32918ae13f0c4e840a62140f53101ba00cdcda7c666dca432b6cfc193b3290c7d93f0636640a31530f518a03a000dc1a7c0663ca402b1cfc0138b29007c53f00360ca401304fc0078102802403d401008b800c014c31e074e98c01a74c4808b600c06834a6033c252037b52780bda930045a18c034e00a01a6c04808b23180e9949e034ca4c011606301c0e93c0607498022b8c6123d187081e892c31de31000ef0c50079c01091e6f4440f361c0721a508387d27c1c0c93d0dec49e0321a4d8187d2640c0c93105ec49802d924b0c774c40692831a049418c822b0c6007746280d300290697013034b00941a540480d1c93c067731e06f598c01874c4808aa00c068d49e00a618f037acc600294624618618c08c3006011500180d1893c066b31e06f518c0178cc4808a600c06936240345a4f01904c980d24648067631e06f498c01870c486d2234806910240229003213d98901c366480e1531e030d98c01854c4808a200c0de8318030a189011400181bd0630618218c08c10060113c0181bce63005df312022700301a398780d1a63c0de631803099890da306780d1803c044d00602c6a4f01a2926086a4624068f7a48345b13213d587c0cea6480e1e31f06f298f01868c600d1262806123120226003019ecc781c0a630014a312022580303a1d8900d0e948067a31e070218c01810c48089400c01e7020074280d01a14050623c01c011e008073fb0f019fd2780b5203c068249e033fb0e123c92580cfc62031dc18a00ee00201a11e880d06c380e414a08740a4f83a0127a1cfa93c48f0496032099041a04c7c0d0063d067d31e20781880c76c62803b60080449006073db0f019ed278089000c067a4a60701a4f0180d260088e00c044618c030a189011140180ceec3c06133121b358cf019ac078088800c84f761f070a98f819c8c680b1a6280443006033998c019cd260c304324118201202c6a4f019d12600ce463c618619208c3009011086300cf0f440e76620873ab0f523bd8700cec941067549ec27da4cd03bd2581ce26360e12319033898a81848c4c0ce0620365c1a09b2c0cf4d97863a642e31931da18a032e0104196007a0cbc01d021700c9a498038124c01a088200c01da0040700a4f01805260088031805a901224773d1103b98701c949420e2749f070124f438012780c949360627499030124c418012600b8292c066e31018ec8c50d24801c092400d043f00600ec802019a0c48087c00c05df312021e803019b18780cce624366b198033580c010f001909f4c3c043b006021d003019a12606bbe32405df012021c803213e587c0cd293e066749a021c003010dc63091dac3840ed49618ec1880d2446340922319043618c00ec0c51d2ec048092000c0e6349e0331a4c0196c6480cac018048f006250230e523b18700ca293784f8499a10224b503b12581cd46370e66319833518ac1998c4e0cca62106643101ec90cddb3786666b2432b64de1939b310c7cd96063663c631531d718a06c900dc73780660b2402b14de0138331007c1960036093200f348e0070247003410cc01803c600901d7004032e98f03770c60e974624065701e024680312d4927886a463c014c31e3e5d18c1d2e8c48630c318065601e024600310608030091600c0e5d61e032ea4f0196c6780416018048a00618c1006005200180cb663c0ddb31802ed98901954078028e00c0e6062403302520197cc980cbc648065c31e06ed18c01768c480cb4348065401e02448030195865009103180dd93183a5d9891f2ecc60e976624318218c06ec18c01760c481caec3c065749e032b18f0375cc600bae624065519e032c252037592780bac93006541a602438c601a69e8a0d28f440e90621874430fd280d87291d6c3806904a1834424fc194126f09e89334203496a075a4b01a18c860cf8642067931f833798f819b4c7a0cc263c0e4931b871e18d83898c661c226320dff31886ea98c01924c560c7862a06263138308989817fcc4a0baa62405c031082d71880d9646866ca633f3d9119bb66e8cccd644656c9ba32731e218a98eb0c5019640860ca603f0d9101b8e6e80cc164405629ba02704980079a430038121801a084e00c01e200480eb002210992600c9e63cb61019e430800f010940190ca2f4884244980328992018e8c800c9c63c0e0f31803079892d83c6790c1e03c04240064211a4c0108c0190844930064f31e04a518c00528c496294318814a00c021100301939e990842930094931800a49892c524631029201804210060328496210752600c72640064d31e070718c01838c496c1c33c860e01e020e803037f8c7802986300625312020700301921878081a00c064b6240323b0f01928c901bfa63c062431202060030102c0180c9063c094a3180311989010280180c8ef4c09493180311189010240180c93258064661e06fe18f01884c48081000c063361e032200c019092780c6cc3c48ea61c031f24b10754c4063aa31401d50040321bd1123a58700c82942064049f031fa4f418f52780c749360638499031aa4c418c92600c5c92c41d431018ea0c5007500100c76c3c063a7a6031c3d3018d98780c6af4c063361c0318a4b1074cc4063a631401d30040318b10018c98800c6092c41d231018e90c5007480100c5a040062b01a206500a0c3280380194010062d6200315b10018b9e997c5804c062c020031500d10324050619201c00c9008031e3d3123998700c729360637499031a24c418bd2600c5292c41d131018e88c500744010080e00c06274a406fda4f01891268080c00c04050060312a4f0188d260080800c04030060311b10010080180c48f4c062249802008030189a4b01bf493c062149a020000300ffc6300c3694884f349e030a992233a8c7807fc00c061431801fe803018752780c2663035e319e02f180f00ff001909d663c061b61e830b990213a8c6486a462803fb006030c18c01861260c3043301182018030ca4f10d48c780c2e630618619e08c300f213c927807f400c06144981aef8cc0177c06007f200c061561e8309a50213c526407f000c061f7a2030f30fd23958700c38942061a49f0307a4da13c1264840092c0616321030918f81830c6d09d2632060a31032c38ca5cdcc64a6b1431d616e18c98e80c50561c05286e6025058a00e88b70064d21401c090a00d03f400600e800221080c4807e600c061061e420f9890d7486600ba403003f20060307bd321078c486ba233005d101801f8803213bcc480c1ac3c434931842771892c5286610294030060c7a621a418c213b4c496292330814901801f48c601829e9807d031806117a6247230e0183926d09d893241ff496030598da13a0c640c126206584194b9b90c94d62463ac2da31931cf18a0ac200a50dc804a0b1201d116d00c9a420038121001a07ce00c01cf00401f30c6017d987807ca318060701801f20030181527807c600c03e200602fcb0f00f8401807c031848e361c0300a4b017ccc40639c3143483007024180340f7c018039c00806067a2247130e018112840c0693e060249e830024f017f526c0bf693205f849882faa4c016fd2580be462031cd18a1a410038120801a07bc00c01cd00401ee803017f987807b800c05fd7a601ed80300f680180bf6f4c03d900601ec003017e587807ae00c05f87a601eb00300f546300becc380df149602f89880c730628690200e048100681ea003007300100beac400df049602f81880c72c628690000e048000681e98030072c01007a431805f349e02f8a4c00f44630801202403d018c02f8b1000f3c6300be4f4c05f049801e70c6100200480bfef4c48e161c02fe24d817e92640bee93105f449802df24b017bcc406394314347f007023f80340f34018039400803cc18c247030e017152586392620347e18d023f0c640f2c630039231405e849801e50030179d260079200c05e649802f598f0d7a86780bd403c03c800601e380300f180180bd063035e719802f380c00f140180bccc4005e131e82e798c40f100180bc063003c300602ef98c00f080180bc893c05de3181af18cf0178c078078200c05ce49e01e000300efc018077c00c05e04981aef8cc0177c060077a00c05e161e82ef25001735264077800c05d9018023e80301760060028c00c05dc49e3a5d18f0176c6780bae030047b00602eca4c1d2ecc600bb033005d71a0023d0c6017b58720bd8c3805e949b82f2a4cd280925a91be92c05e231b82ee98cc174cc560b9862705c731082e21880d76866e6bac3333d8f195b66e0c9d0cd463ee6e631b31e118a98e40c50176806e0bac0330d8f0158e6e009dccd403e86e601b04970079a3c803811e401a076400c01e100480e40020172cc48076200c05d461e02e51890d7486600ba403003b000641d798900ebc0180ba4c4083ae31201d70030174de980b9262435d119802e880c00eb40180b9c93c03ac00601d580301739878075400c05cf61f02e6a4f81729268075200c03a800602e5a4c2cebc649075e02403a700602e53102ceb8649075c02403a400602e63d301725268074600c03a218c02e3bd300e84630074062405c561c246f24b0c71cc4068f031a047818c81cf8c60071c6280b88c4048dd49618e31880d1dc63408ee319039e18c00e30c501755880940292d48dc49602e818ac1720c4e0b8c62105c33101ec70cadb36c64e865a31f737218d98f00c54c7146281b1c02b1cdb013b996807d0dc8036092c00f3476007023b00340e6001803c000901c500401cb8c6036e40800b7203401e701400b60070c5b00200b829480dbf49e02dfa4c00e586300b7a04c0db802002dc00d005ac03862d6010039518c02de010036dc0688194028016a00e18b5004016fde980728318bdbb02602dd810036d80688192028016900e18b480400530c781b7863005bc31201c980300e480180b78c40039100602debd3036ecc600b76624039000601c7803016e4c780b6e630014a31201c700300e340180b6ec40038c00602dc3d3016d8c600292624038b00602e0496036f92780b7c930038818c5edd016016e80981b6a04005b501a00b40070c5a0020070e318038631206cf0d0016786680b66010038518c06d800d016c00500b64f4448db61c206da4b0c194c4068ea31a047518c81c20c6001946280b6204205ad02082d4010016bc07c1b4c0360da401a86ce80d0366c0640b4c02a05a401482ce80a0166c04c627a01e359500e809e8048165402207063180da301a02d180a016b5e98070431805ac02606d100d016880500b52c3848da496206d1880c19062800c800805aa62082d43101236525881b2620306318a003180201699e98070231805a302002d080d0168d8800b42c4005a47a601c00c62f6880980b4404005a001a02cf30e123612588012620306218a00310020167588091ae92c400831018308c50018401006fe318059a02002cc00d016698800b30c40059b7a601bf0c62f6640980b32040059701a00d18c601655e98034431805ae7a6246a30e1035125860c0620347218d02390c640de463000c0314bdab026ded3813016ac0820b4e0400da501b06cf80d436700681b2c03205a501502cf80a416700500b2c026313c00f1aca007404f00240b28011159061e328198c0162066028e202404700060ac93120563d8780b24648058f31e02c618d01628c602b0e62405871980a37809011bc01828dc024046b00602c830f2aa74c600b0c330146d01202350030163de99553863005851980a36009011a40180b1a93c4b4949802c63d312d21260ca0663caa9d31800a518904528630e65e024632f00602c53d32aa70c600292624114918c399700918cb801828d0024014800602c418f01618c60c664624146701200a380305198048128c00c05866200a32809025140180b0ef4c0585318319898905190048028800c059192c0ac730f01638c780b1663405893180ac21890161066028c6024046300603293d3127f1872918ec38064c49bc273a4cd07f125a818e92c0e4531b871418d83880c661c106320dee31886e118c01914c560c5062a06203138304189817b8c4a0b8462405b431082c99880f60c66ed9b43333583195b26d0c9cc77c62a63703140d8301b8e6d00cc160c05629b402704950079a2e8038117401a06f000c01df00480dc0020116c6386aa69480553324022d18a014ac6980a0a348358101402c0807016000200afe00c045831424633d110319870799e93e34cf49918d824b0333cc7c099e6323494315024a18a41158c5003606200b541a105578cf80d5066c055e332028518a1abe80a415f403a0af8011057b00682b7a521b338c78d99a6301cce19e0e668cc015b92600ada93c057831802b624f0d5dcc640aee332045518e00a40cc015d4648028c318056b49e1e6718c873346640ae831c035200802b524f0f334c64199a332045318e02bcb12415d98900ad293c35733241e6618c815cc6901998332045218e01a8813015c809109cac486cc8324326418c073206902990330045118e02b718c0d5b4c646ad0626056d19902b40c9811406386ace626356631302b30c9811386380adec3d056c61e1ab598f0f32cc646aca626056b19e06658cc8159464c089a31c056a01e02b21890158cc480ad0c3c056731e02b1189015980780ac8930056301802b1250015958980ac2624355119832610c6015440602984018050349e02afa4c10aacc486aa033c64ba19232608c601540078297402414c100c02b83d2415a589909c8c3e35523251aad1924d53cc90799463e64c9319326c18c59300c606ac062664b931202a90d2815686920a9e3480cca19f0a648cc85360662298033005601930a5c8c9011306380a120490504024017e80c50ab40600abc02802a501202ac8cf012346381ab8c48055c4a41a9919201560678091231c64c649e0a6b98f035658780ab293c053031e1aa418f0355cc600aae624014718e06ad3d2415698926a989483cc949f1a64a4c81560c9819ac63e04d6319024398a015586500a3004c052000802aa8030150cc500a3e31c054e3241a6398c1930c6300aa293012a9312325d8c91931063009ccc3e3cc831f1a6318c8d364c62698a63064be312095700c015400501a9cc3d054e49e82a10c7014700386a380103cd749f1a6ba4c815206380a1e01c35190082462b0e013d926e09ca93340c54961ea518cdb2f8c646a9462764be3131a9c18803528666397c332054a1938a5f0c98d22063c091031d054118e029c0c502bf0066155c03202fc01381570098d4d803c0a6001d050e00e029b0048d4c00226a1c010028400402a525201520c781a8e6300547312024418f03514c600a8a6240d3d318029e989123112588188620038718a00e00020d240c600a7e624053d4962461988014f06280506008054361c246124b10308c400a84332348f19882a08cc0350064c1a7c3250d3b19202a00c6814f86320a76318053a18a0141002008c86380a7063c050c1a0029b18f014886800aa6f440d5261f86a7b0f523058700aa493f054f49e827aa4dc1391266818292c054d31f02a618f4152cc7879b06333cc03191a6c189cd300c4c635e6200d491998e5c8cc8152464e2972326054618f02a20c7414e46380a6e314051b02102978104142c08015f60330aad019017d809c0ab404c0a6a0120532008828f00400a040106a6263c053119e02190c7014200786a6063c348c18e0698b0f014c52780a6063c0d336240299a520d4c8c906a5e63c05321a402978cf010b86380a0e03c351731e028b8cf034b40680a5a0280d2761e0293a4f0d47cc780a3e33c3516198028b00c014a92786a4833c3515198029200f014540606a2833c051401e1a8998c0144c6600a4ec3848c049602931880d4746646a34331351219818d70c5014740640a34031051201800d70020d4446602552030018219818c100c06aa526025526303182198069224f01490c780a4633c3510198029100c0d43cc780a3ec3848bf496205f9880d4706646a32331350e19818d68c5004ac0101a3a93c051d31e028e0cf034698780a3493c051931e01058d0014592600a2233048be49602899880c6b06280a1a0080d11498028898c122f5258817a620311518a0119002034352600a1a6300232198028bb0e034552641a289310d12498245e24b01454c640a286310512318205e188014406640a1e331050e19818d58c5014300100a58f44052b61c05a8a50434a527c1a5093d0d2549e245d24b00d44c820a5263e052831e829298f102e8c406414341352119f1a900cf4d4786786a3633235181989a858cc0c6a86280414041052101f029000f414780780a360320518018828580c006a8010085a62802fa19e02158c7034218780a1093c042918e0684bd241425892797e93e34bf499065f98f812fcc64085062805071a6057c8cf80be4664697c63004be198028000d0140c0506660318033000c028098c0d2f4630097a01805014981a5d8c9012ec0480a0693c0502498028018f0d2e8648697831804ba012025e00601415e881a08c3d48b961c028224f502e5258797263234b931318d4988032e4664097232601a918a067f80d82a9406409fe02a02a5013027f002015f9e8a0af4f440d7162186aeb0fd27ed8729170c3805714a182aea4fc13d126e09c693341fb496a05c24b0d56cc866aa863f353431f1e6e98dcf354c66797063234dd3159a6a989cd2e0c4c636e62131a731002ad8d0c155067e0a6833e0cdd19b866a8ccc32e066409ba32b04d5193825c0c98126063e690c31e048618e82138c7006dc62a034e314052e02182850108141807e09fa03e0b7601b85a600d82be00661548032037601581a600a80be004e0548026028e004813f0022106926069ee64834f131e027b8d2013c467908329308418498027d18f2105d26069f263e04f919f02130c70d3c8c79083893034f231e02790cf013ac07809eef48841b498027b1920d3ccc7809e233c04ea01e027dbd2813e1e91082c93034f53251a7818f013d469409e033c042418e01a5010013a407809e433c04f231e41f824c013ccc7c09e233e04ee18e01a4804013bc660128c324014618c027731002514648028a31804f07a641f7a4c013b4638069001004eb31e41f724c0d3a8c7c09d433e041f18e0274bd320fa9260083c31c04f492c4207a4c0d3b0c7809d833c041d18e01a3810013a00790838c400ce67a402733122106d88009ca6486cb531e325a98c23391e9509c8c4a84166201a721929b2dcc7d596e63d6cb431e325b98ca92dcc62c968630b2f7313495198901390694396e33e5cb719e8e5a0cf052dc664a96e33114b4198417b8c988a8c648082c31c0af701ea55180f00bdc062854603004e1014014a8091b2bc660c95e3181caf0180a5780601389278953a930429d31236570cc24a74648c95c3181cae018114e809052b803009c2f4c4a9c498214e1891b2a8661253832464aa18c0e5500c08a70048295401804e392c4207b101b2d8c7d596c63d6ca931e325b18ca92d8c62c952630b2f63134950189072d867cb96c33d1ca919e0a5b0cc952d8662295233082f619311500c90103c63815ec03d4aa001e017b00c50a8006009c002802920120a310c9011c463809bcc4804dc61e19b998c0518464808de31c146019202368c701371e9828be324046c18e026ec960136d87866e4630145e19202318c70136589009ae64814d7624026ba520d2a126029b0c4a54b761f026c2528f2dd27c694e93004d6325026a18f85184c6808c26281321194019080d00cb002009a400c54a661e1e5324f0d29926009a925854a561e1e52a4f0d29526009a4f4c04d592c2a5b30f8f2d927c694893004d331f0a2f18d01178c502638328031c01a0195804013440180946930131b314018d8cd00ca8638c94462404a23120265b0f05339290099c64804a13120a668d201334090094062404cb7a60a64252152d527809906483cb531e024f98905319890095093004c418e0a6200a0130c648098662404c431809980cc0130864808f831804c861e8263a4f8131927a098a93c14b5499324e989052f8678098231c049e498019800a012ec020066063004bd312223e0c6012ecc60e8f831804be49e024e989012f0050097401004cf7a20266310c132987e916ec3814c949f8a6024f852dd266296893241a6496026498fc1300c7c096e63304b43190a539898129cc4a093862431a63100a5f8cfc52e467c45ea33322a319909930c784dc063a262c31c127d18a025f80fc12e407c15ea0330aa3019019300a80dc0052062c028137300901b980440ca402004fa00814b361e025324c012de4b02964c3c04a54981e5ab0f812d527c796693204b34988258a4c24a88c48554433004ae18e0259bd3012b0638295802804b162002558c7052ac050095a62404ac31202578cc0aa64649253231804ad192025624d012b988009566242a98192494c0c6012d1e98796493204b2498825824c24a84c48554233004aa18e025424f81299264c63c31c030400e198f00401299e98094ef4c04a5499318e8c700c0c038663a010130231401810ca0cc08638094093064a231e0a510cf012880780940c40447c00e3a3e0040128d8700942937049f499a45b24b19278c66c93a63292f4313c951189989f0c40293c333149d199117a0c9c8a8864cc6da31e136d18e89808c7049f0628093c033049d019057a009c2a8804ce6da01e036d00e818080710db402466da0113301008013e00201271880916a92c92f3313c950989989ecc4045e632722a119331b60c784db063a260031c127b18a0579809c2a8404ce6d801e036c00e818000710db002466d80113300008013d802012e1e989168c3814b64998a54a4c90695258096c63304a93190a5218981290c4a093662431a531011790ccc8a80664264631e136b18e897f8c7049d462815e40330aa0019019180a80dac05205fe028137200901b900440ca002004ea00804994a4064ba4f0125d260092ef4c049892c064b24f0125926018fc93c047e49802450d001220678091831c0c8349e0241a4c03240c60092062448b361c2059a4b01244c4018e03360c6219902380ca8118864c091e31e048818d00db0c5009d001009163300c7d192023e0c60052066018f8324047c18c0645a4c0122cc60191a93c048d31e02460cf0122866018f6324047b18c024418f031e8c6008f462404947a2245930e102c9258092663e049231e824718f03214c6419046310c79318024298981208c4a08f2624047531002448d08121c67c18de3360c6119902378ca8118464c036a314027300402338ca04db4648c65e31c04857a602320ca04db0648c65c31c048349e0240a4c012058800904f4c0480498023e98c011f066008fcc3848b1496023c188011ec66c08f43320c6a19506300c998c2063c26da31a01b418a0139002011e188008f2c4048b0496023b988031a465418be326630518f09b60c6806cc62804e20080474008023a310011d5e9808e6010046b19831980c9011a063008dc93063301920238a4f011b526008e033c046a19831978c90119c63008dc3309a9919202330c6011b58813530324046518c0235a4c26a6464808d4c409a98192023418c01198c4808cc93404676200232989011bde9808d8930046919831970c90119063008c463c046031809b69890118188008c2f4c045f31809b618901219e98915ec3840af496064218c831fcc6218ec6300484313023f989411d8c4808e46200c6319b062f0cc8118c65408bc32601b218a01370020052066018b8324045c18c022318f02f30c600798624045b00e062c98c01164c4817cc63003e6312245730e102b925817fe6320be531885e598c00ffcc4c07ca62503cb31201c3188009b462808b001d045700d022818c01114660179432403fd18c022798c005206601794324014618c022718c010f4660179232403c218c022aa4f01134c6008a833c044419805e40c900ff063008a603c041c49e05e38c900fe8630178e3240bc619201df0c601141260089e3300bc519201fc8c60113806008a2c3d044d4a0020da4c8110c67817fc3320bc419801fd8c900fe0630085a03d02f101282248cc02f90648028c3180c4b49e022598f0112066017c632403e318c0624a4c01124c6008906400be231801f118900fe8630088a93003f918c021e80c00bc004a088cc380c4449a8621a4c522b525808886350443318820d189d02b4c4017f032603f818d02210c5010bc06a08580310aef0138177806c10c402204d80080be031801f0189122b1870815892c0c0d31b060398c82f84c6217be630040d315020398980f84c4a07be624039731002200c5009ac010087431803be18c021f24c010e4630087a0240419498021d18900ef80300830932043b319021c98a00bb804a07ec01948ab4962055988009a8628076a0180c35318021a989010a801893f492d48aa496021298ac105cc4e83f462140aa310061e0cac30e064e087831f043818d821b8c5410d862816d202b0aed01381b4807c0bb40360868013042c0078146802409a401008603300bbb19201dd0c6010ac06002903300bba19201dd0c6010a806018609300430318061924f010c8c78086233c042f19805dc8c900ee463008520300bb831e01fb98c00fd8c4805d83300bf631901fb18982bac66405d6326042a18e05db0c900ed4630176a32403b518c0615a4c010acc6008543300bb419201da0c6030b587a085a93d042c31e05fa98c82eccc6007ea62603b331202148d002ba866405d4326045a61c822b30e0314926e189893349f9496a454a4b01148c6e08986330424315820b189d07e4c428152620044a19b82238ccc1104664087e331043319806060cac301864e17e83260bde19285d90c90103063e080c31b03f418d01ef0c640ec8630072c315038418a021700dc10a006616d002b0ae901381b4007c0ba403605180090268004420a9890108c66017e632403f318c020a9890108c6600840030042661e020a1890109467808443300bf219201f90c60107c0600826624041231202118cc02518648028c3180422620020898902514648028a31883ed31241f618901080660175e32403af18c020fb1020facc48175c32403ae18c02123d301040c4808423300bf119201f88c6010780600838c3c0419318020aa4d0306066208303250ae801881740094306d87c083693e041449a020d0cf8105c67817e033003f019201f70c602b9c06205ce025041319241f680921055260082a330041219201f60c620fb00480826324041249a020a3100104464807d631883eb012020b3d30104126817de33003ef19201f50c602b9806205cc0250bdd19800a40c9010146300816930040e49e020524c0103467817b8330040418c02058cc025186480806318040a62004a28c9010086300818f4c040949805ed8cc01004630080e63c0bda318020218a01014c600806624040349a020231001008c48080cf4c0bd9318020098a00fe864807fa63003f919201e100c00fdc06207f462403be01201fc98d00fd806205b401902d919201fba4f00fd8c7805b032403ff61c01ff24cd22a125807f863603fb31901f918a80fc0c4c83ec62003f819901f70c980fa462807ea0330ae501381ad80740b5c03206c0011026700401f68c600fcd26007d831803af01201f931000fac630075c0240ae401281f831002b8c04a07d86280ad6012816b00640fb4c48074c01803ec49a01d280600fb988007d66280ad5012816a80640fa588007e8c4048a749601f898a80fbcc4c83ea62003ea19301f40c502b8804e06b001d02d400c81ae8044099801007aa93003e601201f218c00f61260914c92c03e031001e90c50099401007cac3848a549601f198d80f88c6407c263103df31801ee18a80f68c4c07ae62503d431201ca98800f4462804c800803dd49801ee31000f6988007b093003d762001eaa4b02f40c4007a0314026300401ea24d02f3cc40079e314026200401e918c00f40c4807a093403d162001e798900f79880914892c03db31501ec98980f58c4a07a6624039431001e70c500984010914692c03a031001300c500f1cc48078c62403c531201e50cc00f24060078e32403c601201e2a4d00f00662075832503b8018857080940efc648077c32403c331801de8c900f08060075663003bf31201df00900f01262077a63403aa31301db80c40b68032076c02403b501201dd98c00ee866007680240ae0198016c8c900ed8c48076a32403b849881db98c40ed066815be32602d818d01e624b40f2d258079062b03c4313a4fc18852288c40078232b03bc19381d80c7c0ea46360744315039f18a01dc80ac0ecc04e16c601f0ade00d81ce004c0b5c01e0516009025f00401d40c600ec5260074e31803af01201d30c600ebd268074a31803b062001d20c600eb8048075663003ab49801d624c80ea8c64074e6280add012816b00640ea0c48074c01803a631401d3a4d00e940300752c4003a4314056e00940b540320744c4003a0496245098800978628073e93448a0310012e8c500adc018073a630039b312015b00300ad4018073693402b400601ce31000e68c48056600c03b249a24fb9885227cc40075a31f03a318d81d08c540e7862816c401f0adb00d81cc804c0b5001e0514009025c00405c780d00e3c050072e63c0b9531801ca98900e4c080171c034038e01401c500400e48068171a02803956205dc881000e440681718028014819805c90c900e486300724934039362005c88c900e44630071e330038d19200a30c600e35268071cc40038c19200a28c600e29880072cf4c0b9431801ca1892ee4009807200400b8b01a01c580a00e24020070e010038661c244f24b10278c40007e314038301a81c280c82e0405216fe026038100e81bf80680df402406f6011038362001c0b1000dfd88006fac40037b62001c23101226d2588136620003e18a5dc101040e0806a17000290b7e01301c000740df803406f8012037a0088213b10127d125a912a92c041d3158207989d07d0c42812a6200c0819586000c9c2f9c64c179a3250b9819202040c7c100063607ce31a03cd18c81cc0c600e2062a06f23140b570158569809c0d5c03e05a601b0287004812b8020cdc4c4806e2324036a18e016200900ddd89006eac3c337331819b818900dcc66006e0324036818e01618090cdbcc4806de324036618e016100900dd5e9866dc624036e19201b28c700b0404866da624132f18e01b9bd30cdb0c48265c31c037149e01b7a4c00db4c4806dec40036d62001b83d300db926006d8624036419801b08c900d706300580018036749801b08c900afc03006d493c036649801b48cf00d8c66006c0324035b18c015f00600af403006ce330035f19201ad0c600af003006ccc40035e19201ac8c600aec0300574018036449801af8c900ae403006c6c40035e192015c00600adc03006c2330035f19200a30c600ad8030056a018035f49a015a00600d8188006bc324014518c015980600d70c6006b4624035a49a01adb1000d64c4806d0f4c036549801b10cc00d7464806b031802b200c01bb49600dd187866e4630336b31201b90cc00dac64806ae31c02b101201a0b0f0cca8c606636624032a198018d8c900d5406006a693c335219e01a900f0cc686300634018034461e199b0cc0cc64630066c030031900c198c18900c606489128c38034e49620f99880cc9c6346644319331718c18d00c500c9c0340644019031700c00d000200d51e889126c3803514a101a824f80d3d27a069a93c034a49b01a324c80d0d2620680930033c49620f91881852c652666a326332c19299948c90cc986346642319331618c18cf8c50452c052066a026032c012819480900c980340642019031600c00cf80200d2d8786692330034901801a4b1000d29e9866903300348018198a8c600c54030068cf4c331418c018a0060cc4c6300626018034461e199a0cc0cc486300668030031200c01a1bd30cccc6606622318033301801888060cc40c480620324034161c019fa4b107c4c40664a31a332018c99878c60c678628064a01a032000c818780600678010661c624030e192019fb100cc34c48061a3240340620019f24b107c0c40664831a331f18c99860c60c674628064801a031f00c8186006006740106616624030b192019d81000ce40680676c400339620019e3d30cc28c480614324bb3a026019d01000ce00686612318033000c019b24f00cd12600664324330818c01978060cc1c6303532018033462019830c606a60030c28c318114600c019931018514630228a01803303180d4c98904518630065ec401a9831208a28c600cd5e980666930033119219828c600cb80306608624032c7a619819890cc08c480654c38489249638ae98810c78634663c319330118c30ae8c5003580100652c40489149638ae18810c74634663a319330018c30ae0c500354010064e93c0325498398f0c900c95880064cf4c0324498398e8c900c892780640930031e31208a38ca00c81880063cc4003217a6018fa4c00c74c4822883280310498018118900c4d26006123244890496018c1880c67062824f4008031b61c2447a4b00c68c6406326310317318018a98980c48c4a061e624030b31001840c680c106320602318319b18a093c80200c5588006269300307192018931000c18648062092c030e31018cd0c5049e0010061c934030f49a01869880c66462824ee008030b620018498c00c1cc48060e9340308620018318900c11880060492c488e310184e8c5046f80100602934488d310184e0c5046f4010062cc40488c496018a18980c44c4a0618624030a31001828c680c0c6320600318319818a093b00200d31e989112c38034749b01a2a4c80d09262067a930033749620f79881850c652665a326332b19299940c90cc8c634663831932ff18c18cb8c50450c052065a026032b012819400900c8c034063801902ff00c00cb80200bc4c5005f434802fc4a4017618a00be989005d462802fd625017bb0f8cbed29465ea93e02fb325017a98f80ba4c5005f234a02d219f01618cd00b9cc5005a233c02f792c017318a00b4067805e893c02f47a6017ac9600bcd27805e063c02e1318016d18900bb067805e093c02da31201758cf00b6464805d093202ee31281678cc80afc65005d631a02e0318016c98900b64c4805d893c02eb31e016f98c00b60c4805e293e02e7499017798f80bb4c7805ca63202de318016b98900ba867c059c33202be19401668cc00ba0c7805c863002d631201660cc00b9de9805c663002d531201658cc00b9126005ac6240aca198017231000b95e9805c693002d531205638cc00b8066005c093002e1499016e98940b7c66405723280aca18d01648c900b75880059032402de620016e18940ae0650158e31a02d9198016c98c00b68c6405ac62602d819901650c980ad8638059232402d662001640c900b5d88005aa62602c719301598c700ba5e9805cc93202e2319016d98c00b50c48058c33202b21940168b0f00b38c50059862802d17a6016598a00b35260059893002cf31e056518c00b28c48059a63002c9312016631000b20c48059262402c949a016531000b20c48059cf4c02cb498056398c00b1cc4805a525802d061e016318a00b00638058893c02c2498015f0c700af06380584c4002bb18e015d0c900adc630057a62402b718c016018c00af0c48057e33002b9192015b0c600af4648056a31802bc49a015a0c600ae8c48056a31802b949a015a0c600adc648056a31802b5314015b24d00ad0630057cc4002bb312015c0c900acc6300586f4c02c149801590c700be24b005ecc3e32f249f017918f80b4cc50058a33e02b119a01548070caa4020255c93c02ae31e015401000aac020855463032aa198015500c10aa4c60655233002aa498095498c00aa4660055893c42ab31e215418c0caac678655033002ab01e015400c00a98068055ef44488861c2156a4f90a8d264832c92c32ad31f195198c8c658c40055a33e02a319900cb0c500a9c084054a03e029e01b014a80c80a44010254493002a2318014d00d00a74020053201c3299008015131000a60038653001002a37a60950a4c00a84c60052e034029c008214d9890ca6c6480536024029f61e214e98c10a68c48653a330329a192014e80c00a6804885326243299192014eb1010a60c486530324029b498094c98900a646480532934029a620094c18900a60648053cf4c429c318214b9890ca70660652e324029c018014b80900a500800528c4002957a65d4981300a4c0800522f4c02a47a62443b0e10a81264832a92c32a031918ca98800a80664032a314029601b014900c80a400100518628015201218a900600a34c781516630028b312014480600a2d8800512c40028c7a6054518c00a28c480510018028e92c014398a0054404862a2018026d31400e00c7007006601506324028318c014218f00a08638050af44488661c204324b0ca04c7c74fa632327d313183398800a0467c14fa332027d19319398c7809cc63a04d031c006718a0140010809fc07c14ac0360a54019012b00a8095004c62ee01a325200c80bb8038094801a04f8624027918e00df0c7009f1880037a31c027a198013c0c9006f863004f09340279620013b8c9006f463004faf4c027b312013b0c7009d0c7814e463002723120138006009c988004e0c4002737a6053898c009c4c4804de0180a60318013018902994c6004ca62448854962042988009a862804dac3848844962042188009b066404d6331026919805338c98299064a14be324026718d01320c64097c630007e314025b007012c8034099d88004ca63002633120131a4d0099188004c4624026049624419880097862804bc934025f49a24411880097462804b6c40025962001343101220525881026200a6619305308c94297064804cc31a026118c812e0c6000f862804b400e0258006812b3d300951e98037e01c02527a600de007009f9e989100c3840804961d3a98c8c9d4c4c60cc6200a75199013a8c98c9b863c04dc31d025718e00330c50295406c14a6032025501501298098c5d803464a201901760070128803413f1e9893d8c39487d61c0273a4dc137d26683d892d407d4961e6d18dcf340c66793463234da3159a68189cd268c4c63626213192310066d0cdc3340666193433204da19582680c9c126864c092a31f345d18f022e8c740de06380362315019218a05ab00dc2bf806c15600330a8f01901ab00ac0bf80540560027028f013014300240940010046e340022819e248f00d10478050623c01c0236326011399200868698041c34800f700e008000600938020049a00c1a48020092400d0092005090f8f44407c61c183e24b06774c84336063e11dd31b08d818c80774c54036062619881a10cac8cf8462066c22b2332018819500ac8c98092c03a04940190249008812380340904c78048063c0a456240122a52008fcc7803b634c02441a400c28130090c0901482c3c024149e01200cf0060408002be63c0a3e318011f189006b4630047e94c02261a400d78c9008f46380352318021802600c000a008f003802ac018022c19e010b010068e98902474948023a32401158cf008e4090042a0401a32498091918c008c86603462c3c123149e011898f008dc020146a93c023531e010480f008c80200462c38487b496203d988008c0628043c0350209019009abd1008d987033b69411a3449f0d19a4f468bd27890f292c11db320891a18f848ccc7a245e63c407931000ed8d0408d067c046633d022f19e183c8c50082007c045c03d021d01a810400c868b1878245893c022c31e0115993008340900454010022800601118ca0057c63804483300a2431801121890057cc78144a630022531201118cf0089de88344cc3d487861c091324f501e1258044c63d30783100d110cd866a4664244432a11a919301110c7806a4634026e3140214021010900f4656006422b0026015800d010a00480884022343c93c121e31e010f0cf0087c690043a340021101e00c09900082c68063040301a1649e090b18f008586780416030021b7a2010d30e06615282343293d1a18498a43ba4b04614c82243263d1218318a03b98800614682043233d0218198983b8c50085007c042e03d021501a810a00c866b5278235a63c01ad19e010919200844698042001c020b00e24c124c10608c606304330498649e20c318f0c61867804160301a0949e090498f00824678041cf44487661c203b24b0c1d8c400410342020d19e8cd40cc846a064c035031a1a0c01b0cab00c8483005422ac026020c00f00ab006808280240410011020700401263d140919e883484c431a3b61f8cf5b0e521d58702484943123b49f9101a4dc87ed26623d692d40754960121190c08ecc7e140663709fb319810198ac07ecc4e03d66213075310011c0d0c08b4684045233f022019f0cf10cdc675866c336e33319a719908f10cac4758654236e32711a719300f10c7c075863c036e31b01a718d010e010c084c084041e03f020601f0cc880dc65fc06c32c8033195501908c880ac45fc05422c8027115501300c8807c05fc03c02c801b015500d00fd189008118900404c3c01f931200ea0cd0080066002fa03401fe01800fc18900809e9803ee62401f631201003d3007d4c4803fcf4c020392c0100b0f007d0c4803a233401ff19800bd00d007f406003f293411a619800d30c9007c8638032c318117501a00ba80a007b8038029c01801fa49e00fc24c007d864802e602801f862000fb310007e5e9803ee93001f519200b800a007ccc7803e2630015d31208ae8c6007c588003e4f4c01f031800ae1890457063003dcf4c01fb92c00fa24d04694660034a32401ef18e00ca8c6045bc06802de02801ed00e00a68060070cc500348624300419418130c900010038004c01801ea00800f4003006fc63803d4f4c01bc18e00d18c60079c080919403440ca01400f3b10007a1e980344318b9e602600f301012324068819202801eb92c00dd98a00684c486006328302519200018070009403003d201001e500600db0c6005b003803c694809e149e00f0a4c006d463062ee024016b00e00da0c6005a803803c2f4c01b318c00b48070078a4b013c093c01e049800d90c60c5d804802d001c09c949e00e4a4c0077804813b893c01dc31e000c00f02739278039c9300142012243a30e101d125803b062001c418a00c70044050801c03baf44487361c2039a4b0076cc8403b463e01d931e80eb98f02750c6c13a063209cd31884e418c00750c5403a062601cd31280e418900194c400386314014100d00dd00640634022028200e01d549e00e9a4c0002404803a6c4001d47a600e924c0002004803a0f4c01ce49e00e624c005000480398c4001cd7a600e5a4c004fc0480392c38487249600e3988007086280318011014000700e3b100072188090e292c01c631000e08c50062c022027e00e01c000800e218f02708c60038462401bf00800df00400709880037a01001c019804df0c9006f8630037c93401bf62004de8c9006f46300386f4c09c131800e0989006f00200374f4c01d67a6243730e101b925813a263609cf31904e518c42714c6003a262a01cf31300e518940714c4800c062001bb18a009f006806e40320314011013e00700da98a00548048627a01001b631e04da18c006d0c480368c4001b57a604d998c006ccc48036f25801b231400a88090c4f0020035634001ad18e00d60cc026b1260035863009ae49e00d718f006b4678035633001b07a22436b0e101b5258035e63e09a631900d318980690c40035434201a919f04cf8cd82658664033e32a019619300338c5006a007c32a8032115401300b38078058c03202ce012019400880cd8ca04574638034cf4c019819408ae0c70068c0180346c4001a47a600d100300670630034093c019e49808ae8c90066c6300334318019e62000cc8c600670c600334624019a49a00cdb1000664c48033ef4c019d49808ae0c900660630032cf4c01947a600d3bd3121b187080d892c09a531900d298980684c40132e336099519900cb8ca8065464c00cc314195301908a98098059803c02c4019016600900c980440640648031a31c016100c00c83d300638c781318630018c31200c631000635e981316630018b31200c8c960063c648031431c016000c00c18cc00608660130e93c018731e00c08cc006180781306930018331800c100c00604c800310f44486b61c2035a4b00614c84030863e097d31b04bc98c805f4c5402f2626017731000c00cf825d466402ea326300418a00b3806805b803202d6011016700700ba0c6005f927802f8930017318c30a5009005c863002f8c40017118c00bebd3005ed26002e0318614901200bcbd3005dde9802e6628017431800b91891851803002e4934017362000b89891851403002eaf4c017031400a38c7005b9e98028831c014800600b618f025a8c6002d4624014700600a3003005a9880028a00c016b7a604b498c005a4c48028800c01677a600bfbd3121a987080d492c097a31b04bc18c805e8c5402f0626017631004b78cc805bc64c6006314016600d00b6806405a002202cc00e016331200b08ca0057803802c6f4c01617a600af98f02574c6002ba624015d62000af3d302570c6002b8624016492c00b11890058065002b601c01597a22434b0e101a5258604c620015819f04aa0cc8055064c028231e015218c80ab8108055807c12a0036094e01900a800a8053804c02960120141008809e80200551e98028e01c01527a600a200700541e98029cf4c014800600a618f02528c600294624014700600a300300529880028a00c014819804a30c900518630028c934014762004a28c9005146300296f4c094931800a498900510018028463c094031800a0189005018800282f4c093f318009f989004f5e9802aaf4c486861c203424b0c094c4012a63320153193009f0c780544632129e036094d01900a780a8053404c0286012013e008809e00200815e9833c8c39485f61c10fe24dc87b126623c892d405f49604fe18dc27b0c6603f862b01ec31380f21884c17cc4033be33719b819b0cd88ccc664866423be32b11b819508d88c9c464864c03be31f01b818f00d88c6c06486343312037196501b0cad00cc64ec064231202b116501508ad009c44ec04c031201f016500f00ad006c04ec034326c0341136014009b007064a58823236c3d185e61c0894a504446d27a20bc92c0129320808d98f40178c4001fe34100fb19e8c9c80d864e0064227202a1138013009c807804e0034026e01201350070098003004c0638325e040112f01a009780a061f187230bac3820f349b906324cc41f125a20ba92c08f331b846318cc03ccc56018c627007c310802e988060dc66e30343331037195880d0c9c00dc63e003431b193301b8c9900cc44cc0562264027013300f8099006c04c4026025c00f0115198008a18f024b00680258028012b0080492b0f00495278023e33c0113198009424f00448660024403c011119e008818c0049587030b892c0124310008c8cc8045c662021e330007b18a00870cc02489278024463c010d198008fb0e1216d25880b6620007a18a008f002004a9e880252c3808f04a08493a4f8249927a124693c185a49600781904049cc7c024c63d012331e082d18800460664022c331010c198003c8c5000d4082024203e012001e808e80f00314c602210628010819a00858ca02465278023263c091761e008ba4f004540200226930010e0180c2ca4b00440c40020a314090e498008718c00451870122493209114988487a4c0616125802246320111318808798c04160c400208314003201a808680c80310630021263000c318c0084a4c042f4648021693c010a498008418f002fc648018431801070120482a4c00414c600208640011b7a2048d30f4615d870023493d1057496008c19080458c82021864008c13190060989801e0c40120c33608b919900830ca802e464c020631400fd020801880740408022002c00d003232000803d1003fd870306a94118fe49e8c7ea4c52159258206a64110fe31e887e98c50158c40006a34100fe19e807e8cc4c15862801f403200f9018800c006003ede8890aac384055496182a988003e868401f23411819199080c8c98006463431f00361816019087c00a8405804c01f001e001600d007b802004d1872025ac38191c49b8c80a4cc61d525a30a892c111c31b888098cc83acc5641706271075310882a1880047066e020233308eb195845c0c9c03ac63e017031b007518a802a0c5003f006e01ec03318300158c0a809c40c003e202a01b0030009800a803c0381878015c62400cc198007a00c003c927801e203c00ad18c0071b0f002b063001a603000ab3120c29b0e003b525820e862010b318d00598c6402a863000e831400f37a20c2930e003c128401de93e00ee49e807624f003a526c01ca93200e2498806fa4c0036d25820e662010b218d00590c6402a463000e6314002c01480690098033804a019602400ea61e007400c003a188001d2f4c00e701800540c600395e98014e31800a618c0071b0f0029463001a203000e27a600520c600340060014662400e061c006f24b041c8c40216231a00b118c80510c6001c8628014262400de62000501890037d88001ba92c107131008580c6802c0632013e318007118a004f1890036808001b003400d6008006d31000361880013a31800d6620004e0c60036de980136624b8d9026006c8100035c06801aa010009a18c0069a4f003452600132318009818c0068b100025c63001a4f4c00d0498004b0c600339e980198c3848514960838188001c0628019400800ca6200065b101214125820de620006f18a0064802003ade98309ec3800e649b007224c8038526201b893000d44960837188042bc634015e319009518c00370c5000a4052019e02600cd0128064009002b9268018862800bd194085e8c700310c60018662400c549e006118a002f0680017e31c10be318005f0cc042f4c60017c93000bd318006024f042fcc78217863000bf19e005e0cc002ec078018cf44184e61c0860a4f842dd26420da92c00c131f005b98c842c8c54016462900a93140036988002e8684017233e009319b00440cc802186282048029002400e803f8044001801a016c930088f31400478cd00248638111c628008e19408470c7002d9880111a628008d19408468c7002dde98016a930088c31400460cd00244638016693c00b14980058b10002c9e98016093000a3498005324c00268048309a92c00ab31000428c5002b9870309892c00ad319005618c402a8c60015062600a5312805118900278c400108314002200e804c806802a1880014c93000980120052b100025c048014692c00a131000418c500285268014493400a031000410c500274020013a934009e620004e00400268c600130624009849a004cb100025cc480152c40184b496005398980290c4a013e624009b31000408c50007c03a012c01a109031200480c9002518782124630108f31200490cc0023c6480116030108e312004931004234c480120930008e312004724d0023d880011a624008b6200049bd304244c602118624009119800460c9002280600110f4c0084314004298c0020cc4801069340084620004118900219e980102628007f7a6005c3d3061298702168932106c496005a18c842bcc54015e629009531400361880022466c010e332008018a080f00a4007803a00fc0110005006843da4f001ecc7800f433c007c7a20c24b0e0412525800f2642007831f043998d821b4c6400e662a006d313000e8c74004863200ee042007601f043580d821a406400d602a006901300338048019401c00e893c007249800380c9001c988000e0c4000737a60038a4c001bc64800daf4c006b7a60034bd30019de9800c8040086201a003100a0019188000c4c4000657a65c318130018c08010c20340061014003abd306121870209092c086e31b043618c801b8c5400d8626001c18e80088c6421a806c10d0032006a01500340098019802400c000e084761c0023a4b00164c6000b893c0058318182d8cf0016c07800b293000584a0002f30e4017587010b493708574998424a4b4211925800b46370057319802918ac0138c4e00926210046310182b0cdcc154666305e32b181419388178c7c405063600ac0370055019b41780ada05004ec05e01f601400d8021004c010001e009a624005361e00261890c14466000a2030005162000293d30012cc4860a03300050018002624d001352600098c40004e7a60025a4d00125e98008ec3800454960022b1000119880008892c003f00600213d3000f8018007e31c003d020041d80d000ec050007ec40003d620001db1000101e98007c31cb83c026001e010020e806800740280054620042424b4210d258009e62b004a31380241884010cc40305c32b181319388170c7c404c636d05c02b6813013b017007d804c0360082013003900780198cc020d9278006c63c00321980419a4c000ccc60006464000377a20417b0e000bd258006a642003431f041618d820a0c64005862a00283130013188000c467c10483320024193000e8c50003801c001800d002f7a600118c6000b52780056930002218c00108c6000ad8800040318002c7a6001524c0007c6300050f4c00267a6001118a0008cc600042624002149a001131000080c480048f4c001f314000ebd3000c1e98105cc38002e496041498d8209cc64005262a0027313001298802078664003c326001c18a00068038002c01a0030010001801e000d3d102051870002892c0012310000c8cf820406640020326000e18f00060c74005c084002c03e080a01b040300c80028054000c0260004004000a3d300049e98001201000107a6000400400039e980018f4c00090120004b1000029e98001002400067a600023d300055e981026c38001349600089880203c664001e326000d18f00058c74201c06c100a032000701500028098000c01001eac40185f4968c1c24b0831cc5640fa627105f310881c1880231c65610fa32700c718f803e8c6c017c62a0070314181b0158c01009c406c03e200401b001b0098001003c1a79880927492d480149642c118ae093cc4e8274621400131036c10cada93c64ecb0431f624f18d989d0c54c0046283b0402b1a4f0138ac1007c493c0360b04013024f007809d00240004010000003f 19 6 13 11 5 6
def s2Data : Forest := fun i => decodeNode 11 24 0x32478f009f8718d78d00978718e78a02678a007f8700f78800778761ce9f313785009f7f19378018f78018ef80015780007f7f61c69f00e77d7a2f41020f7400f77401477900ef7400e77401477600d774008f747a274100877261cf4101ef6e008f6e00776e61c74132476c1a1f4131e76a32676919ff410147677a275c61c75c49e764320f5c49e76231f75c31ef5c61c75f31e75c31e75d18a75c19f7417a275749875919575718a75719ef4100875561cf48008f5200775261c74849875018ff4831974c31274d31474c18df4818af4861c74918a74819e7417a474249e74531e74231e74302474219bf4101be9f7a2ea001373b00cf3b00973b008f3b7a26a04a4739321ea0624f3731fea031eea03247341a1ea00087327a272261c72231e72f19f72219ef2261c72b18a72b19e72231e72549872831872531872619872519af2249e723198f221a16a00087207a271a49e71e31f71a31ef1a31071b31e71a1a0ea000e71700871761cef400ef1200d712009712008f1261c6f431e71019bef431870e32070d199ef401470b61c70249870931af02498707319702318f0231870231870318a7021996f418a700198ef44986fe18fef53196fa3126fb3146fa18def518aef518a6f53126f6009ef51986f41a06a04986e84986f13246e849e6e931e6e94986ec3186ec3126e93126ea19e6e91a66e800fea07a26cd31f6cd31e6cd3136cd4986e2312ecd61c6df3106df3126cd0146dd3106cd3126db19f6cd4986d919eecd3136d24986d6312ed23106d43126d23106d219e6cd3126ce3126cf19e6ce00d6cd00f6a0624ebc49eec73136c949e6c731e6c73266bc61e6c431e6c43266c31996bc3126bd3186be3126bf18c6be1a06bd1946bc00dea031e6b901e6b93266b700c6b7004ea03126b518e6b431eea119e6b101e6b11a16a131e6ae01e6ae1a0ea13186ac1996a6198ea618a6a91986a60196a6018ea61a06a101eea100f6a100d6a1006ea10046a0019e9f62000131269d01469b01269b7a2e53498699014e95013695012e950126957a26536246913246910246914a1e537a4e8961e68c31e68c01e68c62668949868a31468949fe534a4687321e530146857a267d61c67d49e68231f67d31ee7d61c67e31067e31e67d32165349e67b4a667a31fe537a267061e6774a0e7049ee7049867249867331e67231567031067031f65331066e31ee5361e66b01866b315e6249f66749866849a667313e62310e6231066249866300fe6231e6534a465a32665a32465a49e65d31e65a31e65b1a465a021e534a465449e65531e65519e6551a665401fe537a658332465192c64d31e64f7a664e31e64d49bd8362464a32464a92c64631e6487a664761e646315d830186447a263d49e6424a163d49f63d49ee3d49663e49e63d7a662961e63b7a663a49b6297a663849962961e6367a6635498e2961c6336206306206314966304986297a662a62062d02062a62062b01a62a4966293155834a462792c62149e6257a662262062349862249a621313d837a261261fe1249e61d4a161261ee1b49f61249e61749861831861732161261ee134986144a061331f6127a660961e6107a660f49b60961e60d7a660c31b6097a660a3106093135830186077a260049e6054a160049f60049ee0049660149e6007a65ef61e5fe7a65fd49b5ef7a65fb4995ef61e5f97a65f8498def61c5f66205f54985ef49e5f37a65f06205f14985f03105ef312d8361cdd661c5d631e5ea01e5ea49bdd63185e70185e76205e6499dd649e5e301e5e331bdd661edde4985df0185df4a05de319dd649e5db19e5db01bdd64985d81985d81a05d7019dd66205c361e5d47a65d16205d20185d1315dc361f5cd61e5ce49f5cd7a65c94985cb6205ca49a5c9313dc37a65c7310dc361c5c56205c43105c33125834a45c192c5b57a65bf4985b57a65bb6205bc3125bb0265b531e5b97a65b66205b73185b601a5b5310d830085b37a25af0215af0145b001f5af7a65947a65ac0265ac020d94620da861c5a96205a80205947a65a60155947a65a06205a30205a06205a101a5a0014d9461c59e62059d0145947a659762059a02059762059801a5970135947a6595008d9431058332459292c58461e5907a658f31e58449e58d7a658c31a5847a658a31858431e5887a6585620586318585198584015d8300980100e57f00857f00657f7a2cfd00ed7b008d7b006d7b7a24fd624d7231857819957762457219257518e5741a45720245724a1cfd7a4d5e61ed6a31856e19956d61e56a19e56a01e56a62655e61e56631e56601e5666265614985630185634a056231256119355e49855f01455e49fcfd4a455c1a1cfd624d5549e55932655531255719455500655519fcfd7a253549fd3549855101455049ed3549ed4e31f53531ed3531e5354a454a193d3531e54731254718f53531254518ed3561c53a19953a19853a18d53a31253f18cd3a49653c18a53c18c53a18a53a18e53531e53818a53531e53600953519f4fd4a452f1a452f49e53031e53019e52f021cfd01452d7a250b61c50b49e52a31f50b31ed0b61c52631052631e50b31e52219e52201852201f50b01ed0b61c51f01e50b31e51c19e51c01950b49e51931e519018d0b61c50c49851631950c318d0c31051331850c31851119950c198d0c19850c31850d00450c01850b0214fd624d0749e5081a650701fcfd7a24fe49ecfe49e50049850049850131e5000154fe0044fe01f4fd7a62507a54f531e4fa19f4f97a44f57a44f63244f61a54f592c4e831f4f131e4f219f4f17a64ed1984ef6204ee18e4ed19e4e831e4eb19f4ea7a64e901e4e849ba506244e53244e51a54e492c4e049e4e27a64e10144e0499a506244de92c4db7a64dc61e4db195a506244d94a54d64a44d73254d692c4d192c4d431f4d17a64d20064d1193a507a24b93244cd0244cd621cb97a64cb61fcb931fcb961ecc149f4c149ecc149e4c13184c23124c31924c218e4c131f4b901fcb949e4ba3124bd0144ba3184bb0084ba01f4b97a649b92c4b7319c9b49f4b57a64aa7a64b3498caa6204b14984aa1984af6204ab1924ad49a4ac3124ab18e4aa31949b49f4a87a64a57a64a64994a5312c9b61c49d01e4a249bc9d6204a0499c9d019c9d01949d62049c31249b1932504a449992c4967a649749849618fa507a248731f48731ec8731048f31249018f48f31e48731e48a19e48a31848b19848a1a148731e48819f4877a645e7a648531345e49e4837a6480620481498480312c5e61c47a31847c19847c19b47a19947a62047762047831047731245e7a647362047400847331045e49e47019e4707a646419846e62046d49846449846b62046a19846431846862046549a46631246518c46419545e31e4627a645f62046031845f19345e18ea5018c45c00e45b61cc2831245900ec5700d45761c42849e45319e45301e45331bc2861ec4d49844e19844e01844e4a044d319c2831e44b19bc28318449320448199c2861c44249844531ac42318c4218a44219942818a440198c2849843d01243d18fc3431943931243a31443918dc3418ac3418a434312435009c3419842831e42f19e42f31843019842f01bc2849ec2931e42931842a19842a1a0429019c2862037961e42519e4257a641e19842362042219841e19842062041f01841e315b7961e41c49f41719f417318419192c1819e4177a641019841562041119241349a41219241149a410313b7949e40d19e40d7a640919840b62040a49840918fb7931e4077a640131840562040249a40331240231440118db7961c3f5499bf53183fd31b3f53193f53123fa31a3f91993f549e3f631e3f6019bf56203e84983f36203f23153e86203f03133e86203eb3123ed49a3ec3143eb1933e86203e918a3e818d3790123e661c3df3183e431b3df3193df318bdf3103e03183df6203ce4983dd6203dc3153ce6203da3133ce4983d86203d7312bce4963d549a3d43123ce3183d26203cf49a3d03123cf18a3ce18cb79496bb34963b31983c90183c9315bb31923c60123c649a3c5313bb33183c20183c2195bb3498bbd3123be0123be31a3bd193bb33183ba1983ba015bb3498bb4318bb43123b51923b519a3b4013bb349a3994983b16203ae49a3af0123ae18fb994993aa4983ab3193aa6203a43123a849a3a53143a600c3a53143a418db996203a218ab994963a049a39f18a39931839d62039a49a39b31239a009b9918c37931e3977a638962039531238962039149a39218c39102038919838f62038c49a38d19238c01438962038a00838918ab7900838761c38501938562037a62038301ab7a62038100eb7a62037f00d37a62037d00937a62037b008b7a18a37918e25062437792c3577a637561e3577a637319835749e3717a636c62036f49836c62036d31236c19235749e36919e3697a635819836762036649835849836462036319835819836162035e49a35f19235e19235831835c62035949a35a31235918c35818e357015a500183557a234d49e35201e3524a134d49f34d49eb4d49634e49e34d7a62ff61e34b7a634862034901834849b2ff7a63464992ff61e3447a6343498aff61c34162033e62033f49633e4982ff7a633862033b02033862033901a3384962ff49e3367a632e62033449832e62033219232e31833062032f00c32e0132ff7a632c012aff61c32a6203290122ff49e3277a632462032549832400d2ff49e3227a631d62032049831d62031e31231d00caff61c317319317318b17310318318317620300620315313300498313620312312b0049631049a30d49a30e31030d31230062030b31030031830962030649a30731230618d30062030418cb0049630249a30118c30000c2ff0152506252f94a42fc3252f96242fa1a52f992c2b192c2f761f2b192c2f37a62f449e2f331f2b149f2ea49e2f031f2ea312aee31e2ea49e2eb31e2eb19f2ea7a62d431e2e87a62e74992d47a62e36202e44982e33192d44992df4982e01992df6202dc6202dd312adc3182d43192d83182d91992d86202d56202d63132d53122d43142b192c2c67a62d161e2c631e2cf7a62c73182cd6202cc4982c76202c849a2c93122c83122c73142c619f2b149e2c47a62b26202c24982b23182bf1982bf6202b31922bd49a2bc3122b33122ba49a2b91922b31922b749a2b43142b518c2b418c2b318e2b219a2b1013a507a22a531e2ae19f2a549e2a801e2a84982a91982a90182a80212a501a2a601f2a57a62907a62a16202a23182a119929061e29f7a629762029d01829749829b62029849a29919229801229701b2907a62936202940202930192907a629100429001325092c28731e28d7a628862028b31228862028900c288314287004a507a227f31e28218c28318e28219f27f02127f01f27f7a62517a627662027c31227619827a62027749a27819227718e27619325131e2747a626f62027231226f62027000c26f18ea5161c269199269198a6918a26a19826962025862026718d25831826562026249a26331226218ca5849626049a25d49a25e18a25d18c25862025b007258620259006a5818e2517a62560152517a62540132517a6252006a5100425000780100824d00624d7a2a0600ea4700ca47008a47014248006a477a22064a42431a4243024243321a0649e24019e2404a623c31223e18e23c00e23c31fa063242390242391a1a0600823761c22e31e23519f22e19ea2e00823261c23018a23019e22e01ea2e1a120631e22c32622a00822a19fa060062287a222131ea2131222331222419e22318f221008a2119f2061a421d19e21e1a021d021a067a221461c21419ea14198a1401ea1419e21601aa140192140212063242101a621000e21001fa067a220719ea0700f20701820b00920719e209008a0700420701f2067a613b62420492c1fd7a620261e1fd7a62001981fd7a61fe0181fd31593b92c1ed49e1fa7a61f56201f84981f56201f61921f549a1ed31e1f37a61f06201f13181f018e1ed7a61ee00e1ed31393b92c1e57a61ea0081e57a61e66201e70201e60061e531093b4a41e392c1e07a61e14981e018f93b0121de7a21d731e1dc3211d731f1d731e9d73101d831e1d77a61b949e1d57a61d26201d34981d23151b97a61d03131b949e1ce7a61cb6201cc4981cb3129b961c1c96201c66201c73101c63121b931e1c47a61bc6201c23121bc1981c06201bd49a1be18c1bd0081bc18a1b97a61ba00c9b918f13b92c1b231e1b67a61b36201b43121b33141b218d93b7a21a831f1a831e1ab19e1ab3181ac1981ab1a11a819f1a801f1a87a61937a61a63131937a61a26201a30061a231019349e1a07a619862019e49819831819c62019949a19a31219918c1981951937a61961931937a619400899318d13b92c18a7a619019218a31e18e7a618b62018c31218b18e18a00f93b7a218031e18601e18632118031f18031818201818232018119f1807a616649e17e7a617b62017c49817b3151667a61793131667a61773101667a617031817462017149a1723121713141701931667a616e00c96631e16c7a616962016a3121690089667a616700716600f13b92c15b7a616331215b7a616119415b31e15f7a615c62015d31215c00e15b00d93b7a215619f15602115601f1567a613c7a615419313c7a615218c93c7a615001513c7a614e01313c31e14c7a614462014a31214419814862014549a14618c14500614400913c31e1427a613f62014031213f00893c7a613d00413c00d13b00480100f13500d13500913500e13600713561c8f600f92e00d92e00992e18e12f01412f00792e61c0f601412b00812b7a211d61c11d49e12831f11d31e91d61c12431012431e11d31e12201f11d01e91d61c11e00411e01e11d19b8f67a210249e90231e11932110249e11732090200811561c10d49811331910d31890d31011031810d31810e01910d32010249e10749810749810931e10701210719510231810532010418a1020089021998f67a20fd61c0fd19e8fd1988fd01b8f67a20f71a10f71a08f700f0f70040f70198f66200020180f47a20ec49e0f101e0f14a10ec49f0ec49e8ec4960ed49e0ec7a60c861e0ea7a60e76200e80180e749b0c87a60e54990c861e0e37a60e24988c861c0e06200dd6200de4960dd4980c87a60d56200da0200d56200d801a0d56200d60080d54960c849e0d37a60d06200d14980d00130c87a60ce0128c861c0cc6200c96200ca0040c90120c818f8027a20b949e0c23180c33120c33140c231f0b949e0bb19e0bb4980bd3180bd1980bb01e0bb1a10b919f0b97a607e7a60b56200b64980b531907e49e0b37a60b06200b14980b031487e61c0aa3190aa3188aa3100ab3180aa6200966200a83130964980a66200a53128964960a349a0a049a0a13100a031209662009c49a09d00809c31009631809a62009749a09831209700d09631407e61e0947a608a62009219808a49809062008d49a08e31208d19208a62008b01808a19b07e7a608819907e7a608131808562008249a08331208231408118a07e7a607f00887e18d8027a207631e07a19e07a32107631f07602107601f0767a606049e0747a606f62007249806f62007019206f3150607a606d3130607a606b0150607a60690130607a60670090607a606162006402006162006201406100706018a80261c85561c05549e05b01e05b31b8554980594a005831985501b85501985562003961e0537a60506200510180503158397a604b49804d62004c49a04b3138397a604931083961c0476200446200454960443100397a60420098397a603a62003f18e03a62003d02003a62003b01403a00783918a0027a203131e03632103131f03131803332003219f0317a601c7a602f49601c49e02d7a602a62002b49802a31501c7a602831301c7a602631001c7a601f31802362002049a02131202031401f19301c7a601d18a01c0098027a201619f01601e01802101601f0167a60037a60144960037a60123100037a60101930037a600e18f0037a600c18e8037a60086200090120080150037a60060130037a600400400300780200400101f800 i
def s2Tags := dagTraceTags s2Mask 66 (dagTagBases s2StockWords 0xffffffffffc000003fffffc0000ffffc0ffffe0fffe3fff8fffff07fff07ffc1ffff83fff83ffe0ffffe1fffc1fff07ffff 0xe77bdef7bdb18c6839def7b18c6f7bda0fef7b1bdee2f7b8fa7738f5ad056b417d53256bd83bf60ef4ca263181b5b06d6cb 66) 10 s2Data
def s2States := dagTrace s2Mask s2StockWords 10 s2Data
def s2Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s2Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s2Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)
def s2Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)
def s2Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 3, 1, 2, 4, 5] 0 i.val)
def s2Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 3, 1, 4, 5] 0 i.val)
def s2Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 3, 1, 4, 5] 0 i.val)
def s2Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 3, 1, 2, 4, 5] 0 i.val)
def s2Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 3, 2, 1, 4, 5] 0 i.val)
def s2Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 3, 2, 1, 4, 5] 0 i.val)
def s2Move5Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s2Move5Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s2Move6Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val)
def s2Move6Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val)
def s2Move7Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 0, 1, 3, 4, 5] 0 i.val)
def s2Move7Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 2, 0, 3, 4, 5] 0 i.val)
def s2Move8Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 0, 1, 2, 4, 5] 0 i.val)
def s2Move8Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 2, 3, 0, 4, 5] 0 i.val)
def s2Move9Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 0, 3, 1, 4, 5] 0 i.val)
def s2Move9Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 3, 0, 2, 4, 5] 0 i.val)
def s2Move10Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 0, 2, 1, 4, 5] 0 i.val)
def s2Move10Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 3, 2, 0, 4, 5] 0 i.val)
def s2Move11Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 2, 0, 3, 4, 5] 0 i.val)
def s2Move11Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 0, 1, 3, 4, 5] 0 i.val)
def s2Move12Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 3, 0, 2, 4, 5] 0 i.val)
def s2Move12Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 0, 3, 1, 4, 5] 0 i.val)
def s2Move13Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s2Move13Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s2Move14Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 0, 2, 4, 5] 0 i.val)
def s2Move14Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 3, 0, 4, 5] 0 i.val)
def s2Move15Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 3, 0, 1, 4, 5] 0 i.val)
def s2Move15Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 3, 0, 1, 4, 5] 0 i.val)
def s2Move16Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 2, 0, 1, 4, 5] 0 i.val)
def s2Move16Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 3, 1, 0, 4, 5] 0 i.val)
def s2Move17Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 2, 3, 0, 4, 5] 0 i.val)
def s2Move17Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 0, 1, 2, 4, 5] 0 i.val)
def s2Move18Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 3, 2, 0, 4, 5] 0 i.val)
def s2Move18Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 0, 2, 1, 4, 5] 0 i.val)
def s2Move19Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 3, 0, 4, 5] 0 i.val)
def s2Move19Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 0, 2, 4, 5] 0 i.val)
def s2Move20Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 2, 0, 4, 5] 0 i.val)
def s2Move20Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 2, 0, 4, 5] 0 i.val)
def s2Move21Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 3, 1, 0, 4, 5] 0 i.val)
def s2Move21Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 2, 0, 1, 4, 5] 0 i.val)
def s2Move22Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)
def s2Move22Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)
def s2MoveCert : List (DagMoveRecord 64) := [((moveSchedule moveStages [1]), s2Move0Map, s2Move0Inverse), ((moveSchedule moveStages [3]), s2Move1Map, s2Move1Inverse), ((moveSchedule moveStages [4, 1]), s2Move2Map, s2Move2Inverse), ((moveSchedule moveStages [3, 1]), s2Move3Map, s2Move3Inverse), ((moveSchedule moveStages [4]), s2Move4Map, s2Move4Inverse), ((moveSchedule moveStages [6]), s2Move5Map, s2Move5Inverse), ((moveSchedule moveStages [6, 1]), s2Move6Map, s2Move6Inverse), ((moveSchedule moveStages [7, 3]), s2Move7Map, s2Move7Inverse), ((moveSchedule moveStages [8, 4, 1]), s2Move8Map, s2Move8Inverse), ((moveSchedule moveStages [7, 3, 1]), s2Move9Map, s2Move9Inverse), ((moveSchedule moveStages [8, 4]), s2Move10Map, s2Move10Inverse), ((moveSchedule moveStages [6, 3]), s2Move11Map, s2Move11Inverse), ((moveSchedule moveStages [6, 4, 1]), s2Move12Map, s2Move12Inverse), ((moveSchedule moveStages [7]), s2Move13Map, s2Move13Inverse), ((moveSchedule moveStages [8, 1]), s2Move14Map, s2Move14Inverse), ((moveSchedule moveStages [7, 4]), s2Move15Map, s2Move15Inverse), ((moveSchedule moveStages [8, 3, 1]), s2Move16Map, s2Move16Inverse), ((moveSchedule moveStages [6, 3, 1]), s2Move17Map, s2Move17Inverse), ((moveSchedule moveStages [6, 4]), s2Move18Map, s2Move18Inverse), ((moveSchedule moveStages [7, 1]), s2Move19Map, s2Move19Inverse), ((moveSchedule moveStages [8]), s2Move20Map, s2Move20Inverse), ((moveSchedule moveStages [7, 4, 1]), s2Move21Map, s2Move21Inverse), ((moveSchedule moveStages [10]), s2Move22Map, s2Move22Inverse)]
def s2Moves := dagMoves s2MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Autos : DagMovesOK s2Mask s2Goal 64 s2Moves := dagMovesOfCheck (by decide +kernel)
def s2Check := dagCheckNode s2Mask s2Goal s2Chart (dagKnownCloses s2Goal s2Cuts) 1936 s2States s2Moves s2Links s2Sample s2Tags
def s2RootAt (token : Nat) : Bool :=
  let s := rootState s2StockWords 10 token
  !dagAllowedRoot s2Witnesses s.2.1 || dagLocal s2Mask s2Goal s2Chart (dagKnownCloses s2Goal s2Cuts) s ||
  dagRef 1936 s2States s2Moves s2Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2RootBlock0 : treeBlock 0 64 s2RootAt = true := by decide +kernel
theorem s2Roots : dagCheckRoots s2Mask s2Goal s2Chart (dagKnownCloses s2Goal s2Cuts) s2Witnesses (dagRef 1936 s2States s2Moves s2Links 0) s2StockWords 10 = true := s2RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block0 : treeBlock 0 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block16 : treeBlock 16 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block32 : treeBlock 32 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block48 : treeBlock 48 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block64 : treeBlock 64 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block80 : treeBlock 80 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block96 : treeBlock 96 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block112 : treeBlock 112 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block128 : treeBlock 128 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block144 : treeBlock 144 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block160 : treeBlock 160 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block176 : treeBlock 176 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block192 : treeBlock 192 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block208 : treeBlock 208 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block224 : treeBlock 224 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block240 : treeBlock 240 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block256 : treeBlock 256 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block272 : treeBlock 272 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block288 : treeBlock 288 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block304 : treeBlock 304 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block320 : treeBlock 320 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block336 : treeBlock 336 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block352 : treeBlock 352 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block368 : treeBlock 368 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block384 : treeBlock 384 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block400 : treeBlock 400 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block416 : treeBlock 416 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block432 : treeBlock 432 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block448 : treeBlock 448 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block464 : treeBlock 464 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block480 : treeBlock 480 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block496 : treeBlock 496 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block512 : treeBlock 512 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block528 : treeBlock 528 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block544 : treeBlock 544 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block560 : treeBlock 560 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block576 : treeBlock 576 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block592 : treeBlock 592 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block608 : treeBlock 608 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block624 : treeBlock 624 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block640 : treeBlock 640 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block656 : treeBlock 656 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block672 : treeBlock 672 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block688 : treeBlock 688 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block704 : treeBlock 704 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block720 : treeBlock 720 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block736 : treeBlock 736 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block752 : treeBlock 752 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block768 : treeBlock 768 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block784 : treeBlock 784 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block800 : treeBlock 800 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block816 : treeBlock 816 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block832 : treeBlock 832 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block848 : treeBlock 848 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block864 : treeBlock 864 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block880 : treeBlock 880 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block896 : treeBlock 896 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block912 : treeBlock 912 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block928 : treeBlock 928 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block944 : treeBlock 944 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block960 : treeBlock 960 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block976 : treeBlock 976 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block992 : treeBlock 992 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1008 : treeBlock 1008 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1024 : treeBlock 1024 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1040 : treeBlock 1040 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1056 : treeBlock 1056 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1072 : treeBlock 1072 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1088 : treeBlock 1088 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1104 : treeBlock 1104 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1120 : treeBlock 1120 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1136 : treeBlock 1136 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1152 : treeBlock 1152 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1168 : treeBlock 1168 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1184 : treeBlock 1184 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1200 : treeBlock 1200 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1216 : treeBlock 1216 12 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1228 : treeBlock 1228 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1244 : treeBlock 1244 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1260 : treeBlock 1260 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1276 : treeBlock 1276 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1292 : treeBlock 1292 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1308 : treeBlock 1308 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1324 : treeBlock 1324 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1340 : treeBlock 1340 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1356 : treeBlock 1356 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1372 : treeBlock 1372 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1388 : treeBlock 1388 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1404 : treeBlock 1404 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1420 : treeBlock 1420 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1436 : treeBlock 1436 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1452 : treeBlock 1452 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1468 : treeBlock 1468 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1484 : treeBlock 1484 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1500 : treeBlock 1500 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1516 : treeBlock 1516 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1532 : treeBlock 1532 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1548 : treeBlock 1548 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1564 : treeBlock 1564 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1580 : treeBlock 1580 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1596 : treeBlock 1596 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1612 : treeBlock 1612 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1628 : treeBlock 1628 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1644 : treeBlock 1644 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1660 : treeBlock 1660 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1676 : treeBlock 1676 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1692 : treeBlock 1692 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1708 : treeBlock 1708 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1724 : treeBlock 1724 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1740 : treeBlock 1740 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1756 : treeBlock 1756 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1772 : treeBlock 1772 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1788 : treeBlock 1788 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1804 : treeBlock 1804 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1820 : treeBlock 1820 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1836 : treeBlock 1836 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1852 : treeBlock 1852 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1868 : treeBlock 1868 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1884 : treeBlock 1884 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1900 : treeBlock 1900 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1916 : treeBlock 1916 16 s2Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block1932 : treeBlock 1932 4 s2Check = true := by decide +kernel
theorem s2Verified : treeBlock 0 1936 s2Check = true := (@treeBlock_merge 0 976 960 s2Check (@treeBlock_merge 0 480 496 s2Check (@treeBlock_merge 0 240 240 s2Check (@treeBlock_merge 0 112 128 s2Check (@treeBlock_merge 0 48 64 s2Check (@treeBlock_merge 0 16 32 s2Check s2Block0 (@treeBlock_merge 16 16 16 s2Check s2Block16 s2Block32)) (@treeBlock_merge 48 32 32 s2Check (@treeBlock_merge 48 16 16 s2Check s2Block48 s2Block64) (@treeBlock_merge 80 16 16 s2Check s2Block80 s2Block96))) (@treeBlock_merge 112 64 64 s2Check (@treeBlock_merge 112 32 32 s2Check (@treeBlock_merge 112 16 16 s2Check s2Block112 s2Block128) (@treeBlock_merge 144 16 16 s2Check s2Block144 s2Block160)) (@treeBlock_merge 176 32 32 s2Check (@treeBlock_merge 176 16 16 s2Check s2Block176 s2Block192) (@treeBlock_merge 208 16 16 s2Check s2Block208 s2Block224)))) (@treeBlock_merge 240 112 128 s2Check (@treeBlock_merge 240 48 64 s2Check (@treeBlock_merge 240 16 32 s2Check s2Block240 (@treeBlock_merge 256 16 16 s2Check s2Block256 s2Block272)) (@treeBlock_merge 288 32 32 s2Check (@treeBlock_merge 288 16 16 s2Check s2Block288 s2Block304) (@treeBlock_merge 320 16 16 s2Check s2Block320 s2Block336))) (@treeBlock_merge 352 64 64 s2Check (@treeBlock_merge 352 32 32 s2Check (@treeBlock_merge 352 16 16 s2Check s2Block352 s2Block368) (@treeBlock_merge 384 16 16 s2Check s2Block384 s2Block400)) (@treeBlock_merge 416 32 32 s2Check (@treeBlock_merge 416 16 16 s2Check s2Block416 s2Block432) (@treeBlock_merge 448 16 16 s2Check s2Block448 s2Block464))))) (@treeBlock_merge 480 240 256 s2Check (@treeBlock_merge 480 112 128 s2Check (@treeBlock_merge 480 48 64 s2Check (@treeBlock_merge 480 16 32 s2Check s2Block480 (@treeBlock_merge 496 16 16 s2Check s2Block496 s2Block512)) (@treeBlock_merge 528 32 32 s2Check (@treeBlock_merge 528 16 16 s2Check s2Block528 s2Block544) (@treeBlock_merge 560 16 16 s2Check s2Block560 s2Block576))) (@treeBlock_merge 592 64 64 s2Check (@treeBlock_merge 592 32 32 s2Check (@treeBlock_merge 592 16 16 s2Check s2Block592 s2Block608) (@treeBlock_merge 624 16 16 s2Check s2Block624 s2Block640)) (@treeBlock_merge 656 32 32 s2Check (@treeBlock_merge 656 16 16 s2Check s2Block656 s2Block672) (@treeBlock_merge 688 16 16 s2Check s2Block688 s2Block704)))) (@treeBlock_merge 720 128 128 s2Check (@treeBlock_merge 720 64 64 s2Check (@treeBlock_merge 720 32 32 s2Check (@treeBlock_merge 720 16 16 s2Check s2Block720 s2Block736) (@treeBlock_merge 752 16 16 s2Check s2Block752 s2Block768)) (@treeBlock_merge 784 32 32 s2Check (@treeBlock_merge 784 16 16 s2Check s2Block784 s2Block800) (@treeBlock_merge 816 16 16 s2Check s2Block816 s2Block832))) (@treeBlock_merge 848 64 64 s2Check (@treeBlock_merge 848 32 32 s2Check (@treeBlock_merge 848 16 16 s2Check s2Block848 s2Block864) (@treeBlock_merge 880 16 16 s2Check s2Block880 s2Block896)) (@treeBlock_merge 912 32 32 s2Check (@treeBlock_merge 912 16 16 s2Check s2Block912 s2Block928) (@treeBlock_merge 944 16 16 s2Check s2Block944 s2Block960)))))) (@treeBlock_merge 976 476 484 s2Check (@treeBlock_merge 976 240 236 s2Check (@treeBlock_merge 976 112 128 s2Check (@treeBlock_merge 976 48 64 s2Check (@treeBlock_merge 976 16 32 s2Check s2Block976 (@treeBlock_merge 992 16 16 s2Check s2Block992 s2Block1008)) (@treeBlock_merge 1024 32 32 s2Check (@treeBlock_merge 1024 16 16 s2Check s2Block1024 s2Block1040) (@treeBlock_merge 1056 16 16 s2Check s2Block1056 s2Block1072))) (@treeBlock_merge 1088 64 64 s2Check (@treeBlock_merge 1088 32 32 s2Check (@treeBlock_merge 1088 16 16 s2Check s2Block1088 s2Block1104) (@treeBlock_merge 1120 16 16 s2Check s2Block1120 s2Block1136)) (@treeBlock_merge 1152 32 32 s2Check (@treeBlock_merge 1152 16 16 s2Check s2Block1152 s2Block1168) (@treeBlock_merge 1184 16 16 s2Check s2Block1184 s2Block1200)))) (@treeBlock_merge 1216 108 128 s2Check (@treeBlock_merge 1216 44 64 s2Check (@treeBlock_merge 1216 12 32 s2Check s2Block1216 (@treeBlock_merge 1228 16 16 s2Check s2Block1228 s2Block1244)) (@treeBlock_merge 1260 32 32 s2Check (@treeBlock_merge 1260 16 16 s2Check s2Block1260 s2Block1276) (@treeBlock_merge 1292 16 16 s2Check s2Block1292 s2Block1308))) (@treeBlock_merge 1324 64 64 s2Check (@treeBlock_merge 1324 32 32 s2Check (@treeBlock_merge 1324 16 16 s2Check s2Block1324 s2Block1340) (@treeBlock_merge 1356 16 16 s2Check s2Block1356 s2Block1372)) (@treeBlock_merge 1388 32 32 s2Check (@treeBlock_merge 1388 16 16 s2Check s2Block1388 s2Block1404) (@treeBlock_merge 1420 16 16 s2Check s2Block1420 s2Block1436))))) (@treeBlock_merge 1452 240 244 s2Check (@treeBlock_merge 1452 112 128 s2Check (@treeBlock_merge 1452 48 64 s2Check (@treeBlock_merge 1452 16 32 s2Check s2Block1452 (@treeBlock_merge 1468 16 16 s2Check s2Block1468 s2Block1484)) (@treeBlock_merge 1500 32 32 s2Check (@treeBlock_merge 1500 16 16 s2Check s2Block1500 s2Block1516) (@treeBlock_merge 1532 16 16 s2Check s2Block1532 s2Block1548))) (@treeBlock_merge 1564 64 64 s2Check (@treeBlock_merge 1564 32 32 s2Check (@treeBlock_merge 1564 16 16 s2Check s2Block1564 s2Block1580) (@treeBlock_merge 1596 16 16 s2Check s2Block1596 s2Block1612)) (@treeBlock_merge 1628 32 32 s2Check (@treeBlock_merge 1628 16 16 s2Check s2Block1628 s2Block1644) (@treeBlock_merge 1660 16 16 s2Check s2Block1660 s2Block1676)))) (@treeBlock_merge 1692 128 116 s2Check (@treeBlock_merge 1692 64 64 s2Check (@treeBlock_merge 1692 32 32 s2Check (@treeBlock_merge 1692 16 16 s2Check s2Block1692 s2Block1708) (@treeBlock_merge 1724 16 16 s2Check s2Block1724 s2Block1740)) (@treeBlock_merge 1756 32 32 s2Check (@treeBlock_merge 1756 16 16 s2Check s2Block1756 s2Block1772) (@treeBlock_merge 1788 16 16 s2Check s2Block1788 s2Block1804))) (@treeBlock_merge 1820 64 52 s2Check (@treeBlock_merge 1820 32 32 s2Check (@treeBlock_merge 1820 16 16 s2Check s2Block1820 s2Block1836) (@treeBlock_merge 1852 16 16 s2Check s2Block1852 s2Block1868)) (@treeBlock_merge 1884 32 20 s2Check (@treeBlock_merge 1884 16 16 s2Check s2Block1884 s2Block1900) (@treeBlock_merge 1916 16 4 s2Check s2Block1916 s2Block1932)))))))
theorem s2Blocks : treeBlock 0 1936 s2Check = true := s2Verified
theorem s2Known : Known s2Cuts := extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s1Stock) s0Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Stock : Lower s2Mask s2StockWords s2Goal 11 := by
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
    rcases h with rfl | rfl <;> decide +kernel

end PEqualNP.Outside.L_meta_12216

open PEqualNP.Outside.L_meta_12216 in
theorem PEqualNP.Outside.L_meta_12216 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3900762240 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3900762240 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro t h
  let raw : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
  let goal : BitVec 64 := 0xe880e880e8808000
  have root : Lower (fullMask 64) (raw.map BitVec.toNat) goal.toNat 11 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) s2Stock
  have size : 11 ≤ t :=
    hcsLower (n := 6) raw goal 11 _ (by decide +kernel) (by decide +kernel) root t h
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [12, 13]⟩, ⟨.and, [14, 15]⟩], 16⟩
  refine ⟨circuit, ?_, ?_, by decide +kernel⟩
  · intro gate member
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · exact Nat.le_trans (by decide +kernel : circuit.size ≤ 11) size

