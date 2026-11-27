import PEqualNP.Defs

-- The live-wire checker is adapted from the accepted L-meta-8465 proof by odinfree.
namespace PEqualNP.Outside.L_meta_11257_aux

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

-- A viable state consists of the distinct values still needed by a circuit.
-- Each step chooses one gate, then keeps or discards each of its operands.
private def visitChild (mask : Word) (next : RowState → Bool) (state : RowState)
    (a b op keep : Nat) : Bool :=
  match childState mask (gateToken a b op keep) state with
  | none => true
  | some (fuel, ws, history) => dagForceWords ws (fun forced => next (fuel, forced, history))

private def binaryAt (mask : Word) (next : RowState → Bool) (state : RowState)
    (a b : Nat) : Bool :=
  treeBlock 0 2 (fun op => treeBlock 0 4 (visitChild mask next state a b op))

private def childrenAt (mask : Word) (next : RowState → Bool) (state : RowState) (a : Nat) : Bool :=
  treeBlock 0 2 (visitChild mask next state a a 2) &&
    treeBlock (a + 1) (state.2.1.length - (a + 1)) (binaryAt mask next state a)

private theorem childrenAt_from_parts {mask : Word} {next : RowState → Bool} {state : RowState}
    {a n : Nat} (len : state.2.1.length = n)
    (unary : treeBlock 0 2 (visitChild mask next state a a 2) = true)
    (binary : treeBlock (a + 1) (n - (a + 1)) (binaryAt mask next state a) = true) :
    childrenAt mask next state a = true := by
  unfold childrenAt
  rw [len]
  exact Bool.and_eq_true_iff.mpr ⟨unary, binary⟩

private def allChildren (mask : Word) (next : RowState → Bool) (state : RowState) : Bool :=
  treeBlock 0 state.2.1.length (childrenAt mask next state)

private theorem allChildren_at {mask : Word} {next : RowState → Bool} {state child : RowState}
    (ok : allChildren mask next state = true) (step : HasChild mask state child) :
    next child = true := by
  obtain ⟨a, b, op, keep, ha, how, he⟩ := step
  have h := treeBlock_at ok (Nat.zero_le a) (by simpa using ha)
  simp only [childrenAt, Bool.and_eq_true] at h
  obtain ⟨hu, hb⟩ := h
  rcases how with ⟨rfl, rfl, hk⟩ | ⟨hab, hbl, hop, hkeep⟩
  · have v := treeBlock_at hu (Nat.zero_le keep) (by simpa using hk)
    simpa only [visitChild, he, dagForceWordsEq] using v
  · have q := treeBlock_at hb (by omega : a + 1 ≤ b) (by omega)
    simp only [binaryAt] at q
    have qo := treeBlock_at q (Nat.zero_le op) (by simpa using hop)
    have v := treeBlock_at qo (Nat.zero_le keep) (by simpa using hkeep)
    simpa only [visitChild, he, dagForceWordsEq] using v

private def closes (mask goal : Word) (bounds : List Bound) : Nat → RowState → Bool :=
  Nat.rec (motive := fun _ => RowState → Bool) (fun state => !state.2.1.contains goal)
    (fun fuel next state =>
      let ws := state.2.1
      let cap := fuel + 2
      (cap < ws.length) ||
        (!ws.contains goal &&
          (!dagPartition (ws.length == cap) ws goal (mask ^^^ goal) ||
            dagKnownCloses goal bounds state || allChildren mask next state)))

private theorem childFuel {mask : Word} {state child : RowState}
    (h : HasChild mask state child) : child.1 = state.1 - 1 := by
  obtain ⟨a, b, op, keep, _, _, he⟩ := h
  obtain ⟨fuel, ws, history⟩ := state
  simp only [childState] at he
  repeat' first | contradiction | (cases he; rfl) | split at he

private theorem closes_sound {mask goal : Word} (hm : Masked mask goal) {fuel : Nat}
    {bounds : List Bound} (known : Known bounds)
    (submask : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    {state : RowState} (he : state.1 = fuel) (ok : closes mask goal bounds fuel state = true)
    (bound : fuel ≤ 12) (live : WordViable mask goal state) : False := by
  induction fuel generalizing state with
  | zero =>
    obtain ⟨_, k, t, hk, hl⟩ := live
    have hk' : k = 0 := by omega
    subst k
    have mem : goal ∈ state.2.1 := List.mem_toFinset.mp (hl.2.1 ▸ Finset.mem_singleton_self _)
    simp [closes, mem] at ok
  | succ fuel ih =>
    have ⟨nd, k, t, hk, hl⟩ := live
    have ⟨_, card⟩ := liveWordSize hl
    rw [List.toFinset_card_of_nodup nd] at card
    have wide : state.2.1.length ≤ fuel + 2 := by omega
    have good := dagPartitionLive hm hl (directed := state.2.1.length == fuel + 2)
    have part := good (by
      intro exactSize
      have eq := beq_iff_eq.mp exactSize
      omega)
    have cut := knownClosesSound known submask live
    have ok' : !state.2.1.contains goal &&
        allChildren mask (closes mask goal bounds fuel) state := by
      simpa [closes, show ¬ fuel + 2 < state.2.1.length by omega, part, dagKnownClosesEq, cut] using ok
    rcases wordProgress (by omega : state.2.1.length ≤ 64) live with mem | ⟨child, step, rest⟩
    · simp [mem] at ok'
    · have hec : child.1 = fuel := by have hh := childFuel step; omega
      exact ih hec (allChildren_at (Bool.and_eq_true_iff.mp ok').2 step) (by omega) rest


private theorem closes_from_children {mask goal : Word} {cuts : List Bound} {state : RowState}
    {fuel : Nat} (miss : state.2.1.contains goal = false)
    (children : allChildren mask (closes mask goal cuts fuel) state = true) :
    closes mask goal cuts (fuel + 1) state = true := by
  change (decide (fuel + 2 < state.2.1.length) ||
    (!state.2.1.contains goal &&
      (!dagPartition (state.2.1.length == fuel + 2) state.2.1 goal (mask ^^^ goal) ||
        dagKnownCloses goal cuts state || allChildren mask (closes mask goal cuts fuel) state))) = true
  rw [miss, children]
  simp

private theorem children_from_block {mask : Word} {next : RowState → Bool} {state : RowState}
    {n : Nat} (len : state.2.1.length = n)
    (h : treeBlock 0 n (childrenAt mask next state) = true) : allChildren mask next state = true := by
  unfold allChildren
  rw [len]
  exact h

private theorem singletonBlock {p : Nat → Bool} {i : Nat} (h : p i = true) :
    treeBlock i 1 p = true := by
  change (p i && true) = true
  simpa using h

private theorem deriveLower (mask goal : Word) (stock : List Word) (bounds : List Bound)
    (fuel : Nat) (limit : fuel ≤ 12) (hm : Masked mask goal) (proper : properWord mask goal)
    (hs : ∀ w ∈ stock, Masked mask w) (nd : stock.Nodup)
    (known : Known bounds) (sub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (checked : treeBlock 0 (2 ^ stock.length) (fun token =>
      closes mask goal bounds fuel (rootState stock fuel token)) = true) :
    Lower mask stock goal (fuel + 1) := by
  intro values built hit
  by_contra! short
  obtain ⟨k, t, S, hk, hl, avail⟩ := extractWordLive hs built hit proper
  obtain ⟨token, ht, heq⟩ := rootToken stock S
  have hs' : stock.toFinset ∩ S = S :=
    Finset.inter_eq_right.mpr (fun w hw => List.mem_toFinset.mpr (avail w hw))
  exact closes_sound hm known sub
    (state := rootState stock fuel token) rfl
    (treeBlock_at checked (Nat.zero_le _) (by simpa using ht)) limit
    ⟨nd.sublist (rootWordSublist stock token), k, t, by
        change k ≤ fuel
        omega,
      by simpa [rootState, heq, hs'] using hl⟩

private def rowSelectPacked (table : Nat) (i : Fin 128) : Fin 128 :=
  ⟨(table >>> (7 * i.val)) % 128, Nat.mod_lt _ (by decide)⟩

-- The stock and goal words below encode truth tables on subsets of the same 128 rows.
-- Each bound uses previously checked restrictions to rule out additional live-wire states.
private def stock9 : List Word := [0x202, 0x300]
private def b9 : Bound := (0x303, stock9, 1, 0x200)
private def cuts9 : List Bound := []
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks9 : treeBlock 0 (2 ^ stock9.length) (fun token =>
    closes b9.1 b9.2.2.2 cuts9 0 (rootState stock9 0 token)) = true := by
  decide +kernel
private theorem lower9 : Lower b9.1 stock9 b9.2.2.2 1 := by
  exact deriveLower b9.1 b9.2.2.2 stock9 cuts9 0
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
    (by unfold cuts9; decide +kernel) checks9

private def stock17 : List Word := [0x20002, 0x30000]
private def b17 : Bound := (0x30003, stock17, 1, 0x20000)
private def cuts17 : List Bound := []
private theorem lower17 : Lower b17.1 stock17 b17.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcf7ebcf8dfbb6ecd7ab4e8efdbaf4e7cb8f0cf9b2e4c78b0e0bf7aedcb76acd89f3a6cc972a4c8af5aad4a74a8d08f1a2c4870a0c07ef9ebc76e9cb85eb96ac56a94a86ed9ab466c98b04e992a446890a03e78e9c3668c981e3868c16284882e58a9426488900e182840608080) lower9
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock24 : List Word := [0x1000100, 0x1010000]
private def b24 : Bound := (0x1010101, stock24, 1, 0x1000000)
private def cuts24 : List Bound := []
private theorem lower24 : Lower b24.1 stock24 b24.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xffdff76fbd7e74df9f766db97664f7cfd72f3c7c70d78f562d387460bf5ef56bb56e549f1e7469b16644b74ed52b346c50970e54293064407eddf367ad5e345e9d7265a9562476cdd3272c5c30568d52252854203e5cf163a54e141e1c7061a14604364cd123244c10160c5021204400) lower9
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock33 : List Word := [0x200000002, 0x300000000]
private def b33 : Bound := (0x300000003, stock33, 1, 0x200000000)
private def cuts33 : List Bound := []
private theorem lower33 : Lower b33.1 stock33 b33.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcf7ebcf8bf7aedcb76acd8efdbaf4e7cb8f0af5aad4a74a8d0dfbb6ecd7ab4e89f3a6cc972a4c8cf9b2e4c78b0e08f1a2c4870a0c07ef9ebc76e9cb83e78e9c3668c986ed9ab466c98b02e58a9426488905eb96ac56a94a81e3868c16284884e992a446890a00e182840608080) lower9
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock34 : List Word := [0x400000004, 0x500000000]
private def b34 : Bound := (0x500000005, stock34, 1, 0x400000000)
private def cuts34 : List Bound := []
private theorem lower34 : Lower b34.1 stock34 b34.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7f7cf7e7d78bf76f5cb766d58efd7b74e7c7970af56b54a746950dfb776cd7a75689f3674c9726548cf97364c7871608f1634487061407ef5f3c76e5d383e74f1c3664d186ed5b3466c59302e54b1426449105eb572c56a55281e3470c16245084e9532446851200e143040604100) lower9
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock36 : List Word := [0x1000000010, 0x1100000000]
private def b36 : Bound := (0x1100000011, stock36, 1, 0x1000000000)
private def cuts36 : List Bound := []
private theorem lower36 : Lower b36.1 stock36 b36.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xffeff7afbe7e78bf6ef5abb66e58efcfb72ebc7a70af4eb52ab46a50dfaf76adba76689f2e74a9b26648cf8f362cb872608f0e3428b062407eedf3a7ae5e383e6cf1a3a64e186ecdb326ac5a302e4cb122a44a105ead72a5aa56281e2c70a1a246084e8d3224a852200e0c3020a04200) lower9
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock66 : List Word := [0x40000000000000004, 0x50000000000000000]
private def b66 : Bound := (0x50000000000000005, stock66, 1, 0x40000000000000000)
private def cuts66 : List Bound := []
private theorem lower66 : Lower b66.1 stock66 b66.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7f7cf7e7d787ef5f3c76e5d38efd7b74e7c79706ed5b3466c5930dfb776cd7a75685eb572c56a5528cf97364c7871604e953244685120bf76f5cb766d583e74f1c3664d18af56b54a7469502e54b1426449109f3674c97265481e3470c16245088f1634487061400e143040604100) lower9
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock68 : List Word := [0x100000000000000010, 0x110000000000000000]
private def b68 : Bound := (0x110000000000000011, stock68, 1, 0x100000000000000000)
private def cuts68 : List Bound := []
private theorem lower68 : Lower b68.1 stock68 b68.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xffeff7afbe7e787eedf3a7ae5e38efcfb72ebc7a706ecdb326ac5a30dfaf76adba76685ead72a5aa5628cf8f362cb872604e8d3224a85220bf6ef5abb66e583e6cf1a3a64e18af4eb52ab46a502e4cb122a44a109f2e74a9b266481e2c70a1a246088f0e3428b062400e0c3020a04200) lower9
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock72 : List Word := [0x1000000000000000100, 0x1010000000000000000]
private def b72 : Bound := (0x1010000000000000101, stock72, 1, 0x1000000000000000000)
private def cuts72 : List Bound := []
private theorem lower72 : Lower b72.1 stock72 b72.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xffdff76fbd7e747eddf367ad5e34f7cfd72f3c7c7076cdd3272c5c30df9f766db976645e9d7265a95624d78f562d387460568d5225285420bf5ef56bb56e543e5cf163a54e14b74ed52b346c50364cd123244c109f1e7469b166441e1c7061a14604970e5429306440160c5021204400) lower9
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock80 : List Word := [0x100000000000000010000, 0x100010000000000000000]
private def b80 : Bound := (0x100010000000000010001, stock80, 1, 0x100000000000000000000)
private def cuts80 : List Bound := []
private theorem lower80 : Lower b80.1 stock80 b80.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xffbff6efbb7e6c7ebdf2e7ab5e2cf7afd6af3a7c6876add2a72a5c28ef9fb66eb97a646e9db266a95a24e78f962e387860668d9226285820bf3ef4ebb36e4c3e3cf0e3a34e0cb72ed4ab326c48362cd0a3224c08af1eb46ab16a442e1cb062a14a04a70e942a306840260c9022204800) lower9
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock25 : List Word := [0x2020202, 0x3000300, 0x3030000]
private def b25 : Bound := (0x3030303, stock25, 4, 0x3020200)
private def cuts25 : List Bound := [b9, b17, b24]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks25 : treeBlock 0 (2 ^ stock25.length) (fun token =>
    closes b25.1 b25.2.2.2 cuts25 3 (rootState stock25 3 token)) = true := by
  decide +kernel
private theorem lower25 : Lower b25.1 stock25 b25.2.2.2 4 := by
  exact deriveLower b25.1 b25.2.2.2 stock25 cuts25 3
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower24) lower17) lower9)
    (by unfold cuts25; decide +kernel) checks25

private def stock35 : List Word := [0xa0000000a, 0xc0000000c, 0xf00000000]
private def b35 : Bound := (0xf0000000f, stock35, 2, 0xe00000000)
private def cuts35 : List Bound := [b33, b34]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks35 : treeBlock 0 (2 ^ stock35.length) (fun token =>
    closes b35.1 b35.2.2.2 cuts35 1 (rootState stock35 1 token)) = true := by
  decide +kernel
private theorem lower35 : Lower b35.1 stock35 b35.2.2.2 2 := by
  exact deriveLower b35.1 b35.2.2.2 stock35 cuts35 1
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower34) lower33)
    (by unfold cuts35; decide +kernel) checks35

private def stock37 : List Word := [0x2200000022, 0x3000000030, 0x3300000000]
private def b37 : Bound := (0x3300000033, stock37, 2, 0x3200000000)
private def cuts37 : List Bound := [b33, b36]
private theorem lower37 : Lower b37.1 stock37 b37.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbdfafbf3cf8efdb9f2ebd38f0dfbb5eadbb34e8cf9b1e2cb930e0bf7addabb72cd8af5a9d2ab528d09f3a5ca9b324c88f1a1c28b120c07ef9dba7af1cb86ed99b26ad18b05eb95aa5ab14a84e991a24a910a03e78d9a3a70c982e589922a508901e3858a1a304880e181820a10080) lower35
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock38 : List Word := [0x4400000044, 0x5000000050, 0x5500000000]
private def b38 : Bound := (0x5500000055, stock38, 2, 0x5400000000)
private def cuts38 : List Bound := [b34, b36]
private theorem lower38 : Lower b38.1 stock38 b38.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7df9fdf3d78efd79f1edd3970dfb75e9ddb3568cf971e1cd93160bf76dd9bd72d58af569d1ad529509f365c99d325488f161c18d121407ef5db97cf1d386ed59b16cd19305eb55a95cb15284e951a14c911203e74d993c70d182e549912c509101e345891c305080e141810c10100) lower35
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock41 : List Word := [0x20200000202, 0x30000000300, 0x30300000000]
private def b41 : Bound := (0x30300000303, stock41, 2, 0x20200000200)
private def cuts41 : List Bound := [b9, b33]
private theorem lower41 : Lower b41.1 stock41 b41.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xffdefd7fbd6ed5f7cedd3f3c6cd1df9e7c7db966c5d78e5c3d3864c1fddaf56f9d2e54f5cad52f1c2c50dd9a746d992644d58a542d1824407edcf977ad4e9576ccd9372c4c915e9c7875a94685568c58352844817cd8f1678d0e1474c8d1270c0c105c98706589060454885025080400) lower35
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock49 : List Word := [0x2000200020002, 0x3000000030000, 0x3000300000000]
private def b49 : Bound := (0x3000300030003, stock49, 2, 0x2000200020000)
private def cuts49 : List Bound := [b17, b33]
private theorem lower49 : Lower b49.1 stock49 b49.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xffbefcffbb6ecdf7aedcbf3a6cc9ef9ebc7eb96ac5e78e9c3e3868c1fdbaf4ef9b2e4cf5aad4af1a2c48ed9ab46e992a44e58a942e1828407ebcf8f7ab4e8d76acd8b72a4c896e9cb876a94a85668c98362848817cb8f0e78b0e0c74a8d0a70a0c086c98b066890a0464889026080800) lower35
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock70 : List Word := [0x440000000000000044, 0x500000000000000050, 0x550000000000000000]
private def b70 : Bound := (0x550000000000000055, stock70, 2, 0x540000000000000000)
private def cuts70 : List Bound := [b66, b68]
private theorem lower70 : Lower b70.1 stock70 b70.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7df9fdf3d78efd79f1edd3970dfb75e9ddb3568cf971e1cd931607ef5db97cf1d386ed59b16cd19305eb55a95cb15284e951a14c91120bf76dd9bd72d58af569d1ad529509f365c99d325488f161c18d121403e74d993c70d182e549912c509101e345891c305080e141810c10100) lower35
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock73 : List Word := [0x2020000000000000202, 0x3000000000000000300, 0x3030000000000000000]
private def b73 : Bound := (0x3030000000000000303, stock73, 2, 0x3000000000000000200)
private def cuts73 : List Bound := [b9, b72]
private theorem lower73 : Lower b73.1 stock73 b73.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xfff9fbefbf1ebcf7e9dbaf3e1cb8dfb97aedbb16acd7a95aad3a14a8efd9bb6ebd1ab4e7c99b2e3c18b0cf993a6cb912a4c7891a2c3810a0bf78f9ebb70e9cb768d9ab360c989f3878e9b3068c972858a9320488af58b96ab50a94a748992a3408908f183868b1028487081828300080) lower35
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock74 : List Word := [0x4040000000000000404, 0x5000000000000000500, 0x5050000000000000000]
private def b74 : Bound := (0x5050000000000000505, stock74, 2, 0x5040000000000000000)
private def cuts74 : List Bound := [b66, b72]
private theorem lower74 : Lower b74.1 stock74 b74.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7bf5fdf3b74f7e79f1f5e3970dfb73e5ddb3364d7a71e1d5a31607ef5bb57cf1b3476e59b174e19305eb53a55cb132456a51a154a1120bf76bd5bd72b54b7669d1b5629509f363c59d3234497261c195221403e74b953c70b14366499134609101e343851c3030416241811420100) lower35
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock76 : List Word := [0x10100000000000001010, 0x11000000000000001100, 0x11110000000000000000]
private def b76 : Bound := (0x11110000000000001111, stock76, 2, 0x11100000000000000000)
private def cuts76 : List Bound := [b68, b72]
private theorem lower76 : Lower b76.1 stock76 b76.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xffefbf3fdebb72fbe7af1f9e3a70dfaf3e3ddab362dba72e1d9a32607eedbb37ce9b327ae5ab178e1a305ead3a35ca93225aa52a158a1220bf6ebd3bd6ab52bb66ad1b962a509f2e3c39d2a3429b262c199222403e6cb933c68b123a64a913860a101e2c3831c283021a242811820200) lower35
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock81 : List Word := [0x200020000000000020002, 0x300000000000000030000, 0x300030000000000000000]
private def b81 : Bound := (0x300030000000000030003, stock81, 2, 0x300000000000000020000)
private def cuts81 : List Bound := [b17, b80]
private theorem lower81 : Lower b81.1 stock81 b81.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xfff9fbefbf1ebcf7e9dbaf3e1cb8efd9bb6ebd1ab4e7c99b2e3c18b0dfb97aedbb16acd7a95aad3a14a8cf993a6cb912a4c7891a2c3810a0bf78f9ebb70e9cb768d9ab360c98af58b96ab50a94a748992a3408909f3878e9b3068c972858a93204888f183868b1028487081828300080) lower35
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock82 : List Word := [0x400040000000000040004, 0x500000000000000050000, 0x500050000000000000000]
private def b82 : Bound := (0x500050000000000050005, stock82, 2, 0x500040000000000000000)
private def cuts82 : List Bound := [b66, b80]
private theorem lower82 : Lower b82.1 stock82 b82.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xfff77edfdf376cf7e75e9f5e3568efd73e5edd3364e7c71e1e5c31607ef57ad7cf172c76e55a974e15286ed53a56cd132466c51a164c1120bf767cdbd7274cb7665c9b562548af563c5ad52344a7461c1a5421403e7478d3c7070c366458934605082e543852c5030426441812440100) lower35
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock84 : List Word := [0x1000100000000000100010, 0x1100000000000000110000, 0x1100110000000000000000]
private def b84 : Bound := (0x1100110000000000110011, stock84, 2, 0x1100100000000000000000)
private def cuts84 : List Bound := [b68, b80]
private theorem lower84 : Lower b84.1 stock84 b84.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xffef7ebfdeb76afbe76e9f9e3668efcf3e3edcb362ebc72e1e9c32607eed7ab7ce972a7ae56a978e16286ecd3a36cc93226ac52a168c1220bf6e7cbbd6a74abb666c9b962648af4e3c3ad4a342ab462c1a9422403e6c78b3c6870a3a6468938606082e4c3832c483022a442812840200) lower35
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock88 : List Word := [0x10001000000000001000100, 0x10100000000000001010000, 0x10101010000000000000000]
private def b88 : Bound := (0x10101010000000001010101, stock88, 4, 0x10101000000000001000000)
private def cuts88 : List Bound := [b24, b72, b80]
private theorem lower88 : Lower b88.1 stock88 b88.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xffdff76fbd7e74df9f766db976647eddf367ad5e345e9d7265a95624f7cfd72f3c7c70d78f562d38746076cdd3272c5c30568d5225285420bf5ef56bb56e549f1e7469b166443e5cf163a54e141e1c7061a14604b74ed52b346c50970e5429306440364cd123244c10160c5021204400) lower25
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock98 : List Word := [0x4000000040000000400000004, 0x5000000000000000500000000, 0x5000000050000000000000000]
private def b98 : Bound := (0x5000000050000000500000005, stock98, 2, 0x4000000040000000400000000)
private def cuts98 : List Bound := [b34, b66]
private theorem lower98 : Lower b98.1 stock98 b98.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xff7df9ffd79f1ef76dd9bf569d1aef5db97ed59b16e74d993e549912fb75e9df971e1cf365c99f161c18eb55a95e951a14e345891e141810df3d78fdd3970ed72d58bd52950acf1d387cd19306c70d183c509102db3568dd93160cd325489d121408cb15285c911204c305081c101000) lower35
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock100 : List Word := [0x10000000100000001000000010, 0x11000000000000001100000000, 0x11000000110000000000000000]
private def b100 : Bound := (0x11000000110000001100000011, stock100, 2, 0x10000000100000001000000000)
private def cuts100 : List Bound := [b36, b68]
private theorem lower100 : Lower b100.1 stock100 b100.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xff7df9ffd79f1efb75e9df971e1cef5db97ed59b16eb55a95e951a14f76dd9bf569d1af365c99f161c18e74d993e549912e345891e141810df3d78fdd3970edb3568dd93160ccf1d387cd19306cb15285c911204d72d58bd52950ad325489d121408c70d183c509102c305081c101000) lower35
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock39 : List Word := [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000]
private def b39 : Bound := (0xff000000ff, stock39, 3, 0xfe00000000)
private def cuts39 : List Bound := [b35, b37, b38]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks39 : treeBlock 0 (2 ^ stock39.length) (fun token =>
    closes b39.1 b39.2.2.2 cuts39 2 (rootState stock39 2 token)) = true := by
  decide +kernel
private theorem lower39 : Lower b39.1 stock39 b39.2.2.2 3 := by
  exact deriveLower b39.1 b39.2.2.2 stock39 cuts39 2
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower38) lower37) lower35)
    (by unfold cuts39; decide +kernel) checks39

private def stock43 : List Word := [0xa0a00000a0a, 0xc0c00000c0c, 0xf0000000f00, 0xf0f00000000]
private def b43 : Bound := (0xf0f00000f0f, stock43, 4, 0xe0e00000a00)
private def cuts43 : List Bound := [b35, b41, b9, b34]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks43 : treeBlock 0 (2 ^ stock43.length) (fun token =>
    closes b43.1 b43.2.2.2 cuts43 3 (rootState stock43 3 token)) = true := by
  decide +kernel
private theorem lower43 : Lower b43.1 stock43 b43.2.2.2 4 := by
  exact deriveLower b43.1 b43.2.2.2 stock43 cuts43 3
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower34) lower9) lower41) lower35)
    (by unfold cuts43; decide +kernel) checks43

private def stock45 : List Word := [0x222200002222, 0x303000003030, 0x330000003300, 0x333300000000]
private def b45 : Bound := (0x333300003333, stock45, 4, 0x323200002200)
private def cuts45 : List Bound := [b37, b41, b9, b36]
private theorem lower45 : Lower b45.1 stock45 b45.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbdfafbf3cf8efdb9f2ebd38f0dfbb5eadbb34e8cf9b1e2cb930e0bf7addabb72cd8af5a9d2ab528d09f3a5ca9b324c88f1a1c28b120c07ef9dba7af1cb86ed99b26ad18b05eb95aa5ab14a84e991a24a910a03e78d9a3a70c982e589922a508901e3858a1a304880e181820a10080) lower43
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock51 : List Word := [0xa000a000a000a, 0xc000c000c000c, 0xf0000000f0000, 0xf000f00000000]
private def b51 : Bound := (0xf000f000f000f, stock51, 4, 0xe000e000a0000)
private def cuts51 : List Bound := [b35, b49, b17, b34]
private theorem lower51 : Lower b51.1 stock51 b51.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcf7ebcf8dfbb6ecd7ab4e8efdbaf4e7cb8f0cf9b2e4c78b0e0bf7aedcb76acd89f3a6cc972a4c8af5aad4a74a8d08f1a2c4870a0c07ef9ebc76e9cb85eb96ac56a94a86ed9ab466c98b04e992a446890a03e78e9c3668c981e3868c16284882e58a9426488900e182840608080) lower43
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock53 : List Word := [0x22002200220022, 0x30003000300030, 0x33000000330000, 0x33003300000000]
private def b53 : Bound := (0x33003300330033, stock53, 4, 0x32003200220000)
private def cuts53 : List Bound := [b37, b49, b17, b36]
private theorem lower53 : Lower b53.1 stock53 b53.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbdfafbf3cf8dfbb5eadbb34e8efdb9f2ebd38f0cf9b1e2cb930e0bf7addabb72cd89f3a5ca9b324c8af5a9d2ab528d08f1a1c28b120c07ef9dba7af1cb85eb95aa5ab14a86ed99b26ad18b04e991a24a910a03e78d9a3a70c981e3858a1a304882e589922a508900e181820a10080) lower43
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock57 : List Word := [0x202020202020202, 0x300030003000300, 0x303000003030000, 0x303030300000000]
private def b57 : Bound := (0x303030303030303, stock57, 5, 0x302020203020200)
private def cuts57 : List Bound := [b25, b41, b49, b24]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks57 : treeBlock 0 (2 ^ stock57.length) (fun token =>
    closes b57.1 b57.2.2.2 cuts57 4 (rootState stock57 4 token)) = true := by
  decide +kernel
private theorem lower57 : Lower b57.1 stock57 b57.2.2.2 5 := by
  exact deriveLower b57.1 b57.2.2.2 stock57 cuts57 4
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower24) lower49) lower41) lower25)
    (by unfold cuts57; decide +kernel) checks57

private def stock58 : List Word := [0x404040404040404, 0x500050005000500, 0x505000005050000, 0x505050500000000]
private def b58 : Bound := (0x505050505050505, stock58, 3, 0x504040405000000)
private def cuts58 : List Bound := [b24, b34]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks58 : treeBlock 0 (2 ^ stock58.length) (fun token =>
    closes b58.1 b58.2.2.2 cuts58 2 (rootState stock58 2 token)) = true := by
  decide +kernel
private theorem lower58 : Lower b58.1 stock58 b58.2.2.2 3 := by
  exact deriveLower b58.1 b58.2.2.2 stock58 cuts58 2
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower34) lower24)
    (by unfold cuts58; decide +kernel) checks58

private def stock60 : List Word := [0x1010101010101010, 0x1100110011001100, 0x1111000011110000, 0x1111111100000000]
private def b60 : Bound := (0x1111111111111111, stock60, 3, 0x1110101011000000)
private def cuts60 : List Bound := [b24, b36]
private theorem lower60 : Lower b60.1 stock60 b60.2.2.2 3 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbdfafbf3cf8efdb9f2ebd38f0dfbb5eadbb34e8cf9b1e2cb930e0bf7addabb72cd8af5a9d2ab528d09f3a5ca9b324c88f1a1c28b120c07ef9dba7af1cb86ed99b26ad18b05eb95aa5ab14a84e991a24a910a03e78d9a3a70c982e589922a508901e3858a1a304880e181820a10080) lower58
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock75 : List Word := [0xa0a0000000000000a0a, 0xc0c0000000000000c0c, 0xf000000000000000f00, 0xf0f0000000000000000]
private def b75 : Bound := (0xf0f0000000000000f0f, stock75, 4, 0xf0c0000000000000a00)
private def cuts75 : List Bound := [b73, b74, b9, b66]
private theorem lower75 : Lower b75.1 stock75 b75.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xffdfef5f7cfcf1fddbe74f5cbc70df9f6e5d78f4e1dd9b664d58b4607eddeb576cdcb17cd9e3474c9c305e9d6a5568d4a15c996245489420bf5eed5b74ecd1bd5ae54b54ac509f1e6c5970e4c19d1a644950a4403e5ce95364cc913c58e143448c101e1c685160c4811c186041408400) lower43
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock77 : List Word := [0x22220000000000002222, 0x30300000000000003030, 0x33000000000000003300, 0x33330000000000000000]
private def b77 : Bound := (0x33330000000000003333, stock77, 4, 0x33300000000000002200)
private def cuts77 : List Bound := [b73, b76, b9, b68]
private theorem lower77 : Lower b77.1 stock77 b77.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xffdfdf3fbd7cf1fddbd72f9d3c70df9f5e3db974e1dd9b562d9934607edddb37ad5cb17cd9d3278d1c305e9d5a35a954a15c995225891420bf5edd3bb56cd1bd5ad52b952c509f1e5c39b164c19d1a54299124403e5cd933a54c913c58d123850c101e1c5831a144811c185021810400) lower43
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock78 : List Word := [0x44440000000000004444, 0x50500000000000005050, 0x55000000000000005500, 0x55550000000000000000]
private def b78 : Bound := (0x55550000000000005555, stock78, 3, 0x55540000000000000000)
private def cuts78 : List Bound := [b70, b74, b76]
private theorem lower78 : Lower b78.1 stock78 b78.2.2.2 3 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7df9efd79f1fdf3d78edd3970dfb75e9cf971e1ddb3568cd931607ef5db96ed59b17cf1d386cd19305eb55a94e951a15cb15284c91120bf76dd9af569d1bd72d58ad529509f365c98f161c19d325488d121403e74d992e549913c70d182c509101e345890e141811c305080c10100) lower39
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock83 : List Word := [0xa000a00000000000a000a, 0xc000c00000000000c000c, 0xf000000000000000f0000, 0xf000f0000000000000000]
private def b83 : Bound := (0xf000f00000000000f000f, stock83, 4, 0xf000c00000000000a0000)
private def cuts83 : List Bound := [b81, b82, b17, b66]
private theorem lower83 : Lower b83.1 stock83 b83.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xffbfeedf7afce9fdbbe6cf5abc68ef9fae5e78f8e1ed9ba64e58b8607ebdead76adca97cb9e2c74a9c286e9daa5668d8a16c99a246489820bf3eecdb72ecc9bd3ae4cb52ac48af1eac5a70e8c1ad1aa44a50a8403e3ce8d362cc893c38e0c3428c082e1ca85260c8812c18a042408800) lower43
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock85 : List Word := [0x2200220000000000220022, 0x3000300000000000300030, 0x3300000000000000330000, 0x3300330000000000000000]
private def b85 : Bound := (0x3300330000000000330033, stock85, 4, 0x3300300000000000220000)
private def cuts85 : List Bound := [b81, b84, b17, b68]
private theorem lower85 : Lower b85.1 stock85 b85.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xffbfdebfbb7ce9fdbbd6af9b3c68ef9f9e3eb978e1ed9b962e9938607ebddab7ab5ca97cb9d2a78b1c286e9d9a36a958a16c999226891820bf3edcbbb36cc9bd3ad4ab932c48af1e9c3ab168c1ad1a942a9128403e3cd8b3a34c893c38d0a3830c082e1c9832a148812c189022810800) lower43
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock86 : List Word := [0x4400440000000000440044, 0x5000500000000000500050, 0x5500000000000000550000, 0x5500550000000000000000]
private def b86 : Bound := (0x5500550000000000550055, stock86, 3, 0x5500540000000000000000)
private def cuts86 : List Bound := [b70, b82, b84]
private theorem lower86 : Lower b86.1 stock86 b86.2.2.2 3 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7df9dfb75e9fdf3d78ddb3568efd79f1cf971e1edd3970cd931607ef5db95eb55a97cf1d385cb15286ed59b14e951a16cd19304c91120bf76dd99f365c9bd72d589d32548af569d18f161c1ad529508d121403e74d991e345893c70d181c305082e549910e141812c509100c10100) lower39
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock89 : List Word := [0x20202020000000002020202, 0x30003000000000003000300, 0x30300000000000003030000, 0x30303030000000000000000]
private def b89 : Bound := (0x30303030000000003030303, stock89, 5, 0x30303000000000003020200)
private def cuts89 : List Bound := [b25, b88, b73, b81]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks89 : treeBlock 0 (2 ^ stock89.length) (fun token =>
    closes b89.1 b89.2.2.2 cuts89 4 (rootState stock89 4 token)) = true := by
  decide +kernel
private theorem lower89 : Lower b89.1 stock89 b89.2.2.2 5 := by
  exact deriveLower b89.1 b89.2.2.2 stock89 cuts89 4
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower81) lower73) lower88) lower25)
    (by unfold cuts89; decide +kernel) checks89

private def stock90 : List Word := [0x40404040000000004040404, 0x50005000000000005000500, 0x50500000000000005050000, 0x50505050000000000000000]
private def b90 : Bound := (0x50505050000000005050505, stock90, 5, 0x50505040000000005000000)
private def cuts90 : List Bound := [b88, b74, b82, b24]
private theorem lower90 : Lower b90.1 stock90 b90.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xfefff3ef6efd3aeedfb36e6cf932debf72ed6af52ace9f326c68f122faf7e3cf2e7c38ead7a34e2c7830dab762cd2a7428ca97224c287020be7ef1eb66ed1aae5eb16a64e9129e3e70e962e50a8e1e306860e102ba76e1cb266c18aa56a14a2468109a3660c92264088a162048206000) lower57
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock92 : List Word := [0x101010100000000010101010, 0x110011000000000011001100, 0x111100000000000011110000, 0x111111110000000000000000]
private def b92 : Bound := (0x111111110000000011111111, stock92, 5, 0x111111100000000011000000)
private def cuts92 : List Bound := [b88, b76, b84, b24]
private theorem lower92 : Lower b92.1 stock92 b92.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xfefff3efaf7e3ceedfb36ead7a34debf72edab762cce9f326ca97224f6efd3af2e7c38e6cf932e2c7830d6af52ad2a7428c68f122c287020be7ef1eba76e1cae5eb16aa56a149e3e70e9a3660c8e1e3068a16204b66ed1ab266c18a64e912a246810962e50a9226408860e1028206000) lower57
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock99 : List Word := [0xa0000000a0000000a0000000a, 0xc0000000c0000000c0000000c, 0xf000000000000000f00000000, 0xf0000000f0000000000000000]
private def b99 : Bound := (0xf0000000f0000000f0000000f, stock99, 4, 0xe0000000c0000000e00000000)
private def cuts99 : List Bound := [b35, b98, b33, b66]
private theorem lower99 : Lower b99.1 stock99 b99.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7f7cf7e7d787ef5f3c76e5d38efd7b74e7c79706ed5b3466c5930bf76f5cb766d583e74f1c3664d18af56b54a7469502e54b142644910dfb776cd7a75685eb572c56a5528cf97364c7871604e9532446851209f3674c97265481e3470c16245088f1634487061400e143040604100) lower43
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock101 : List Word := [0x22000000220000002200000022, 0x30000000300000003000000030, 0x33000000000000003300000000, 0x33000000330000000000000000]
private def b101 : Bound := (0x33000000330000003300000033, stock101, 4, 0x32000000300000003200000000)
private def cuts101 : List Bound := [b37, b100, b33, b68]
private theorem lower101 : Lower b101.1 stock101 b101.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xffeff7afbe7e787eedf3a7ae5e38efcfb72ebc7a706ecdb326ac5a30bf6ef5abb66e583e6cf1a3a64e18af4eb52ab46a502e4cb122a44a10dfaf76adba76685ead72a5aa5628cf8f362cb872604e8d3224a852209f2e74a9b266481e2c70a1a246088f0e3428b062400e0c3020a04200) lower43
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock102 : List Word := [0x44000000440000004400000044, 0x50000000500000005000000050, 0x55000000000000005500000000, 0x55000000550000000000000000]
private def b102 : Bound := (0x55000000550000005500000055, stock102, 3, 0x54000000540000005400000000)
private def cuts102 : List Bound := [b38, b70, b98, b100]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks102 : treeBlock 0 (2 ^ stock102.length) (fun token =>
    closes b102.1 b102.2.2.2 cuts102 2 (rootState stock102 2 token)) = true := by
  decide +kernel
private theorem lower102 : Lower b102.1 stock102 b102.2.2.2 3 := by
  exact deriveLower b102.1 b102.2.2.2 stock102 cuts102 2
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower100) lower98) lower70) lower38)
    (by unfold cuts102; decide +kernel) checks102

private def stock105 : List Word := [0x202000002020000020200000202, 0x300000003000000030000000300, 0x303000000000000030300000000, 0x303000003030000000000000000]
private def b105 : Bound := (0x303000003030000030300000303, stock105, 4, 0x302000003000000020200000200)
private def cuts105 : List Bound := [b41, b73, b33, b72]
private theorem lower105 : Lower b105.1 stock105 b105.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xfff9fbefbf1ebcbf78f9ebb70e9cf7e9dbaf3e1cb8b768d9ab360c98efd9bb6ebd1ab4af58b96ab50a94e7c99b2e3c18b0a748992a340890dfb97aedbb16ac9f3878e9b3068cd7a95aad3a14a8972858a9320488cf993a6cb912a48f183868b10284c7891a2c3810a087081828300080) lower43
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock106 : List Word := [0x404000004040000040400000404, 0x500000005000000050000000500, 0x505000000000000050500000000, 0x505000005050000000000000000]
private def b106 : Bound := (0x505000005050000050500000505, stock106, 4, 0x504000005040000040400000000)
private def cuts106 : List Bound := [b74, b98, b34, b72]
private theorem lower106 : Lower b106.1 stock106 b106.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7bf5fdf3b74bf76bd5bd72b54f7e79f1f5e3970b7669d1b5629507ef5bb57cf1b343e74b953c70b1476e59b174e193036649913460910dfb73e5ddb33649f363c59d32344d7a71e1d5a316097261c195221405eb53a55cb13241e343851c3030456a51a154a112016241811420100) lower43
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock108 : List Word := [0x1010000010100000101000001010, 0x1100000011000000110000001100, 0x1111000000000000111100000000, 0x1111000011110000000000000000]
private def b108 : Bound := (0x1111000011110000111100001111, stock108, 4, 0x1110000011100000101000000000)
private def cuts108 : List Bound := [b76, b100, b36, b72]
private theorem lower108 : Lower b108.1 stock108 b108.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xffefbf3fdebb72bf6ebd3bd6ab52fbe7af1f9e3a70bb66ad1b962a507eedbb37ce9b323e6cb933c68b127ae5ab178e1a303a64a913860a10dfaf3e3ddab3629f2e3c39d2a342dba72e1d9a32609b262c199222405ead3a35ca93221e2c3831c283025aa52a158a12201a242811820200) lower43
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock113 : List Word := [0x20002000200020002000200020002, 0x30000000300000003000000030000, 0x30003000000000003000300000000, 0x30003000300030000000000000000]
private def b113 : Bound := (0x30003000300030003000300030003, stock113, 4, 0x30002000300000002000200020000)
private def cuts113 : List Bound := [b49, b81, b33, b80]
private theorem lower113 : Lower b113.1 stock113 b113.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xfff9fbefbf1ebcbf78f9ebb70e9cf7e9dbaf3e1cb8b768d9ab360c98dfb97aedbb16ac9f3878e9b3068cd7a95aad3a14a8972858a9320488efd9bb6ebd1ab4af58b96ab50a94e7c99b2e3c18b0a748992a340890cf993a6cb912a48f183868b10284c7891a2c3810a087081828300080) lower43
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock114 : List Word := [0x40004000400040004000400040004, 0x50000000500000005000000050000, 0x50005000000000005000500000000, 0x50005000500050000000000000000]
private def b114 : Bound := (0x50005000500050005000500050005, stock114, 4, 0x50004000500040004000400000000)
private def cuts114 : List Bound := [b82, b98, b34, b80]
private theorem lower114 : Lower b114.1 stock114 b114.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xfff77edfdf376cbf767cdbd7274cf7e75e9f5e3568b7665c9b5625487ef57ad7cf172c3e7478d3c7070c76e55a974e152836645893460508efd73e5edd3364af563c5ad52344e7c71e1e5c3160a7461c1a5421406ed53a56cd13242e543852c5030466c51a164c112026441812440100) lower43
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock116 : List Word := [0x100010001000100010001000100010, 0x110000001100000011000000110000, 0x110011000000000011001100000000, 0x110011001100110000000000000000]
private def b116 : Bound := (0x110011001100110011001100110011, stock116, 4, 0x110010001100100010001000000000)
private def cuts116 : List Bound := [b84, b100, b36, b80]
private theorem lower116 : Lower b116.1 stock116 b116.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xffef7ebfdeb76abf6e7cbbd6a74afbe76e9f9e3668bb666c9b9626487eed7ab7ce972a3e6c78b3c6870a7ae56a978e16283a646893860608efcf3e3edcb362af4e3c3ad4a342ebc72e1e9c3260ab462c1a9422406ecd3a36cc93222e4c3832c483026ac52a168c12202a442812840200) lower43
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock47 : List Word := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]
private def b47 : Bound := (0xffff0000ffff, stock47, 5, 0xfefe0000aa00)
private def cuts47 : List Bound := [b43, b45, b39, b38, b9]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks47 : treeBlock 0 (2 ^ stock47.length) (fun token =>
    closes b47.1 b47.2.2.2 cuts47 4 (rootState stock47 4 token)) = true := by
  decide +kernel
private theorem lower47 : Lower b47.1 stock47 b47.2.2.2 5 := by
  exact deriveLower b47.1 b47.2.2.2 stock47 cuts47 4
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower9) lower38) lower39) lower45) lower43)
    (by unfold cuts47; decide +kernel) checks47

private def stock55 : List Word := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]
private def b55 : Bound := (0xff00ff00ff00ff, stock55, 5, 0xfe00fe00aa0000)
private def cuts55 : List Bound := [b51, b53, b39, b38, b17]
private theorem lower55 : Lower b55.1 stock55 b55.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcf7ebcf8dfbb6ecd7ab4e8efdbaf4e7cb8f0cf9b2e4c78b0e0bf7aedcb76acd89f3a6cc972a4c8af5aad4a74a8d08f1a2c4870a0c07ef9ebc76e9cb85eb96ac56a94a86ed9ab466c98b04e992a446890a03e78e9c3668c981e3868c16284882e58a9426488900e182840608080) lower47
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock59 : List Word := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]
private def b59 : Bound := (0xf0f0f0f0f0f0f0f, stock59, 7, 0xf0e0e0e0f0a0a00)
private def cuts59 : List Bound := [b57, b25, b43, b51, b58]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks59 : treeBlock 0 (2 ^ stock59.length) (fun token =>
    closes b59.1 b59.2.2.2 cuts59 6 (rootState stock59 6 token)) = true := by
  decide +kernel
private theorem lower59 : Lower b59.1 stock59 b59.2.2.2 7 := by
  exact deriveLower b59.1 b59.2.2.2 stock59 cuts59 6
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower58) lower51) lower43) lower25) lower57)
    (by unfold cuts59; decide +kernel) checks59

private def stock61 : List Word := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]
private def b61 : Bound := (0x3333333333333333, stock61, 7, 0x3332323233222200)
private def cuts61 : List Bound := [b57, b25, b45, b53, b60]
private theorem lower61 : Lower b61.1 stock61 b61.2.2.2 7 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbdfafbf3cf8efdb9f2ebd38f0dfbb5eadbb34e8cf9b1e2cb930e0bf7addabb72cd8af5a9d2ab528d09f3a5ca9b324c88f1a1c28b120c07ef9dba7af1cb86ed99b26ad18b05eb95aa5ab14a84e991a24a910a03e78d9a3a70c982e589922a508901e3858a1a304880e181820a10080) lower59
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock62 : List Word := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]
private def b62 : Bound := (0x5555555555555555, stock62, 4, 0x5554545455000000)
private def cuts62 : List Bound := [b58, b60, b38, b24]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks62 : treeBlock 0 (2 ^ stock62.length) (fun token =>
    closes b62.1 b62.2.2.2 cuts62 3 (rootState stock62 3 token)) = true := by
  decide +kernel
private theorem lower62 : Lower b62.1 stock62 b62.2.2.2 4 := by
  exact deriveLower b62.1 b62.2.2.2 stock62 cuts62 3
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower24) lower38) lower60) lower58)
    (by unfold cuts62; decide +kernel) checks62

private def stock79 : List Word := [0xaaaa000000000000aaaa, 0xcccc000000000000cccc, 0xf0f0000000000000f0f0, 0xff00000000000000ff00, 0xffff0000000000000000]
private def b79 : Bound := (0xffff000000000000ffff, stock79, 5, 0xfffc000000000000aa00)
private def cuts79 : List Bound := [b75, b77, b78, b70, b9]
private theorem lower79 : Lower b79.1 stock79 b79.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xffdfef5f7cfcf1fddbe74f5cbc70df9f6e5d78f4e1dd9b664d58b4607eddeb576cdcb17cd9e3474c9c305e9d6a5568d4a15c996245489420bf5eed5b74ecd1bd5ae54b54ac509f1e6c5970e4c19d1a644950a4403e5ce95364cc913c58e143448c101e1c685160c4811c186041408400) lower47
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock87 : List Word := [0xaa00aa0000000000aa00aa, 0xcc00cc0000000000cc00cc, 0xf000f00000000000f000f0, 0xff00000000000000ff0000, 0xff00ff0000000000000000]
private def b87 : Bound := (0xff00ff0000000000ff00ff, stock87, 5, 0xff00fc0000000000aa0000)
private def cuts87 : List Bound := [b83, b85, b86, b70, b17]
private theorem lower87 : Lower b87.1 stock87 b87.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xffbfeedf7afce9fdbbe6cf5abc68ef9fae5e78f8e1ed9ba64e58b8607ebdead76adca97cb9e2c74a9c286e9daa5668d8a16c99a246489820bf3eecdb72ecc9bd3ae4cb52ac48af1eac5a70e8c1ad1aa44a50a8403e3ce8d362cc893c38e0c3428c082e1ca85260c8812c18a042408800) lower47
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock91 : List Word := [0xa0a0a0a000000000a0a0a0a, 0xc0c0c0c000000000c0c0c0c, 0xf000f00000000000f000f00, 0xf0f0000000000000f0f0000, 0xf0f0f0f0000000000000000]
private def b91 : Bound := (0xf0f0f0f000000000f0f0f0f, stock91, 7, 0xf0f0f0c000000000f0a0a00)
private def cuts91 : List Bound := [b89, b90, b25, b75, b83]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks91 : treeBlock 0 (2 ^ stock91.length) (fun token =>
    closes b91.1 b91.2.2.2 cuts91 6 (rootState stock91 6 token)) = true := by
  decide +kernel
private theorem lower91 : Lower b91.1 stock91 b91.2.2.2 7 := by
  exact deriveLower b91.1 b91.2.2.2 stock91 cuts91 6
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower83) lower75) lower25) lower90) lower89)
    (by unfold cuts91; decide +kernel) checks91

private def stock93 : List Word := [0x222222220000000022222222, 0x303030300000000030303030, 0x330033000000000033003300, 0x333300000000000033330000, 0x333333330000000000000000]
private def b93 : Bound := (0x333333330000000033333333, stock93, 7, 0x333333300000000033222200)
private def cuts93 : List Bound := [b89, b92, b25, b77, b85]
private theorem lower93 : Lower b93.1 stock93 b93.2.2.2 7 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbdfafbf3cf8efdb9f2ebd38f0dfbb5eadbb34e8cf9b1e2cb930e0bf7addabb72cd8af5a9d2ab528d09f3a5ca9b324c88f1a1c28b120c07ef9dba7af1cb86ed99b26ad18b05eb95aa5ab14a84e991a24a910a03e78d9a3a70c982e589922a508901e3858a1a304880e181820a10080) lower91
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock94 : List Word := [0x444444440000000044444444, 0x505050500000000050505050, 0x550055000000000055005500, 0x555500000000000055550000, 0x555555550000000000000000]
private def b94 : Bound := (0x555555550000000055555555, stock94, 6, 0x555555540000000055000000)
private def cuts94 : List Bound := [b90, b92, b78, b86, b24]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks94 : treeBlock 0 (2 ^ stock94.length) (fun token =>
    closes b94.1 b94.2.2.2 cuts94 5 (rootState stock94 5 token)) = true := by
  decide +kernel
private theorem lower94 : Lower b94.1 stock94 b94.2.2.2 6 := by
  exact deriveLower b94.1 b94.2.2.2 stock94 cuts94 5
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower24) lower86) lower78) lower92) lower90)
    (by unfold cuts94; decide +kernel) checks94

private def stock103 : List Word := [0xaa000000aa000000aa000000aa, 0xcc000000cc000000cc000000cc, 0xf0000000f0000000f0000000f0, 0xff00000000000000ff00000000, 0xff000000ff0000000000000000]
private def b103 : Bound := (0xff000000ff000000ff000000ff, stock103, 5, 0xfe000000fc000000fe00000000)
private def cuts103 : List Bound := [b99, b101, b39, b102, b70]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks103 : treeBlock 0 (2 ^ stock103.length) (fun token =>
    closes b103.1 b103.2.2.2 cuts103 4 (rootState stock103 4 token)) = true := by
  decide +kernel
private theorem lower103 : Lower b103.1 stock103 b103.2.2.2 5 := by
  exact deriveLower b103.1 b103.2.2.2 stock103 cuts103 4
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower70) lower102) lower39) lower101) lower99)
    (by unfold cuts103; decide +kernel) checks103

private def stock107 : List Word := [0xa0a00000a0a00000a0a00000a0a, 0xc0c00000c0c00000c0c00000c0c, 0xf0000000f0000000f0000000f00, 0xf0f0000000000000f0f00000000, 0xf0f00000f0f0000000000000000]
private def b107 : Bound := (0xf0f00000f0f00000f0f00000f0f, stock107, 7, 0xf0e00000f0c00000e0e00000a00)
private def cuts107 : List Bound := [b43, b75, b99, b105, b106]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks107 : treeBlock 0 (2 ^ stock107.length) (fun token =>
    closes b107.1 b107.2.2.2 cuts107 6 (rootState stock107 6 token)) = true := by
  decide +kernel
private theorem lower107 : Lower b107.1 stock107 b107.2.2.2 7 := by
  exact deriveLower b107.1 b107.2.2.2 stock107 cuts107 6
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower106) lower105) lower99) lower75) lower43)
    (by unfold cuts107; decide +kernel) checks107

private def stock109 : List Word := [0x2222000022220000222200002222, 0x3030000030300000303000003030, 0x3300000033000000330000003300, 0x3333000000000000333300000000, 0x3333000033330000000000000000]
private def b109 : Bound := (0x3333000033330000333300003333, stock109, 7, 0x3332000033300000323200002200)
private def cuts109 : List Bound := [b45, b77, b101, b105, b108]
private theorem lower109 : Lower b109.1 stock109 b109.2.2.2 7 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbdfafbf3cf8efdb9f2ebd38f0dfbb5eadbb34e8cf9b1e2cb930e0bf7addabb72cd8af5a9d2ab528d09f3a5ca9b324c88f1a1c28b120c07ef9dba7af1cb86ed99b26ad18b05eb95aa5ab14a84e991a24a910a03e78d9a3a70c982e589922a508901e3858a1a304880e181820a10080) lower107
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock110 : List Word := [0x4444000044440000444400004444, 0x5050000050500000505000005050, 0x5500000055000000550000005500, 0x5555000000000000555500000000, 0x5555000055550000000000000000]
private def b110 : Bound := (0x5555000055550000555500005555, stock110, 5, 0x5554000055540000545400000000)
private def cuts110 : List Bound := [b106, b108, b78, b102, b38]
private theorem lower110 : Lower b110.1 stock110 b110.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xffdfef5f7cfcf1fddbe74f5cbc70df9f6e5d78f4e1dd9b664d58b4607eddeb576cdcb17cd9e3474c9c305e9d6a5568d4a15c996245489420bf5eed5b74ecd1bd5ae54b54ac509f1e6c5970e4c19d1a644950a4403e5ce95364cc913c58e143448c101e1c685160c4811c186041408400) lower103
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock115 : List Word := [0xa000a000a000a000a000a000a000a, 0xc000c000c000c000c000c000c000c, 0xf0000000f0000000f0000000f0000, 0xf000f00000000000f000f00000000, 0xf000f000f000f0000000000000000]
private def b115 : Bound := (0xf000f000f000f000f000f000f000f, stock115, 7, 0xf000e000f000c000e000e000a0000)
private def cuts115 : List Bound := [b51, b83, b99, b113, b114]
private theorem lower115 : Lower b115.1 stock115 b115.2.2.2 7 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcf7ebcf8dfbb6ecd7ab4e8efdbaf4e7cb8f0cf9b2e4c78b0e0bf7aedcb76acd89f3a6cc972a4c8af5aad4a74a8d08f1a2c4870a0c07ef9ebc76e9cb85eb96ac56a94a86ed9ab466c98b04e992a446890a03e78e9c3668c981e3868c16284882e58a9426488900e182840608080) lower107
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock117 : List Word := [0x220022002200220022002200220022, 0x300030003000300030003000300030, 0x330000003300000033000000330000, 0x330033000000000033003300000000, 0x330033003300330000000000000000]
private def b117 : Bound := (0x330033003300330033003300330033, stock117, 7, 0x330032003300300032003200220000)
private def cuts117 : List Bound := [b53, b85, b101, b113, b116]
private theorem lower117 : Lower b117.1 stock117 b117.2.2.2 7 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbdfafbf3cf8dfbb5eadbb34e8efdb9f2ebd38f0cf9b1e2cb930e0bf7addabb72cd89f3a5ca9b324c8af5a9d2ab528d08f1a1c28b120c07ef9dba7af1cb85eb95aa5ab14a86ed99b26ad18b04e991a24a910a03e78d9a3a70c981e3858a1a304882e589922a508900e181820a10080) lower107
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock118 : List Word := [0x440044004400440044004400440044, 0x500050005000500050005000500050, 0x550000005500000055000000550000, 0x550055000000000055005500000000, 0x550055005500550000000000000000]
private def b118 : Bound := (0x550055005500550055005500550055, stock118, 5, 0x550054005500540054005400000000)
private def cuts118 : List Bound := [b114, b116, b86, b102, b38]
private theorem lower118 : Lower b118.1 stock118 b118.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xffbfeedf7afce9fdbbe6cf5abc68ef9fae5e78f8e1ed9ba64e58b8607ebdead76adca97cb9e2c74a9c286e9daa5668d8a16c99a246489820bf3eecdb72ecc9bd3ae4cb52ac48af1eac5a70e8c1ad1aa44a50a8403e3ce8d362cc893c38e0c3428c082e1ca85260c8812c18a042408800) lower103
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock121 : List Word := [0x2020202020202020202020202020202, 0x3000300030003000300030003000300, 0x3030000030300000303000003030000, 0x3030303000000000303030300000000, 0x3030303030303030000000000000000]
private def b121 : Bound := (0x3030303030303030303030303030303, stock121, 7, 0x3030302030303000302020203020200)
private def cuts121 : List Bound := [b57, b89, b88, b105, b113]
private theorem lower121 : Lower b121.1 stock121 b121.2.2.2 7 :=
  lowerRelabelMasked (rowSelectPacked 0xfefef9ffaf6e9deedeb97ead6a95debe78fdab668dce9e387ca96285f6eed9bf2e6c99e6ce993e2c6891d6ae58bd2a6489c68e183c286081fcfaf1ef8f2e1cecdab16e8d2a14dcba70ed8b260ccc9a306c892204f4ead1af0e2c18e4ca912e0c2810d4aa50ad0a2408c48a102c082000) lower91
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock122 : List Word := [0x4040404040404040404040404040404, 0x5000500050005000500050005000500, 0x5050000050500000505000005050000, 0x5050505000000000505050500000000, 0x5050505050505050000000000000000]
private def b122 : Bound := (0x5050505050505050505050505050505, stock122, 7, 0x5050504050505040504040405000000)
private def cuts122 : List Bound := [b90, b88, b106, b114, b58]
private theorem lower122 : Lower b122.1 stock122 b122.2.2.2 7 :=
  lowerRelabelMasked (rowSelectPacked 0xfefef9ffcfaf1eeedeb97ecdab16debe78fdcba70ece9e387cc9a306faf6e9df8f2e1cead6a95e8d2a14dab668dd8b260cca96285c892204f6eed9bf4ead1ae6ce993e4ca912d6ae58bd4aa50ac68e183c48a102f2e6c99f0e2c18e2c6891e0c2810d2a6489d0a2408c286081c082000) lower59
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock124 : List Word := [0x10101010101010101010101010101010, 0x11001100110011001100110011001100, 0x11110000111100001111000011110000, 0x11111111000000001111111100000000, 0x11111111111111110000000000000000]
private def b124 : Bound := (0x11111111111111111111111111111111, stock124, 7, 0x11111110111111101110101011000000)
private def cuts124 : List Bound := [b92, b88, b108, b116, b60]
private theorem lower124 : Lower b124.1 stock124 b124.2.2.2 7 :=
  lowerRelabelMasked (rowSelectPacked 0xfefef9ffcfaf1eeedeb97ecdab16debe78fdcba70ece9e387cc9a306f6eed9bf4ead1ae6ce993e4ca912d6ae58bd4aa50ac68e183c48a102faf6e9df8f2e1cead6a95e8d2a14dab668dd8b260cca96285c892204f2e6c99f0e2c18e2c6891e0c2810d2a6489d0a2408c286081c082000) lower59
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock63 : List Word := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
private def b63 : Bound := (0xffffffffffffffff, stock63, 8, 0xfffefefeffaaaa00)
private def cuts63 : List Bound := [b59, b61, b47, b55, b25, b62]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks63 : treeBlock 0 (2 ^ stock63.length) (fun token =>
    closes b63.1 b63.2.2.2 cuts63 7 (rootState stock63 7 token)) = true := by
  decide +kernel
private theorem lower63 : Lower b63.1 stock63 b63.2.2.2 8 := by
  exact deriveLower b63.1 b63.2.2.2 stock63 cuts63 7
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower62) lower25) lower55) lower47) lower61) lower59)
    (by unfold cuts63; decide +kernel) checks63

private def stock95 : List Word := [0xaaaaaaaa00000000aaaaaaaa, 0xcccccccc00000000cccccccc, 0xf0f0f0f000000000f0f0f0f0, 0xff00ff0000000000ff00ff00, 0xffff000000000000ffff0000, 0xffffffff0000000000000000]
private def b95 : Bound := (0xffffffff00000000ffffffff, stock95, 8, 0xfffffffc00000000ffaaaa00)
private def cuts95 : List Bound := [b91, b93, b94, b79, b87, b25]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks95 : treeBlock 0 (2 ^ stock95.length) (fun token =>
    closes b95.1 b95.2.2.2 cuts95 7 (rootState stock95 7 token)) = true := by
  decide +kernel
private theorem lower95 : Lower b95.1 stock95 b95.2.2.2 8 := by
  exact deriveLower b95.1 b95.2.2.2 stock95 cuts95 7
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower25) lower87) lower79) lower94) lower93) lower91)
    (by unfold cuts95; decide +kernel) checks95

private def stock111 : List Word := [0xaaaa0000aaaa0000aaaa0000aaaa, 0xcccc0000cccc0000cccc0000cccc, 0xf0f00000f0f00000f0f00000f0f0, 0xff000000ff000000ff000000ff00, 0xffff000000000000ffff00000000, 0xffff0000ffff0000000000000000]
private def b111 : Bound := (0xffff0000ffff0000ffff0000ffff, stock111, 8, 0xfffe0000fffc0000fefe0000aa00)
private def cuts111 : List Bound := [b107, b109, b47, b79, b103, b110]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks111 : treeBlock 0 (2 ^ stock111.length) (fun token =>
    closes b111.1 b111.2.2.2 cuts111 7 (rootState stock111 7 token)) = true := by
  decide +kernel
private theorem lower111 : Lower b111.1 stock111 b111.2.2.2 8 := by
  exact deriveLower b111.1 b111.2.2.2 stock111 cuts111 7
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower110) lower103) lower79) lower47) lower109) lower107)
    (by unfold cuts111; decide +kernel) checks111

private def stock119 : List Word := [0xaa00aa00aa00aa00aa00aa00aa00aa, 0xcc00cc00cc00cc00cc00cc00cc00cc, 0xf000f000f000f000f000f000f000f0, 0xff000000ff000000ff000000ff0000, 0xff00ff0000000000ff00ff00000000, 0xff00ff00ff00ff0000000000000000]
private def b119 : Bound := (0xff00ff00ff00ff00ff00ff00ff00ff, stock119, 8, 0xff00fe00ff00fc00fe00fe00aa0000)
private def cuts119 : List Bound := [b115, b117, b55, b87, b103, b118]
private theorem lower119 : Lower b119.1 stock119 b119.2.2.2 8 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcf7ebcf8dfbb6ecd7ab4e8efdbaf4e7cb8f0cf9b2e4c78b0e0bf7aedcb76acd89f3a6cc972a4c8af5aad4a74a8d08f1a2c4870a0c07ef9ebc76e9cb85eb96ac56a94a86ed9ab466c98b04e992a446890a03e78e9c3668c981e3868c16284882e58a9426488900e182840608080) lower111
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock123 : List Word := [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 0xf000f000f000f000f000f000f000f00, 0xf0f00000f0f00000f0f00000f0f0000, 0xf0f0f0f000000000f0f0f0f00000000, 0xf0f0f0f0f0f0f0f0000000000000000]
private def b123 : Bound := (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, stock123, 10, 0xf0f0f0e0f0f0f0c0f0e0e0e0f0a0a00)
private def cuts123 : List Bound := [b59, b91, b107, b115, b121, b122]
private def c123Index : Nat := 0x45208a41148225244a0894106e20923f4f7e80fd01fa03ec47d80fb01f413e807d00ef59de03b447680ed01da03b40750cea01d403a807500e985ca4b9407280e501ca039407188df21be037a16d50da819ccb3046600cc0198033006508c2bd85030a06140c09181030205fc4baa97502ea05d40b891700ad465a80a8695002a005400a80150029845300a39547028e05106a20144028425080a101410a7a44f40935d26024a147cc8f81193232046408c81180a30044108801100220042ca85810b0216042c0831506020c041808301060204440427d98fa09f403d887a08ef29de03b447680eb11d603a067400e801ce139c07380e511ca038c46e1cdb09b6036446c80d901ac3344a5ce0b7116262c025784af015642ac05298a50144328805084a10140128004c20980130025c249909301187230045848b0116022c045808b0114122804120820102120403f887f00fe01fc03f807f00f261e023b087220e401c8038847008e001c0038006748cc1190431846300c6018c031046108c2018022b285600aa115402a044f286ba0c4818802d205a00b4016802d005a00b40149029005200a401480290052009480b3c01a8001
private def c123Edges : Nat := 0x5ca04eb98084730078e500941b25093de9f5cbd12e2627cfac4eb8d887643108e761c9c8c38dc129d38193a9a1a79b034338c66e640cd4b918a15a04f2680867100dc7d01aae00291c003a27804c0d004414f44add8705ba4b00a310412f449398875b30e38b4a1fa49373812594c990cd731bba462b2d8c40560d0c9919bb1632b13863e048c52dc0273ba0363740546e0048cb6261b2c4881e4a16b3d3e457a71bcf4536de8916313b6c4a7bb4943739282eba4b26c3279b4643338c826c18acd731015204f3580862281056c0158d801f0b0022038020cb4a61a8948afcc80df8cd23f7a719ef448ad89c65a5043f0208560113280993fb138cc624996c42325871ba253a7432753634e0f406a150044c602718a04231006c61804a3a7a7450c4eafd26b4a0d38bf1951280350e803a140044c031a706c4edd929cdfa50a833274ec34e2fc6841280d52500ec1d250945e9f5d3d138c6279a6c4334987068a53e824a71a094333928466a4dcc849b18e92d3092593a9938c132153a34e2f866c53813c93021ad40372f40561c80a42400880c008811e88dc30e0b849600862082de885c30e0b7496006620841e892ab10cbb61c7209436e926edb24b2903219746372e4c565b1880a61a19243375a0656340c7c0218a5640426cc06c5980a8b200f55ec402bc668403160ae62a4ccc4c5c52b1b125307132c4c464c198068b100a06200e08ef582a9ea90e31301c0084ca64c1012b05425526432604e35807c0500d0040b4928963250aad89f24b13619620d4cc386c129ec32537614a0f4e9376b125858193c86326cc2641a9cc6e5698acac31015634f12469a548cdda719594e31f298628b080a86100f03201228809cd080d8a101514001e89d89c4da5058349a92831d05c0243fb1309c624136c4011deb04c3d501600807e94c2552904a190015008411250291e9f24bd38a37a293ef44db929ecf250d824a0b3a93566525937193c9e321904641274c6a4d18ac9931012e34f258686228d059319592631f2486280a00487331a10095823d2a93025307231a2c005819c0983fa5308d4a41069401d0c983b19015e01a1120342224a1203134804a690e94a9812823898a8401a68c002a901e9c423d107f4a09069350fc6824031387f6210fcc380f466a3301387b0270f40421e406c3c00785f014452c4e1d12823b24d43a18e8c804e1780542e80a0733244b86405700983181025c3200b801c1d1884392538713270c404e16c0502025606f4aa07e94c1b52901ea5006b49e24a32818c65032b1221b4a02b864c18cc8110b105604a68ce941198c54320cd86219503e01d1706382e99005f31a0ba936570c842e0d09606272bc942180c9c2f0d085b19441f25094de9e483d108e627918c4322d87045253c864a710a94320928440a4dc7d49b0f892d1dd2583a99087031b0dc34f1b0686350cdc691958723291a06283081385a01b05c34008c0982399605832a43064c0b46800c0160220260700081580482019605432a0523280840981f9930523240746280ac698140ca01702007a640140c78150d004431e09804012e4a023b1344a625430c4150129a2019352719504e31e0e008023bd38467a227e9410fcc82222539424a10849360dd258930d082619b04004e108c901e0100404a707e9420f927a1ea4d83b49607464249466c0f81383801406e9480d80981a0138330210640410c40809800d83001503c0400b86900e81002d6272569410acc820e01381b02002c0340ad2841524d82932705064209c69c130cf42519b03404e0540840f00d0231a403a03406c0380f00f01d4a003634006189a113105214a08426410806628f8ca81f18f0380364680540d00781600e02c334061e9c8ba4d41731aa2a02a05403d08c940577a78aaf4454d89ea8b10d4e61c0a694f14528627a4dc4e49609a64f124c9c24190c4532108663d504c6e9c98d84131587262a0d4c421798802c1a12483360906540c81381402140af444318700624b00531040af4442d87005a4b004310018f4402d8700524b00331000af4401187081a4b003310024f440458860830e10f4a1a1c93742525807990c0e31b81a62b024c40040d0c0719ba0c32b01863e010c52017a2426c43ad5871aca50fbc49bbbe92c964c875e18dce13159be620a446866a8cddbc19597831f2d462852810c9101bab202b16403e09804c0100400003f
private def c123Links : DagLinks :=
  dagLookupLinks c123Index c123Edges 15 5 13 8 2 6
private def c123Data : Forest := fun i => decodeNode 8 21 0x61cf1007b94025cac38e219bf100df88c560292ce031000bd1758055b8012dc7a26b190f59891b262bd63106b010f5866e02948d4621deb0e2f529f7a943bd7a267a50af526f7ac49c96216481332987192936bd496de813b0c08586036c300961a4b2f4c857a634c01a15f8cdaf40577a31f0161c5b18ded8c576cc38b74965b9882d862803251a601559007aca4a14c64fa619a57b152b8c574c620a61a7d33d52a866f4c954a818fd30c529808602f4f927a2c9013a800554001ea07a249190e48c6b24c489b6204d98ae48c4124f54981a7c90d0e49291286409418fc90c524806e02f445a4aa47b13d692911ac435a61c2d253d6806913250874a543a53969286b4f448349ac1a5096926eb4c4e7e6213f30e1f926cb492d5a0273c0109e006cf001e784962d24d5d8c84b4c427132439a539c4c9ce26365a4aa378d3d69290da3435a49e358cdd68656b43145a4a0b118a989890ca33662320318ca98809cb464e5b31a2f8d096d26cb83425c1942d80d96803e02654587a78a009159e8828654544a78a1921492862863c5049b8a24b050c9e280404c92825312928c9c28643147a7233d1118c842894e4431e8a192108c562894e3a4a11d24f4e926c740403c4961d1908e8c5428028384a41b0130d8c422804e30021180104c00806002a303100a0d20b989c5a342144a112a4d894c9c4a642251a7128cf49466c4a32a141a411b10468c82343311a18f0d00f0792803a0361a1a00d80786809c28f4e1531a8a8cd05803c2a0421400980bd100988604c38023218118dc08c5604f440a61c0524b028c40043430219b810c7c09e8806c3803310018c50080100203f00 i
private def c123Sample : DagSample := (0x30140825018140505009140145001940c04820920604814120244805120064830060821818060501809060141801860c04220908604214108244205108064230088822218088502209088142201888c02120884602114084242105084062130044821118044501109044141101844c009208246009140242409050240609, 56)
private def c123Tags := dagTraceTags b123.1 56
  (dagTagBases stock123 0xfffc07f00000000000000fffc000fe03f800003f8001fff80000007f000007ffe00000000000001fffff 0xc183060c183060b162c58b162c582850a142850a14142850a142850a0e1c3870e1c38742850a142850a1 56) 9 c123Data
private def c123States := dagTrace b123.1 stock123 9 c123Data
private def c123MoveCert : List (DagMoveRecord 128) := [
  ([([(0xff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff0000, 8)])], rowSelectPacked 0xfffbefcf7ebcf8dfbb6ecd7ab4e8efdbaf4e7cb8f0cf9b2e4c78b0e0bf7aedcb76acd89f3a6cc972a4c8af5aad4a74a8d08f1a2c4870a0c07ef9ebc76e9cb85eb96ac56a94a86ed9ab466c98b04e992a446890a03e78e9c3668c981e3868c16284882e58a9426488900e182840608080, rowSelectPacked 0xfffbefcf7ebcf8dfbb6ecd7ab4e8efdbaf4e7cb8f0cf9b2e4c78b0e0bf7aedcb76acd89f3a6cc972a4c8af5aad4a74a8d08f1a2c4870a0c07ef9ebc76e9cb85eb96ac56a94a86ed9ab466c98b04e992a446890a03e78e9c3668c981e3868c16284882e58a9426488900e182840608080),
  ([([(0x88888888222222224444444411111111, 0), (0x888888880000000044444444, 30), (0x2222222200000000, 33), (0x8888888822222222, 63), (0x88888888, 93)], [(0x11111111000000000000000000000000, 93), (0x44444444111111110000000000000000, 63), (0x444444440000000000000000, 33), (0x22222222000000001111111100000000, 30)])], rowSelectPacked 0xfefef9ff6eed9beedeb97e6ce993debe78fd6ae58bce9e387c68e183faf6e9df2e6c99ead6a95e2c6891dab668dd2a6489ca96285c286081fcfaf1ef4ead1aecdab16e4ca912dcba70ed4aa50acc9a306c48a102f8f2e1cf0e2c18e8d2a14e0c2810d8b260cd0a2408c892204c082000, rowSelectPacked 0xfefef9ff6eed9beedeb97e6ce993debe78fd6ae58bce9e387c68e183faf6e9df2e6c99ead6a95e2c6891dab668dd2a6489ca96285c286081fcfaf1ef4ead1aecdab16e4ca912dcba70ed4aa50acc9a306c48a102f8f2e1cf0e2c18e8d2a14e0c2810d8b260cd0a2408c892204c082000),
  ([([(0x88000088220000224400004411000011, 0), (0x8800000022000000440000001100, 8), (0x8800000000000000440000, 22), (0x22000000000000, 25), (0x880000880000000044000044, 30), (0x2200002200000000, 33), (0x88000000000000004400, 38), (0x220000000000, 41), (0x88000000220000, 55), (0x8800008822000022, 63), (0x880000002200, 71), (0x880000, 85), (0x88000088, 93), (0x8800, 101)], [(0x110000000000000000000000000000, 101), (0x11000011000000000000000000000000, 93), (0x1100000000000000000000000000, 85), (0x440000001100000000000000000000, 71), (0x44000044110000110000000000000000, 63), (0x4400000011000000000000000000, 55), (0x4400000000000000000000, 41), (0x220000000000000011000000000000, 38), (0x440000440000000000000000, 33), (0x22000022000000001100001100000000, 30), (0x44000000000000000000, 25), (0x2200000000000000110000000000, 22), (0x880000002200000044000000110000, 8)])], rowSelectPacked 0xfefef9ff6eed9bdebe78fd6ae58beedeb97e6ce993ce9e387c68e183faf6e9df2e6c99dab668dd2a6489ead6a95e2c6891ca96285c286081fcfaf1ef4ead1adcba70ed4aa50aecdab16e4ca912cc9a306c48a102f8f2e1cf0e2c18d8b260cd0a2408e8d2a14e0c2810c892204c082000, rowSelectPacked 0xfefef9ff6eed9bdebe78fd6ae58beedeb97e6ce993ce9e387c68e183faf6e9df2e6c99dab668dd2a6489ead6a95e2c6891ca96285c286081fcfaf1ef4ead1adcba70ed4aa50aecdab16e4ca912cc9a306c48a102f8f2e1cf0e2c18d8b260cd0a2408e8d2a14e0c2810c892204c082000)]
private def c123Moves := dagMoves c123MoveCert

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Autos : DagMovesOK b123.1 b123.2.2.2 128 c123Moves :=
  dagMovesOfCheck (by decide +kernel)

private def c123Check := dagCheckNode b123.1 b123.2.2.2 none (dagKnownCloses b123.2.2.2 cuts123) 232
  c123States c123Moves c123Links c123Sample c123Tags

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Roots :
    dagCheckRoots b123.1 b123.2.2.2 none (dagKnownCloses b123.2.2.2 cuts123) []
      (dagRef 232 c123States c123Moves c123Links 0) stock123 9 = true := by
  decide +kernel

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block0 : treeBlock 0 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block6 : treeBlock 6 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block12 : treeBlock 12 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block18 : treeBlock 18 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block24 : treeBlock 24 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block30 : treeBlock 30 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block36 : treeBlock 36 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block42 : treeBlock 42 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block48 : treeBlock 48 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block54 : treeBlock 54 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block60 : treeBlock 60 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block66 : treeBlock 66 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block72 : treeBlock 72 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block78 : treeBlock 78 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block84 : treeBlock 84 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block90 : treeBlock 90 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block96 : treeBlock 96 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block102 : treeBlock 102 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block108 : treeBlock 108 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block114 : treeBlock 114 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block120 : treeBlock 120 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block126 : treeBlock 126 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block132 : treeBlock 132 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block138 : treeBlock 138 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block144 : treeBlock 144 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block150 : treeBlock 150 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block156 : treeBlock 156 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block162 : treeBlock 162 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block168 : treeBlock 168 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block174 : treeBlock 174 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block180 : treeBlock 180 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block186 : treeBlock 186 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block192 : treeBlock 192 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block198 : treeBlock 198 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block204 : treeBlock 204 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block210 : treeBlock 210 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block216 : treeBlock 216 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block222 : treeBlock 222 6 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block228 : treeBlock 228 4 c123Check = true := by decide +kernel

private theorem c123Checked : treeBlock 0 232 c123Check = true :=
  (@treeBlock_merge 0 114 118 c123Check
    (@treeBlock_merge 0 54 60 c123Check
    (@treeBlock_merge 0 24 30 c123Check
    (@treeBlock_merge 0 12 12 c123Check
    (@treeBlock_merge 0 6 6 c123Check
    c123Block0
    c123Block6)
    (@treeBlock_merge 12 6 6 c123Check
    c123Block12
    c123Block18))
    (@treeBlock_merge 24 12 18 c123Check
    (@treeBlock_merge 24 6 6 c123Check
    c123Block24
    c123Block30)
    (@treeBlock_merge 36 6 12 c123Check
    c123Block36
    (@treeBlock_merge 42 6 6 c123Check
    c123Block42
    c123Block48))))
    (@treeBlock_merge 54 30 30 c123Check
    (@treeBlock_merge 54 12 18 c123Check
    (@treeBlock_merge 54 6 6 c123Check
    c123Block54
    c123Block60)
    (@treeBlock_merge 66 6 12 c123Check
    c123Block66
    (@treeBlock_merge 72 6 6 c123Check
    c123Block72
    c123Block78)))
    (@treeBlock_merge 84 12 18 c123Check
    (@treeBlock_merge 84 6 6 c123Check
    c123Block84
    c123Block90)
    (@treeBlock_merge 96 6 12 c123Check
    c123Block96
    (@treeBlock_merge 102 6 6 c123Check
    c123Block102
    c123Block108)))))
    (@treeBlock_merge 114 60 58 c123Check
    (@treeBlock_merge 114 30 30 c123Check
    (@treeBlock_merge 114 12 18 c123Check
    (@treeBlock_merge 114 6 6 c123Check
    c123Block114
    c123Block120)
    (@treeBlock_merge 126 6 12 c123Check
    c123Block126
    (@treeBlock_merge 132 6 6 c123Check
    c123Block132
    c123Block138)))
    (@treeBlock_merge 144 12 18 c123Check
    (@treeBlock_merge 144 6 6 c123Check
    c123Block144
    c123Block150)
    (@treeBlock_merge 156 6 12 c123Check
    c123Block156
    (@treeBlock_merge 162 6 6 c123Check
    c123Block162
    c123Block168))))
    (@treeBlock_merge 174 30 28 c123Check
    (@treeBlock_merge 174 12 18 c123Check
    (@treeBlock_merge 174 6 6 c123Check
    c123Block174
    c123Block180)
    (@treeBlock_merge 186 6 12 c123Check
    c123Block186
    (@treeBlock_merge 192 6 6 c123Check
    c123Block192
    c123Block198)))
    (@treeBlock_merge 204 12 16 c123Check
    (@treeBlock_merge 204 6 6 c123Check
    c123Block204
    c123Block210)
    (@treeBlock_merge 216 6 10 c123Check
    c123Block216
    (@treeBlock_merge 222 6 4 c123Check
    c123Block222
    c123Block228))))))

private theorem lower123 : Lower b123.1 stock123 b123.2.2.2 10 := by
  exact lowerDag (width := 128) (chart := none)
    (by unfold Masked; decide +kernel) (by unfold Masked; decide +kernel)
    (by unfold properWord; decide +kernel) (by simp) c123Autos
    (by unfold Masked; decide +kernel) (by decide +kernel) (by decide +kernel)
    (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower122) lower121) lower115) lower107) lower91) lower59) (by decide +kernel)
    c123Roots c123Checked

private def stock125 : List Word := [0x22222222222222222222222222222222, 0x30303030303030303030303030303030, 0x33003300330033003300330033003300, 0x33330000333300003333000033330000, 0x33333333000000003333333300000000, 0x33333333333333330000000000000000]
private def b125 : Bound := (0x33333333333333333333333333333333, stock125, 10, 0x33333332333333303332323233222200)
private def cuts125 : List Bound := [b61, b93, b109, b117, b121, b124]
private theorem lower125 : Lower b125.1 stock125 b125.2.2.2 10 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbdfafbf3cf8efdb9f2ebd38f0dfbb5eadbb34e8cf9b1e2cb930e0bf7addabb72cd8af5a9d2ab528d09f3a5ca9b324c88f1a1c28b120c07ef9dba7af1cb86ed99b26ad18b05eb95aa5ab14a84e991a24a910a03e78d9a3a70c982e589922a508901e3858a1a304880e181820a10080) lower123
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock126 : List Word := [0x44444444444444444444444444444444, 0x50505050505050505050505050505050, 0x55005500550055005500550055005500, 0x55550000555500005555000055550000, 0x55555555000000005555555500000000, 0x55555555555555550000000000000000]
private def b126 : Bound := (0x55555555555555555555555555555555, stock126, 8, 0x55555554555555545554545455000000)
private def cuts126 : List Bound := [b122, b124, b94, b110, b118, b62]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks126 : treeBlock 0 (2 ^ stock126.length) (fun token =>
    closes b126.1 b126.2.2.2 cuts126 7 (rootState stock126 7 token)) = true := by
  decide +kernel
private theorem lower126 : Lower b126.1 stock126 b126.2.2.2 8 := by
  exact deriveLower b126.1 b126.2.2.2 stock126 cuts126 7
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower62) lower118) lower110) lower94) lower124) lower122)
    (by unfold cuts126; decide +kernel) checks126

private def stock127 : List Word := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000]
private def b127 : Bound := (0xffffffffffffffffffffffffffffffff, stock127, 11, 0xfffffffefffffffcfffefefeffaaaa00)
private def cuts127 : List Bound := [b123, b125, b63, b95, b111, b119, b126]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks127 : treeBlock 0 (2 ^ stock127.length) (fun token =>
    closes b127.1 b127.2.2.2 cuts127 10 (rootState stock127 10 token)) = true := by
  decide +kernel
private theorem lower127 : Lower b127.1 stock127 b127.2.2.2 11 := by
  exact deriveLower b127.1 b127.2.2.2 stock127 cuts127 10
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower126) lower119) lower111) lower95) lower63) lower125) lower123)
    (by unfold cuts127; decide +kernel) checks127

open PEqualNP.CircuitLowerBounds

def endpoints : List ℕ := [0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6]

def graph (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < endpoints.length / 2, (List.ofFn x).getD (endpoints.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (endpoints.getD (2 * i + 1) 0) false = true)

def upper : Circuit :=
  ⟨[⟨.and, [0, 5]⟩, ⟨.or, [7, 1]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [11, 9]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [13, 12]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [10, 15]⟩, ⟨.or, [16, 14]⟩], 17⟩

theorem upper_legal :
    ∀ g ∈ upper.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g h
  simp only [upper, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_correct : ∀ x, upper.eval (List.ofFn x) = graph x := by
  decide +kernel

private theorem lowerAll (s : ℕ) (h : PEqualNP.MetaComplexity.HasCircuitSize 7 graph s) : 11 ≤ s := by
  let raw : List (BitVec 128) :=
    [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc,
      0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00,
      0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000,
      0xffffffffffffffff0000000000000000]
  let target : BitVec 128 := 0xfffffffefffffffcfffefefeffaaaa00
  have bounded : Lower (fullMask 128) (raw.map BitVec.toNat) target.toNat 11 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) lower127
  exact hcsLower (n := 7) raw target 11 graph (by decide +kernel) (by decide +kernel) bounded s h

end PEqualNP.Outside.L_meta_11257_aux

open PEqualNP.Outside.L_meta_11257_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_11257 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates out legal _ computes
  have fan : PEqualNP.MetaComplexity.FanInTwo ⟨gates, out⟩ := by
    intro g hg
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using legal g hg
  have h : PEqualNP.MetaComplexity.HasCircuitSize 7 graph gates.length :=
    ⟨⟨gates, out⟩, fan, le_rfl, computes⟩
  exact ⟨upper.gates, upper.output, upper_legal,
    le_trans (show upper.gates.length ≤ 11 by decide) (lowerAll _ h), upper_correct⟩
