import PEqualNP.Defs

-- The live-wire checker is adapted from the accepted L-meta-8465 proof by odinfree.
namespace PEqualNP.Outside.L_meta_10576_aux

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
private def stock5 : List Word := [0x22, 0x30]
private def b5 : Bound := (0x33, stock5, 1, 0x20)
private def cuts5 : List Bound := []
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks5 : treeBlock 0 (2 ^ stock5.length) (fun token =>
    closes b5.1 b5.2.2.2 cuts5 0 (rootState stock5 0 token)) = true := by
  decide +kernel
private theorem lower5 : Lower b5.1 stock5 b5.2.2.2 1 := by
  exact deriveLower b5.1 b5.2.2.2 stock5 cuts5 0
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
    (by unfold cuts5; decide +kernel) checks5

private def stock10 : List Word := [0x404, 0x500]
private def b10 : Bound := (0x505, stock10, 1, 0x400)
private def cuts10 : List Bound := []
private theorem lower10 : Lower b10.1 stock10 b10.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7f7cefd7b74f7e7d78e7c7970dfb776ccf97364d7a7568c787160bf76f5caf56b54b766d58a7469509f3674c8f16344972654887061407ef5f3c6ed5b3476e5d3866c59305eb572c4e9532456a552846851203e74f1c2e54b143664d1826449101e3470c0e1430416245080604100) lower5
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock17 : List Word := [0x20002, 0x30000]
private def b17 : Bound := (0x30003, stock17, 1, 0x20000)
private def cuts17 : List Bound := []
private theorem lower17 : Lower b17.1 stock17 b17.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcdfbb6ecf7ebcf8d7ab4e8efdbaf4cf9b2e4e7cb8f0c78b0e0bf7aedc9f3a6ccb76acd8972a4c8af5aad48f1a2c4a74a8d0870a0c07ef9ebc5eb96ac76e9cb856a94a86ed9ab44e992a466c98b046890a03e78e9c1e3868c3668c9816284882e58a940e1828426488900608080) lower5
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock18 : List Word := [0x40004, 0x50000]
private def b18 : Bound := (0x50005, stock18, 1, 0x40000)
private def cuts18 : List Bound := []
private theorem lower18 : Lower b18.1 stock18 b18.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7f7cdfb776cf7e7d78d7a7568efd7b74cf97364e7c7970c787160bf76f5c9f3674cb766d589726548af56b548f16344a74695087061407ef5f3c5eb572c76e5d3856a55286ed5b344e9532466c593046851203e74f1c1e3470c3664d1816245082e54b140e1430426449100604100) lower5
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock20 : List Word := [0x100010, 0x110000]
private def b20 : Bound := (0x110011, stock20, 1, 0x100000)
private def cuts20 : List Bound := []
private theorem lower20 : Lower b20.1 stock20 b20.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xffeff7adfaf76afbe7e78dba7668efcfb72cf8f362ebc7a70cb87260bf6ef5a9f2e74abb66e589b26648af4eb528f0e342ab46a508b062407eedf3a5ead72a7ae5e385aa56286ecdb324e8d3226ac5a304a852203e6cf1a1e2c70a3a64e181a246082e4cb120e0c3022a44a100a04200) lower5
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock33 : List Word := [0x200000002, 0x300000000]
private def b33 : Bound := (0x300000003, stock33, 1, 0x200000000)
private def cuts33 : List Bound := []
private theorem lower33 : Lower b33.1 stock33 b33.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcbf7aedcf7ebcf8b76acd8efdbaf4af5aad4e7cb8f0a74a8d0dfbb6ec9f3a6ccd7ab4e8972a4c8cf9b2e48f1a2c4c78b0e0870a0c07ef9ebc3e78e9c76e9cb83668c986ed9ab42e58a9466c98b026488905eb96ac1e3868c56a94a816284884e992a40e1828446890a00608080) lower5
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock34 : List Word := [0x400000004, 0x500000000]
private def b34 : Bound := (0x500000005, stock34, 1, 0x400000000)
private def cuts34 : List Bound := []
private theorem lower34 : Lower b34.1 stock34 b34.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7f7cbf76f5cf7e7d78b766d58efd7b74af56b54e7c7970a746950dfb776c9f3674cd7a75689726548cf973648f16344c78716087061407ef5f3c3e74f1c76e5d383664d186ed5b342e54b1466c593026449105eb572c1e3470c56a552816245084e953240e1430446851200604100) lower5
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock36 : List Word := [0x1000000010, 0x1100000000]
private def b36 : Bound := (0x1100000011, stock36, 1, 0x1000000000)
private def cuts36 : List Bound := []
private theorem lower36 : Lower b36.1 stock36 b36.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xffeff7abf6ef5afbe7e78bb66e58efcfb72af4eb52ebc7a70ab46a50dfaf76a9f2e74adba76689b26648cf8f3628f0e342cb872608b062407eedf3a3e6cf1a7ae5e383a64e186ecdb322e4cb126ac5a302a44a105ead72a1e2c70a5aa56281a246084e8d3220e0c3024a852200a04200) lower5
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock40 : List Word := [0x10000000100, 0x10100000000]
private def b40 : Bound := (0x10100000101, stock40, 1, 0x10000000000)
private def cuts40 : List Bound := []
private theorem lower40 : Lower b40.1 stock40 b40.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xffdff76bf5ef56fbd7e74bb56e54f7cfd72b74ed52f3c7c70b346c50df9f7669f1e746db976649b16644d78f562970e542d38746093064407eddf363e5cf167ad5e343a54e1476cdd32364cd1272c5c303244c105e9d7261e1c7065a956241a14604568d522160c50252854201204400) lower5
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock48 : List Word := [0x1000000010000, 0x1000100000000]
private def b48 : Bound := (0x1000100010001, stock48, 1, 0x1000000000000)
private def cuts48 : List Bound := []
private theorem lower48 : Lower b48.1 stock48 b48.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xffbff6ebf3ef4efbb7e6cbb36e4cf7afd6ab72ed4af3a7c68b326c48ef9fb66af1eb46eb97a64ab16a44e78f962a70e942e387860a3068407ebdf2e3e3cf0e7ab5e2c3a34e0c76add2a362cd0a72a5c283224c086e9db262e1cb066a95a242a14a04668d922260c90262858202204800) lower5
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock65 : List Word := [0x20000000000000002, 0x30000000000000000]
private def b65 : Bound := (0x30000000000000003, stock65, 1, 0x20000000000000000)
private def cuts65 : List Bound := []
private theorem lower65 : Lower b65.1 stock65 b65.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefc7ef9ebcf7ebcf876e9cb8efdbaf46ed9ab4e7cb8f066c98b0dfbb6ec5eb96acd7ab4e856a94a8cf9b2e44e992a4c78b0e046890a0bf7aedc3e78e9cb76acd83668c98af5aad42e58a94a74a8d026488909f3a6cc1e3868c972a4c816284888f1a2c40e18284870a0c00608080) lower5
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock66 : List Word := [0x40000000000000004, 0x50000000000000000]
private def b66 : Bound := (0x50000000000000005, stock66, 1, 0x40000000000000000)
private def cuts66 : List Bound := []
private theorem lower66 : Lower b66.1 stock66 b66.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7f7c7ef5f3cf7e7d7876e5d38efd7b746ed5b34e7c797066c5930dfb776c5eb572cd7a756856a5528cf973644e95324c7871604685120bf76f5c3e74f1cb766d583664d18af56b542e54b14a74695026449109f3674c1e3470c972654816245088f163440e1430487061400604100) lower5
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock68 : List Word := [0x100000000000000010, 0x110000000000000000]
private def b68 : Bound := (0x110000000000000011, stock68, 1, 0x100000000000000000)
private def cuts68 : List Bound := []
private theorem lower68 : Lower b68.1 stock68 b68.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xffeff7a7eedf3afbe7e787ae5e38efcfb726ecdb32ebc7a706ac5a30dfaf76a5ead72adba76685aa5628cf8f3624e8d322cb872604a85220bf6ef5a3e6cf1abb66e583a64e18af4eb522e4cb12ab46a502a44a109f2e74a1e2c70a9b266481a246088f0e3420e0c3028b062400a04200) lower5
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock72 : List Word := [0x1000000000000000100, 0x1010000000000000000]
private def b72 : Bound := (0x1010000000000000101, stock72, 1, 0x1000000000000000000)
private def cuts72 : List Bound := []
private theorem lower72 : Lower b72.1 stock72 b72.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xffdff767eddf36fbd7e747ad5e34f7cfd7276cdd32f3c7c7072c5c30df9f7665e9d726db976645a95624d78f562568d522d3874605285420bf5ef563e5cf16bb56e543a54e14b74ed52364cd12b346c503244c109f1e7461e1c7069b166441a14604970e542160c50293064401204400) lower5
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock80 : List Word := [0x100000000000000010000, 0x100010000000000000000]
private def b80 : Bound := (0x100010000000000010001, stock80, 1, 0x100000000000000000000)
private def cuts80 : List Bound := []
private theorem lower80 : Lower b80.1 stock80 b80.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xffbff6e7ebdf2efbb7e6c7ab5e2cf7afd6a76add2af3a7c6872a5c28ef9fb666e9db26eb97a646a95a24e78f962668d922e3878606285820bf3ef4e3e3cf0ebb36e4c3a34e0cb72ed4a362cd0ab326c483224c08af1eb462e1cb06ab16a442a14a04a70e942260c902a3068402204800) lower5
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock96 : List Word := [0x1000000000000000100000000, 0x1000000010000000000000000]
private def b96 : Bound := (0x1000000010000000100000001, stock96, 1, 0x1000000000000000000000000)
private def cuts96 : List Bound := []
private theorem lower96 : Lower b96.1 stock96 b96.2.2.2 1 :=
  lowerRelabelMasked (rowSelectPacked 0xff7ff5e7e7df1efb77e5c7a75e1cf76fd5a766dd1af367c587265c18ef5fb566e5db16eb57a546a55a14e74f952664d912e3478506245810df3f74e5e3d70edb3764c5a3560cd72f54a562d50ad3274485225408cf1f3464e1d306cb172444a15204c70f142460d102c3070404205000) lower5
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock19 : List Word := [0xa000a, 0xc000c, 0xf0000]
private def b19 : Bound := (0xf000f, stock19, 2, 0xe0000)
private def cuts19 : List Bound := [b17, b18]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks19 : treeBlock 0 (2 ^ stock19.length) (fun token =>
    closes b19.1 b19.2.2.2 cuts19 1 (rootState stock19 1 token)) = true := by
  decide +kernel
private theorem lower19 : Lower b19.1 stock19 b19.2.2.2 2 := by
  exact deriveLower b19.1 b19.2.2.2 stock19 cuts19 1
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower18) lower17)
    (by unfold cuts19; decide +kernel) checks19

private def stock21 : List Word := [0x220022, 0x300030, 0x330000]
private def b21 : Bound := (0x330033, stock21, 4, 0x320020)
private def cuts21 : List Bound := [b5, b17, b20]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks21 : treeBlock 0 (2 ^ stock21.length) (fun token =>
    closes b21.1 b21.2.2.2 cuts21 3 (rootState stock21 3 token)) = true := by
  decide +kernel
private theorem lower21 : Lower b21.1 stock21 b21.2.2.2 4 := by
  exact deriveLower b21.1 b21.2.2.2 stock21 cuts21 3
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower20) lower17) lower5)
    (by unfold cuts21; decide +kernel) checks21

private def stock22 : List Word := [0x440044, 0x500050, 0x550000]
private def b22 : Bound := (0x550055, stock22, 2, 0x540000)
private def cuts22 : List Bound := [b18, b20]
private theorem lower22 : Lower b22.1 stock22 b22.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7df9fdf3d78efd79f1edd3970dfb75e9ddb3568cf971e1cd93160bf76dd9bd72d58af569d1ad529509f365c99d325488f161c18d121407ef5db97cf1d386ed59b16cd19305eb55a95cb15284e951a14c911203e74d993c70d182e549912c509101e345891c305080e141810c10100) lower19
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock26 : List Word := [0x4040404, 0x5000500, 0x5050000]
private def b26 : Bound := (0x5050505, stock26, 2, 0x4040400)
private def cuts26 : List Bound := [b10, b18]
private theorem lower26 : Lower b26.1 stock26 b26.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xffdf7e7fddb766f7cf5e3f5cb562fbd76e5f9d3664f3c74e1f1c3460bf5e7c7bd5a746b74e5c3b54a542bb566c5b952644b3464c1b1424407edd7a77cd972676cd5a374c95227ad56a578d162472c54a170c14203e5c7873c58706364c58334485023a54685385060432444813040400) lower19
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock35 : List Word := [0xa0000000a, 0xc0000000c, 0xf00000000]
private def b35 : Bound := (0xf0000000f, stock35, 2, 0xe00000000)
private def cuts35 : List Bound := [b33, b34]
private theorem lower35 : Lower b35.1 stock35 b35.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0bf7aedcb76acd8af5aad4a74a8d0dfbb6ecd7ab4e8cf9b2e4c78b0e09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b03e78e9c3668c982e58a9426488905eb96ac56a94a84e992a446890a01e3868c16284880e182840608080) lower19
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock37 : List Word := [0x2200000022, 0x3000000030, 0x3300000000]
private def b37 : Bound := (0x3300000033, stock37, 4, 0x3200000020)
private def cuts37 : List Bound := [b5, b33, b36]
private theorem lower37 : Lower b37.1 stock37 b37.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0bf7aedcb76acd8af5aad4a74a8d0dfbb6ecd7ab4e8cf9b2e4c78b0e09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b03e78e9c3668c982e58a9426488905eb96ac56a94a84e992a446890a01e3868c16284880e182840608080) lower21
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock38 : List Word := [0x4400000044, 0x5000000050, 0x5500000000]
private def b38 : Bound := (0x5500000055, stock38, 2, 0x5400000000)
private def cuts38 : List Bound := [b34, b36]
private theorem lower38 : Lower b38.1 stock38 b38.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7df9fdf3d78efd79f1edd3970bf76dd9bd72d58af569d1ad52950dfb75e9ddb3568cf971e1cd931609f365c99d325488f161c18d121407ef5db97cf1d386ed59b16cd19303e74d993c70d182e549912c509105eb55a95cb15284e951a14c911201e345891c305080e141810c10100) lower19
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock41 : List Word := [0x20200000202, 0x30000000300, 0x30300000000]
private def b41 : Bound := (0x30300000303, stock41, 2, 0x30200000000)
private def cuts41 : List Bound := [b33, b40]
private theorem lower41 : Lower b41.1 stock41 b41.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbbf6fbf3af4f7eb9f2f3e38f0bf7abd6bb72ad4b76a9d2b3628d0dfbb3e6dbb32e4d7ab1e2d3a30e09f3a3c69b322c4972a1c293220c07ef9bb67af1ab476e99b272e18b03e78b963a70a94366899232608905eb93a65ab12a456a91a252a10a01e383861a3028416281821220080) lower19
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock42 : List Word := [0x40400000404, 0x50000000500, 0x50500000000]
private def b42 : Bound := (0x50500000505, stock42, 4, 0x50400000400)
private def cuts42 : List Bound := [b10, b34, b40]
private theorem lower42 : Lower b42.1 stock42 b42.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7f7cefd7b74f7e7d78e7c7970bf76f5caf56b54b766d58a746950dfb776ccf97364d7a7568c7871609f3674c8f16344972654887061407ef5f3c6ed5b3476e5d3866c59303e74f1c2e54b143664d1826449105eb572c4e9532456a552846851201e3470c0e1430416245080604100) lower21
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock44 : List Word := [0x101000001010, 0x110000001100, 0x111100000000]
private def b44 : Bound := (0x111100001111, stock44, 2, 0x111000000000)
private def cuts44 : List Bound := [b36, b40]
private theorem lower44 : Lower b44.1 stock44 b44.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xffefbf3fdebb72fbe7af1f9e3a70bf6ebd3bd6ab52bb66ad1b962a50dfaf3e3ddab362dba72e1d9a32609f2e3c39d2a3429b262c199222407eedbb37ce9b327ae5ab178e1a303e6cb933c68b123a64a913860a105ead3a35ca93225aa52a158a12201e2c3831c283021a242811820200) lower19
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock49 : List Word := [0x2000200020002, 0x3000000030000, 0x3000300000000]
private def b49 : Bound := (0x3000300030003, stock49, 4, 0x3000200020000)
private def cuts49 : List Bound := [b17, b33, b48]
private theorem lower49 : Lower b49.1 stock49 b49.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcdfbb6ecf7ebcf8d7ab4e8bf7aedc9f3a6ccb76acd8972a4c8efdbaf4cf9b2e4e7cb8f0c78b0e0af5aad48f1a2c4a74a8d0870a0c07ef9ebc5eb96ac76e9cb856a94a83e78e9c1e3868c3668c9816284886ed9ab44e992a466c98b046890a02e58a940e1828426488900608080) lower21
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock50 : List Word := [0x4000400040004, 0x5000000050000, 0x5000500000000]
private def b50 : Bound := (0x5000500050005, stock50, 4, 0x5000400040000)
private def cuts50 : List Bound := [b18, b34, b48]
private theorem lower50 : Lower b50.1 stock50 b50.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7f7cdfb776cf7e7d78d7a7568bf76f5c9f3674cb766d589726548efd7b74cf97364e7c7970c787160af56b548f16344a74695087061407ef5f3c5eb572c76e5d3856a55283e74f1c1e3470c3664d1816245086ed5b344e9532466c593046851202e54b140e1430426449100604100) lower21
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock52 : List Word := [0x10001000100010, 0x11000000110000, 0x11001100000000]
private def b52 : Bound := (0x11001100110011, stock52, 4, 0x11001000100000)
private def cuts52 : List Bound := [b20, b36, b48]
private theorem lower52 : Lower b52.1 stock52 b52.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xffeff7adfaf76afbe7e78dba7668bf6ef5a9f2e74abb66e589b26648efcfb72cf8f362ebc7a70cb87260af4eb528f0e342ab46a508b062407eedf3a5ead72a7ae5e385aa56283e6cf1a1e2c70a3a64e181a246086ecdb324e8d3226ac5a304a852202e4cb120e0c3022a44a100a04200) lower21
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock56 : List Word := [0x100010001000100, 0x101000001010000, 0x101010100000000]
private def b56 : Bound := (0x101010101010101, stock56, 2, 0x101010000000000)
private def cuts56 : List Bound := [b40, b48]
private theorem lower56 : Lower b56.1 stock56 b56.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xffdf7e7fddb766fbd76e5f9d3664bf5e7c7bd5a746bb566c5b952644f7cf5e3f5cb562f3c74e1f1c3460b74e5c3b54a542b3464c1b1424407edd7a77cd97267ad56a578d16243e5c7873c587063a54685385060476cd5a374c952272c54a170c1420364c583344850232444813040400) lower19
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock67 : List Word := [0xa000000000000000a, 0xc000000000000000c, 0xf0000000000000000]
private def b67 : Bound := (0xf000000000000000f, stock67, 2, 0xe0000000000000000)
private def cuts67 : List Bound := [b65, b66]
private theorem lower67 : Lower b67.1 stock67 b67.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f07ef9ebc76e9cb86ed9ab466c98b0dfbb6ecd7ab4e8cf9b2e4c78b0e05eb96ac56a94a84e992a446890a0bf7aedcb76acd8af5aad4a74a8d03e78e9c3668c982e58a9426488909f3a6cc972a4c88f1a2c4870a0c01e3868c16284880e182840608080) lower19
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock69 : List Word := [0x220000000000000022, 0x300000000000000030, 0x330000000000000000]
private def b69 : Bound := (0x330000000000000033, stock69, 4, 0x320000000000000020)
private def cuts69 : List Bound := [b5, b65, b68]
private theorem lower69 : Lower b69.1 stock69 b69.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f07ef9ebc76e9cb86ed9ab466c98b0dfbb6ecd7ab4e8cf9b2e4c78b0e05eb96ac56a94a84e992a446890a0bf7aedcb76acd8af5aad4a74a8d03e78e9c3668c982e58a9426488909f3a6cc972a4c88f1a2c4870a0c01e3868c16284880e182840608080) lower21
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock70 : List Word := [0x440000000000000044, 0x500000000000000050, 0x550000000000000000]
private def b70 : Bound := (0x550000000000000055, stock70, 2, 0x540000000000000000)
private def cuts70 : List Bound := [b66, b68]
private theorem lower70 : Lower b70.1 stock70 b70.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7df9fdf3d78efd79f1edd39707ef5db97cf1d386ed59b16cd1930dfb75e9ddb3568cf971e1cd931605eb55a95cb15284e951a14c91120bf76dd9bd72d58af569d1ad529503e74d993c70d182e549912c509109f365c99d325488f161c18d121401e345891c305080e141810c10100) lower19
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock73 : List Word := [0x2020000000000000202, 0x3000000000000000300, 0x3030000000000000000]
private def b73 : Bound := (0x3030000000000000303, stock73, 2, 0x3020000000000000000)
private def cuts73 : List Bound := [b65, b72]
private theorem lower73 : Lower b73.1 stock73 b73.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbbf6fbf3af4f7eb9f2f3e38f07ef9bb67af1ab476e99b272e18b0dfbb3e6dbb32e4d7ab1e2d3a30e05eb93a65ab12a456a91a252a10a0bf7abd6bb72ad4b76a9d2b3628d03e78b963a70a94366899232608909f3a3c69b322c4972a1c293220c01e383861a3028416281821220080) lower19
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock74 : List Word := [0x4040000000000000404, 0x5000000000000000500, 0x5050000000000000000]
private def b74 : Bound := (0x5050000000000000505, stock74, 4, 0x5040000000000000400)
private def cuts74 : List Bound := [b10, b66, b72]
private theorem lower74 : Lower b74.1 stock74 b74.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7f7cefd7b74f7e7d78e7c79707ef5f3c6ed5b3476e5d3866c5930dfb776ccf97364d7a7568c7871605eb572c4e9532456a55284685120bf76f5caf56b54b766d58a7469503e74f1c2e54b143664d1826449109f3674c8f16344972654887061401e3470c0e1430416245080604100) lower21
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock76 : List Word := [0x10100000000000001010, 0x11000000000000001100, 0x11110000000000000000]
private def b76 : Bound := (0x11110000000000001111, stock76, 2, 0x11100000000000000000)
private def cuts76 : List Bound := [b68, b72]
private theorem lower76 : Lower b76.1 stock76 b76.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xffefbf3fdebb72fbe7af1f9e3a707eedbb37ce9b327ae5ab178e1a30dfaf3e3ddab362dba72e1d9a32605ead3a35ca93225aa52a158a1220bf6ebd3bd6ab52bb66ad1b962a503e6cb933c68b123a64a913860a109f2e3c39d2a3429b262c199222401e2c3831c283021a242811820200) lower19
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock81 : List Word := [0x200020000000000020002, 0x300000000000000030000, 0x300030000000000000000]
private def b81 : Bound := (0x300030000000000030003, stock81, 4, 0x300020000000000020000)
private def cuts81 : List Bound := [b17, b65, b80]
private theorem lower81 : Lower b81.1 stock81 b81.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcdfbb6ecf7ebcf8d7ab4e87ef9ebc5eb96ac76e9cb856a94a8efdbaf4cf9b2e4e7cb8f0c78b0e06ed9ab44e992a466c98b046890a0bf7aedc9f3a6ccb76acd8972a4c83e78e9c1e3868c3668c981628488af5aad48f1a2c4a74a8d0870a0c02e58a940e1828426488900608080) lower21
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock82 : List Word := [0x400040000000000040004, 0x500000000000000050000, 0x500050000000000000000]
private def b82 : Bound := (0x500050000000000050005, stock82, 4, 0x500040000000000040000)
private def cuts82 : List Bound := [b18, b66, b80]
private theorem lower82 : Lower b82.1 stock82 b82.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7f7cdfb776cf7e7d78d7a75687ef5f3c5eb572c76e5d3856a5528efd7b74cf97364e7c7970c7871606ed5b344e9532466c59304685120bf76f5c9f3674cb766d5897265483e74f1c1e3470c3664d181624508af56b548f16344a74695087061402e54b140e1430426449100604100) lower21
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock84 : List Word := [0x1000100000000000100010, 0x1100000000000000110000, 0x1100110000000000000000]
private def b84 : Bound := (0x1100110000000000110011, stock84, 4, 0x1100100000000000100000)
private def cuts84 : List Bound := [b20, b68, b80]
private theorem lower84 : Lower b84.1 stock84 b84.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xffeff7adfaf76afbe7e78dba76687eedf3a5ead72a7ae5e385aa5628efcfb72cf8f362ebc7a70cb872606ecdb324e8d3226ac5a304a85220bf6ef5a9f2e74abb66e589b266483e6cf1a1e2c70a3a64e181a24608af4eb528f0e342ab46a508b062402e4cb120e0c3022a44a100a04200) lower21
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock88 : List Word := [0x10001000000000001000100, 0x10100000000000001010000, 0x10101010000000000000000]
private def b88 : Bound := (0x10101010000000001010101, stock88, 2, 0x10101000000000000000000)
private def cuts88 : List Bound := [b72, b80]
private theorem lower88 : Lower b88.1 stock88 b88.2.2.2 2 :=
  lowerRelabelMasked (rowSelectPacked 0xffdf7e7fddb766fbd76e5f9d36647edd7a77cd97267ad56a578d1624f7cf5e3f5cb562f3c74e1f1c346076cd5a374c952272c54a170c1420bf5e7c7bd5a746bb566c5b9526443e5c7873c587063a546853850604b74e5c3b54a542b3464c1b142440364c583344850232444813040400) lower19
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock97 : List Word := [0x2000000020000000200000002, 0x3000000000000000300000000, 0x3000000030000000000000000]
private def b97 : Bound := (0x3000000030000000300000003, stock97, 4, 0x3000000020000000200000000)
private def cuts97 : List Bound := [b33, b65, b96]
private theorem lower97 : Lower b97.1 stock97 b97.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcbf7aedcf7ebcf8b76acd87ef9ebc3e78e9c76e9cb83668c98efdbaf4af5aad4e7cb8f0a74a8d06ed9ab42e58a9466c98b02648890dfbb6ec9f3a6ccd7ab4e8972a4c85eb96ac1e3868c56a94a81628488cf9b2e48f1a2c4c78b0e0870a0c04e992a40e1828446890a00608080) lower21
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock98 : List Word := [0x4000000040000000400000004, 0x5000000000000000500000000, 0x5000000050000000000000000]
private def b98 : Bound := (0x5000000050000000500000005, stock98, 4, 0x5000000040000000400000000)
private def cuts98 : List Bound := [b34, b66, b96]
private theorem lower98 : Lower b98.1 stock98 b98.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7f7cbf76f5cf7e7d78b766d587ef5f3c3e74f1c76e5d383664d18efd7b74af56b54e7c7970a7469506ed5b342e54b1466c59302644910dfb776c9f3674cd7a756897265485eb572c1e3470c56a55281624508cf973648f16344c78716087061404e953240e1430446851200604100) lower21
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock100 : List Word := [0x10000000100000001000000010, 0x11000000000000001100000000, 0x11000000110000000000000000]
private def b100 : Bound := (0x11000000110000001100000011, stock100, 4, 0x11000000100000001000000000)
private def cuts100 : List Bound := [b36, b68, b96]
private theorem lower100 : Lower b100.1 stock100 b100.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xffeff7abf6ef5afbe7e78bb66e587eedf3a3e6cf1a7ae5e383a64e18efcfb72af4eb52ebc7a70ab46a506ecdb322e4cb126ac5a302a44a10dfaf76a9f2e74adba76689b266485ead72a1e2c70a5aa56281a24608cf8f3628f0e342cb872608b062404e8d3220e0c3024a852200a04200) lower21
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock104 : List Word := [0x100000001000000010000000100, 0x101000000000000010100000000, 0x101000001010000000000000000]
private def b104 : Bound := (0x101000001010000010100000101, stock104, 4, 0x101000001000000010000000000)
private def cuts104 : List Bound := [b40, b72, b96]
private theorem lower104 : Lower b104.1 stock104 b104.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xffdff76bf5ef56fbd7e74bb56e547eddf363e5cf167ad5e343a54e14f7cfd72b74ed52f3c7c70b346c5076cdd32364cd1272c5c303244c10df9f7669f1e746db976649b166445e9d7261e1c7065a956241a14604d78f562970e542d3874609306440568d522160c50252854201204400) lower21
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock112 : List Word := [0x10000000100000001000000010000, 0x10001000000000001000100000000, 0x10001000100010000000000000000]
private def b112 : Bound := (0x10001000100010001000100010001, stock112, 4, 0x10001000100000001000000000000)
private def cuts112 : List Bound := [b48, b80, b96]
private theorem lower112 : Lower b112.1 stock112 b112.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xffbff6ebf3ef4efbb7e6cbb36e4c7ebdf2e3e3cf0e7ab5e2c3a34e0cf7afd6ab72ed4af3a7c68b326c4876add2a362cd0a72a5c283224c08ef9fb66af1eb46eb97a64ab16a446e9db262e1cb066a95a242a14a04e78f962a70e942e387860a306840668d922260c90262858202204800) lower21
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock15 : List Word := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]
private def b15 : Bound := (0xffff, stock15, 3, 0xeca0)
private def cuts15 : List Bound := [b5, b10]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks15 : treeBlock 0 (2 ^ stock15.length) (fun token =>
    closes b15.1 b15.2.2.2 cuts15 2 (rootState stock15 2 token)) = true := by
  decide +kernel
private theorem lower15 : Lower b15.1 stock15 b15.2.2.2 3 := by
  exact deriveLower b15.1 b15.2.2.2 stock15 cuts15 2
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower10) lower5)
    (by unfold cuts15; decide +kernel) checks15

private def stock23 : List Word := [0xaa00aa, 0xcc00cc, 0xf000f0, 0xff0000]
private def b23 : Bound := (0xff00ff, stock23, 5, 0xfe00a0)
private def cuts23 : List Bound := [b21, b19, b22, b5]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks23 : treeBlock 0 (2 ^ stock23.length) (fun token =>
    closes b23.1 b23.2.2.2 cuts23 4 (rootState stock23 4 token)) = true := by
  decide +kernel
private theorem lower23 : Lower b23.1 stock23 b23.2.2.2 5 := by
  exact deriveLower b23.1 b23.2.2.2 stock23 cuts23 4
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower5) lower22) lower19) lower21)
    (by unfold cuts23; decide +kernel) checks23

private def stock27 : List Word := [0xa0a0a0a, 0xc0c0c0c, 0xf000f00, 0xf0f0000]
private def b27 : Bound := (0xf0f0f0f, stock27, 4, 0xe0e0c00)
private def cuts27 : List Bound := [b19, b26, b10, b17]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks27 : treeBlock 0 (2 ^ stock27.length) (fun token =>
    closes b27.1 b27.2.2.2 cuts27 3 (rootState stock27 3 token)) = true := by
  decide +kernel
private theorem lower27 : Lower b27.1 stock27 b27.2.2.2 4 := by
  exact deriveLower b27.1 b27.2.2.2 stock27 cuts27 3
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower17) lower10) lower26) lower19)
    (by unfold cuts27; decide +kernel) checks27

private def stock30 : List Word := [0x44444444, 0x50505050, 0x55005500, 0x55550000]
private def b30 : Bound := (0x55555555, stock30, 4, 0x54544400)
private def cuts30 : List Bound := [b22, b26, b10, b20]
private theorem lower30 : Lower b30.1 stock30 b30.2.2.2 4 :=
  lowerRelabelMasked (rowSelectPacked 0xffefef9fdebe78efcfaf1edcba70dfaf6e9ddab668cf8f2e1cd8b260bf6eed9bd6ae58af4ead1ad4aa509f2e6c99d2a6488f0e2c18d0a2407eedeb97ce9e386ecdab16cc9a305ead6a95ca96284e8d2a14c892203e6ce993c68e182e4ca912c48a101e2c6891c286080e0c2810c08200) lower27
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock39 : List Word := [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000]
private def b39 : Bound := (0xff000000ff, stock39, 5, 0xfe000000a0)
private def cuts39 : List Bound := [b37, b35, b38, b5]
private theorem lower39 : Lower b39.1 stock39 b39.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0bf7aedcb76acd8af5aad4a74a8d0dfbb6ecd7ab4e8cf9b2e4c78b0e09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b03e78e9c3668c982e58a9426488905eb96ac56a94a84e992a446890a01e3868c16284880e182840608080) lower23
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock43 : List Word := [0xa0a00000a0a, 0xc0c00000c0c, 0xf0000000f00, 0xf0f00000000]
private def b43 : Bound := (0xf0f00000f0f, stock43, 5, 0xf0e00000c00)
private def cuts43 : List Bound := [b42, b35, b41, b10]
private theorem lower43 : Lower b43.1 stock43 b43.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7f7cefd7b74f7e7d78e7c7970bf76f5caf56b54b766d58a746950dfb776ccf97364d7a7568c7871609f3674c8f16344972654887061407ef5f3c6ed5b3476e5d3866c59303e74f1c2e54b143664d1826449105eb572c4e9532456a552846851201e3470c0e1430416245080604100) lower23
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock45 : List Word := [0x222200002222, 0x303000003030, 0x330000003300, 0x333300000000]
private def b45 : Bound := (0x333300003333, stock45, 5, 0x333200002020)
private def cuts45 : List Bound := [b37, b41, b44, b5]
private theorem lower45 : Lower b45.1 stock45 b45.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbbf6f7eb9f2fbf3af4f3e38f0bf7abd6b76a9d2bb72ad4b3628d0dfbb3e6d7ab1e2dbb32e4d3a30e09f3a3c6972a1c29b322c493220c07ef9bb676e99b27af1ab472e18b03e78b9636689923a70a9432608905eb93a656a91a25ab12a452a10a01e3838616281821a302841220080) lower23
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock46 : List Word := [0x444400004444, 0x505000005050, 0x550000005500, 0x555500000000]
private def b46 : Bound := (0x555500005555, stock46, 5, 0x555400004400)
private def cuts46 : List Bound := [b42, b38, b44, b10]
private theorem lower46 : Lower b46.1 stock46 b46.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7df9efd79f1fdf3d78edd3970bf76dd9af569d1bd72d58ad52950dfb75e9cf971e1ddb3568cd931609f365c98f161c19d325488d121407ef5db96ed59b17cf1d386cd19303e74d992e549913c70d182c509105eb55a94e951a15cb15284c911201e345890e141811c305080c10100) lower23
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock51 : List Word := [0xa000a000a000a, 0xc000c000c000c, 0xf0000000f0000, 0xf000f00000000]
private def b51 : Bound := (0xf000f000f000f, stock51, 5, 0xf000e000e0000)
private def cuts51 : List Bound := [b49, b50, b19, b35]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks51 : treeBlock 0 (2 ^ stock51.length) (fun token =>
    closes b51.1 b51.2.2.2 cuts51 4 (rootState stock51 4 token)) = true := by
  decide +kernel
private theorem lower51 : Lower b51.1 stock51 b51.2.2.2 5 := by
  exact deriveLower b51.1 b51.2.2.2 stock51 cuts51 4
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower35) lower19) lower50) lower49)
    (by unfold cuts51; decide +kernel) checks51

private def stock53 : List Word := [0x22002200220022, 0x30003000300030, 0x33000000330000, 0x33003300000000]
private def b53 : Bound := (0x33003300330033, stock53, 7, 0x33003200320020)
private def cuts53 : List Bound := [b21, b37, b49, b52]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks53 : treeBlock 0 (2 ^ stock53.length) (fun token =>
    closes b53.1 b53.2.2.2 cuts53 6 (rootState stock53 6 token)) = true := by
  decide +kernel
private theorem lower53 : Lower b53.1 stock53 b53.2.2.2 7 := by
  exact deriveLower b53.1 b53.2.2.2 stock53 cuts53 6
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower52) lower49) lower37) lower21)
    (by unfold cuts53; decide +kernel) checks53

private def stock54 : List Word := [0x44004400440044, 0x50005000500050, 0x55000000550000, 0x55005500000000]
private def b54 : Bound := (0x55005500550055, stock54, 5, 0x55005400540000)
private def cuts54 : List Bound := [b50, b52, b22, b38]
private theorem lower54 : Lower b54.1 stock54 b54.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7df9fdf3d78efd79f1edd3970dfb75e9ddb3568cf971e1cd93160bf76dd9bd72d58af569d1ad529509f365c99d325488f161c18d121407ef5db97cf1d386ed59b16cd19305eb55a95cb15284e951a14c911203e74d993c70d182e549912c509101e345891c305080e141810c10100) lower51
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock57 : List Word := [0x202020202020202, 0x300030003000300, 0x303000003030000, 0x303030300000000]
private def b57 : Bound := (0x303030303030303, stock57, 5, 0x303030202020000)
private def cuts57 : List Bound := [b49, b41, b56, b17]
private theorem lower57 : Lower b57.1 stock57 b57.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbbf6dfbb3e6fbf3af4dbb32e4bf7abd69f3a3c6bb72ad49b322c4f7eb9f2d7ab1e2f3e38f0d3a30e0b76a9d2972a1c2b3628d093220c07ef9bb65eb93a67af1ab45ab12a43e78b961e383863a70a941a3028476e99b256a91a272e18b052a10a03668992162818232608901220080) lower23
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock58 : List Word := [0x404040404040404, 0x500050005000500, 0x505000005050000, 0x505050500000000]
private def b58 : Bound := (0x505050505050505, stock58, 5, 0x505050404040400)
private def cuts58 : List Bound := [b42, b50, b26, b56]
private theorem lower58 : Lower b58.1 stock58 b58.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xffdf7e7fddb766f7cf5e3f5cb562fbd76e5f9d3664f3c74e1f1c3460bf5e7c7bd5a746b74e5c3b54a542bb566c5b952644b3464c1b1424407edd7a77cd972676cd5a374c95227ad56a578d162472c54a170c14203e5c7873c58706364c58334485023a54685385060432444813040400) lower51
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock60 : List Word := [0x1010101010101010, 0x1100110011001100, 0x1111000011110000, 0x1111111100000000]
private def b60 : Bound := (0x1111111111111111, stock60, 5, 0x1111111010100000)
private def cuts60 : List Bound := [b52, b44, b56, b20]
private theorem lower60 : Lower b60.1 stock60 b60.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xffefbf3dfaf3e3fdebb72ddab362bf6ebd39f2e3c3bd6ab529d2a342fbe7af1dba72e1f9e3a70d9a3260bb66ad19b262c1b962a5099222407eedbb35ead3a37ce9b325ca93223e6cb931e2c3833c68b121c283027ae5ab15aa52a178e1a3058a12203a64a911a242813860a101820200) lower23
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock71 : List Word := [0xaa00000000000000aa, 0xcc00000000000000cc, 0xf000000000000000f0, 0xff0000000000000000]
private def b71 : Bound := (0xff00000000000000ff, stock71, 5, 0xfe00000000000000a0)
private def cuts71 : List Bound := [b69, b67, b70, b5]
private theorem lower71 : Lower b71.1 stock71 b71.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f07ef9ebc76e9cb86ed9ab466c98b0dfbb6ecd7ab4e8cf9b2e4c78b0e05eb96ac56a94a84e992a446890a0bf7aedcb76acd8af5aad4a74a8d03e78e9c3668c982e58a9426488909f3a6cc972a4c88f1a2c4870a0c01e3868c16284880e182840608080) lower23
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock75 : List Word := [0xa0a0000000000000a0a, 0xc0c0000000000000c0c, 0xf000000000000000f00, 0xf0f0000000000000000]
private def b75 : Bound := (0xf0f0000000000000f0f, stock75, 5, 0xf0e0000000000000c00)
private def cuts75 : List Bound := [b74, b67, b73, b10]
private theorem lower75 : Lower b75.1 stock75 b75.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7f7cefd7b74f7e7d78e7c79707ef5f3c6ed5b3476e5d3866c5930dfb776ccf97364d7a7568c7871605eb572c4e9532456a55284685120bf76f5caf56b54b766d58a7469503e74f1c2e54b143664d1826449109f3674c8f16344972654887061401e3470c0e1430416245080604100) lower23
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock77 : List Word := [0x22220000000000002222, 0x30300000000000003030, 0x33000000000000003300, 0x33330000000000000000]
private def b77 : Bound := (0x33330000000000003333, stock77, 5, 0x33320000000000002020)
private def cuts77 : List Bound := [b69, b73, b76, b5]
private theorem lower77 : Lower b77.1 stock77 b77.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbbf6f7eb9f2fbf3af4f3e38f07ef9bb676e99b27af1ab472e18b0dfbb3e6d7ab1e2dbb32e4d3a30e05eb93a656a91a25ab12a452a10a0bf7abd6b76a9d2bb72ad4b3628d03e78b9636689923a70a9432608909f3a3c6972a1c29b322c493220c01e3838616281821a302841220080) lower23
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock78 : List Word := [0x44440000000000004444, 0x50500000000000005050, 0x55000000000000005500, 0x55550000000000000000]
private def b78 : Bound := (0x55550000000000005555, stock78, 5, 0x55540000000000004400)
private def cuts78 : List Bound := [b74, b70, b76, b10]
private theorem lower78 : Lower b78.1 stock78 b78.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7df9efd79f1fdf3d78edd39707ef5db96ed59b17cf1d386cd1930dfb75e9cf971e1ddb3568cd931605eb55a94e951a15cb15284c91120bf76dd9af569d1bd72d58ad529503e74d992e549913c70d182c509109f365c98f161c19d325488d121401e345890e141811c305080c10100) lower23
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock83 : List Word := [0xa000a00000000000a000a, 0xc000c00000000000c000c, 0xf000000000000000f0000, 0xf000f0000000000000000]
private def b83 : Bound := (0xf000f00000000000f000f, stock83, 5, 0xf000e00000000000e0000)
private def cuts83 : List Bound := [b81, b82, b19, b67]
private theorem lower83 : Lower b83.1 stock83 b83.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c03e78e9c3668c982e58a9426488901e3868c16284880e182840608080) lower51
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock85 : List Word := [0x2200220000000000220022, 0x3000300000000000300030, 0x3300000000000000330000, 0x3300330000000000000000]
private def b85 : Bound := (0x3300330000000000330033, stock85, 7, 0x3300320000000000320020)
private def cuts85 : List Bound := [b21, b69, b81, b84]
private theorem lower85 : Lower b85.1 stock85 b85.2.2.2 7 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c03e78e9c3668c982e58a9426488901e3868c16284880e182840608080) lower53
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock86 : List Word := [0x4400440000000000440044, 0x5000500000000000500050, 0x5500000000000000550000, 0x5500550000000000000000]
private def b86 : Bound := (0x5500550000000000550055, stock86, 5, 0x5500540000000000540000)
private def cuts86 : List Bound := [b82, b84, b22, b70]
private theorem lower86 : Lower b86.1 stock86 b86.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7df9fdf3d78efd79f1edd3970dfb75e9ddb3568cf971e1cd931607ef5db97cf1d386ed59b16cd19305eb55a95cb15284e951a14c91120bf76dd9bd72d58af569d1ad529509f365c99d325488f161c18d121403e74d993c70d182e549912c509101e345891c305080e141810c10100) lower51
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock89 : List Word := [0x20202020000000002020202, 0x30003000000000003000300, 0x30300000000000003030000, 0x30303030000000000000000]
private def b89 : Bound := (0x30303030000000003030303, stock89, 5, 0x30303020000000002020000)
private def cuts89 : List Bound := [b81, b73, b88, b17]
private theorem lower89 : Lower b89.1 stock89 b89.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbbf6dfbb3e6fbf3af4dbb32e47ef9bb65eb93a67af1ab45ab12a4f7eb9f2d7ab1e2f3e38f0d3a30e076e99b256a91a272e18b052a10a0bf7abd69f3a3c6bb72ad49b322c43e78b961e383863a70a941a30284b76a9d2972a1c2b3628d093220c03668992162818232608901220080) lower23
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock90 : List Word := [0x40404040000000004040404, 0x50005000000000005000500, 0x50500000000000005050000, 0x50505050000000000000000]
private def b90 : Bound := (0x50505050000000005050505, stock90, 5, 0x50505040000000004040400)
private def cuts90 : List Bound := [b74, b82, b26, b88]
private theorem lower90 : Lower b90.1 stock90 b90.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xffdf7e7fddb766f7cf5e3f5cb562fbd76e5f9d3664f3c74e1f1c34607edd7a77cd972676cd5a374c95227ad56a578d162472c54a170c1420bf5e7c7bd5a746b74e5c3b54a542bb566c5b952644b3464c1b1424403e5c7873c58706364c58334485023a54685385060432444813040400) lower51
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock92 : List Word := [0x101010100000000010101010, 0x110011000000000011001100, 0x111100000000000011110000, 0x111111110000000000000000]
private def b92 : Bound := (0x111111110000000011111111, stock92, 5, 0x111111100000000010100000)
private def cuts92 : List Bound := [b84, b76, b88, b20]
private theorem lower92 : Lower b92.1 stock92 b92.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xffefbf3dfaf3e3fdebb72ddab3627eedbb35ead3a37ce9b325ca9322fbe7af1dba72e1f9e3a70d9a32607ae5ab15aa52a178e1a3058a1220bf6ebd39f2e3c3bd6ab529d2a3423e6cb931e2c3833c68b121c28302bb66ad19b262c1b962a5099222403a64a911a242813860a101820200) lower23
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock99 : List Word := [0xa0000000a0000000a0000000a, 0xc0000000c0000000c0000000c, 0xf000000000000000f00000000, 0xf0000000f0000000000000000]
private def b99 : Bound := (0xf0000000f0000000f0000000f, stock99, 5, 0xf0000000e0000000e00000000)
private def cuts99 : List Bound := [b97, b98, b35, b67]
private theorem lower99 : Lower b99.1 stock99 b99.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0bf7aedcb76acd8af5aad4a74a8d07ef9ebc76e9cb86ed9ab466c98b03e78e9c3668c982e58a942648890dfbb6ecd7ab4e8cf9b2e4c78b0e09f3a6cc972a4c88f1a2c4870a0c05eb96ac56a94a84e992a446890a01e3868c16284880e182840608080) lower51
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock101 : List Word := [0x22000000220000002200000022, 0x30000000300000003000000030, 0x33000000000000003300000000, 0x33000000330000000000000000]
private def b101 : Bound := (0x33000000330000003300000033, stock101, 7, 0x33000000320000003200000020)
private def cuts101 : List Bound := [b37, b69, b97, b100]
private theorem lower101 : Lower b101.1 stock101 b101.2.2.2 7 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0bf7aedcb76acd8af5aad4a74a8d07ef9ebc76e9cb86ed9ab466c98b03e78e9c3668c982e58a942648890dfbb6ecd7ab4e8cf9b2e4c78b0e09f3a6cc972a4c88f1a2c4870a0c05eb96ac56a94a84e992a446890a01e3868c16284880e182840608080) lower53
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock102 : List Word := [0x44000000440000004400000044, 0x50000000500000005000000050, 0x55000000000000005500000000, 0x55000000550000000000000000]
private def b102 : Bound := (0x55000000550000005500000055, stock102, 5, 0x55000000540000005400000000)
private def cuts102 : List Bound := [b98, b100, b38, b70]
private theorem lower102 : Lower b102.1 stock102 b102.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7df9fdf3d78efd79f1edd3970bf76dd9bd72d58af569d1ad529507ef5db97cf1d386ed59b16cd19303e74d993c70d182e549912c50910dfb75e9ddb3568cf971e1cd931609f365c99d325488f161c18d121405eb55a95cb15284e951a14c911201e345891c305080e141810c10100) lower51
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock105 : List Word := [0x202000002020000020200000202, 0x300000003000000030000000300, 0x303000000000000030300000000, 0x303000003030000000000000000]
private def b105 : Bound := (0x303000003030000030300000303, stock105, 5, 0x303000003020000030200000000)
private def cuts105 : List Bound := [b97, b104, b41, b73]
private theorem lower105 : Lower b105.1 stock105 b105.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbbf6fbf3af4f7eb9f2f3e38f0bf7abd6bb72ad4b76a9d2b3628d07ef9bb67af1ab476e99b272e18b03e78b963a70a9436689923260890dfbb3e6dbb32e4d7ab1e2d3a30e09f3a3c69b322c4972a1c293220c05eb93a65ab12a456a91a252a10a01e383861a3028416281821220080) lower51
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock106 : List Word := [0x404000004040000040400000404, 0x500000005000000050000000500, 0x505000000000000050500000000, 0x505000005050000000000000000]
private def b106 : Bound := (0x505000005050000050500000505, stock106, 7, 0x505000005040000050400000400)
private def cuts106 : List Bound := [b42, b74, b98, b104]
private theorem lower106 : Lower b106.1 stock106 b106.2.2.2 7 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7f7cefd7b74f7e7d78e7c7970bf76f5caf56b54b766d58a7469507ef5f3c6ed5b3476e5d3866c59303e74f1c2e54b143664d182644910dfb776ccf97364d7a7568c7871609f3674c8f16344972654887061405eb572c4e9532456a552846851201e3470c0e1430416245080604100) lower53
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock108 : List Word := [0x1010000010100000101000001010, 0x1100000011000000110000001100, 0x1111000000000000111100000000, 0x1111000011110000000000000000]
private def b108 : Bound := (0x1111000011110000111100001111, stock108, 5, 0x1111000011100000111000000000)
private def cuts108 : List Bound := [b100, b104, b44, b76]
private theorem lower108 : Lower b108.1 stock108 b108.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xffefbf3fdebb72fbe7af1f9e3a70bf6ebd3bd6ab52bb66ad1b962a507eedbb37ce9b327ae5ab178e1a303e6cb933c68b123a64a913860a10dfaf3e3ddab362dba72e1d9a32609f2e3c39d2a3429b262c199222405ead3a35ca93225aa52a158a12201e2c3831c283021a242811820200) lower51
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock113 : List Word := [0x20002000200020002000200020002, 0x30000000300000003000000030000, 0x30003000000000003000300000000, 0x30003000300030000000000000000]
private def b113 : Bound := (0x30003000300030003000300030003, stock113, 7, 0x30003000300020003000200020000)
private def cuts113 : List Bound := [b49, b81, b97, b112]
private theorem lower113 : Lower b113.1 stock113 b113.2.2.2 7 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcdfbb6ecf7ebcf8d7ab4e8bf7aedc9f3a6ccb76acd8972a4c87ef9ebc5eb96ac76e9cb856a94a83e78e9c1e3868c3668c981628488efdbaf4cf9b2e4e7cb8f0c78b0e0af5aad48f1a2c4a74a8d0870a0c06ed9ab44e992a466c98b046890a02e58a940e1828426488900608080) lower53
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock114 : List Word := [0x40004000400040004000400040004, 0x50000000500000005000000050000, 0x50005000000000005000500000000, 0x50005000500050000000000000000]
private def b114 : Bound := (0x50005000500050005000500050005, stock114, 7, 0x50005000500040005000400040000)
private def cuts114 : List Bound := [b50, b82, b98, b112]
private theorem lower114 : Lower b114.1 stock114 b114.2.2.2 7 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7f7cdfb776cf7e7d78d7a7568bf76f5c9f3674cb766d5897265487ef5f3c5eb572c76e5d3856a55283e74f1c1e3470c3664d181624508efd7b74cf97364e7c7970c787160af56b548f16344a74695087061406ed5b344e9532466c593046851202e54b140e1430426449100604100) lower53
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock116 : List Word := [0x100010001000100010001000100010, 0x110000001100000011000000110000, 0x110011000000000011001100000000, 0x110011001100110000000000000000]
private def b116 : Bound := (0x110011001100110011001100110011, stock116, 7, 0x110011001100100011001000100000)
private def cuts116 : List Bound := [b52, b84, b100, b112]
private theorem lower116 : Lower b116.1 stock116 b116.2.2.2 7 :=
  lowerRelabelMasked (rowSelectPacked 0xffeff7adfaf76afbe7e78dba7668bf6ef5a9f2e74abb66e589b266487eedf3a5ead72a7ae5e385aa56283e6cf1a1e2c70a3a64e181a24608efcfb72cf8f362ebc7a70cb87260af4eb528f0e342ab46a508b062406ecdb324e8d3226ac5a304a852202e4cb120e0c3022a44a100a04200) lower53
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock120 : List Word := [0x1000100010001000100010001000100, 0x1010000010100000101000001010000, 0x1010101000000000101010100000000, 0x1010101010101010000000000000000]
private def b120 : Bound := (0x1010101010101010101010101010101, stock120, 5, 0x1010101010101000101010000000000)
private def cuts120 : List Bound := [b104, b112, b56, b88]
private theorem lower120 : Lower b120.1 stock120 b120.2.2.2 5 :=
  lowerRelabelMasked (rowSelectPacked 0xffdf7e7fddb766fbd76e5f9d3664bf5e7c7bd5a746bb566c5b9526447edd7a77cd97267ad56a578d16243e5c7873c587063a546853850604f7cf5e3f5cb562f3c74e1f1c3460b74e5c3b54a542b3464c1b14244076cd5a374c952272c54a170c1420364c583344850232444813040400) lower51
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock31 : List Word := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
private def b31 : Bound := (0xffffffff, stock31, 7, 0xfefeeca0)
private def cuts31 : List Bound := [b23, b21, b27, b30, b15]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks31 : treeBlock 0 (2 ^ stock31.length) (fun token =>
    closes b31.1 b31.2.2.2 cuts31 6 (rootState stock31 6 token)) = true := by
  decide +kernel
private theorem lower31 : Lower b31.1 stock31 b31.2.2.2 7 := by
  exact deriveLower b31.1 b31.2.2.2 stock31 cuts31 6
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower15) lower30) lower27) lower21) lower23)
    (by unfold cuts31; decide +kernel) checks31

private def stock47 : List Word := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]
private def b47 : Bound := (0xffff0000ffff, stock47, 8, 0xfffe0000eca0)
private def cuts47 : List Bound := [b39, b43, b45, b46, b15]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks47 : treeBlock 0 (2 ^ stock47.length) (fun token =>
    closes b47.1 b47.2.2.2 cuts47 7 (rootState stock47 7 token)) = true := by
  decide +kernel
private theorem lower47 : Lower b47.1 stock47 b47.2.2.2 8 := by
  exact deriveLower b47.1 b47.2.2.2 stock47 cuts47 7
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower15) lower46) lower45) lower43) lower39)
    (by unfold cuts47; decide +kernel) checks47

private def stock55 : List Word := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]
private def b55 : Bound := (0xff00ff00ff00ff, stock55, 8, 0xff00fe00fe00a0)
private def cuts55 : List Bound := [b53, b23, b39, b51, b54]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks55 : treeBlock 0 (2 ^ stock55.length) (fun token =>
    closes b55.1 b55.2.2.2 cuts55 7 (rootState stock55 7 token)) = true := by
  decide +kernel
private theorem lower55 : Lower b55.1 stock55 b55.2.2.2 8 := by
  exact deriveLower b55.1 b55.2.2.2 stock55 cuts55 7
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower54) lower51) lower39) lower23) lower53)
    (by unfold cuts55; decide +kernel) checks55

private def stock59 : List Word := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]
private def b59 : Bound := (0xf0f0f0f0f0f0f0f, stock59, 7, 0xf0f0f0e0e0e0c00)
private def cuts59 : List Bound := [b43, b51, b57, b58, b27]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks59 : treeBlock 0 (2 ^ stock59.length) (fun token =>
    closes b59.1 b59.2.2.2 cuts59 6 (rootState stock59 6 token)) = true := by
  decide +kernel
private theorem lower59 : Lower b59.1 stock59 b59.2.2.2 7 := by
  exact deriveLower b59.1 b59.2.2.2 stock59 cuts59 6
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower27) lower58) lower57) lower51) lower43)
    (by unfold cuts59; decide +kernel) checks59

private def stock61 : List Word := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]
private def b61 : Bound := (0x3333333333333333, stock61, 8, 0x3333333232322020)
private def cuts61 : List Bound := [b53, b45, b57, b60, b21]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks61 : treeBlock 0 (2 ^ stock61.length) (fun token =>
    closes b61.1 b61.2.2.2 cuts61 7 (rootState stock61 7 token)) = true := by
  decide +kernel
private theorem lower61 : Lower b61.1 stock61 b61.2.2.2 8 := by
  exact deriveLower b61.1 b61.2.2.2 stock61 cuts61 7
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower21) lower60) lower57) lower45) lower53)
    (by unfold cuts61; decide +kernel) checks61

private def stock62 : List Word := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]
private def b62 : Bound := (0x5555555555555555, stock62, 7, 0x5555555454544400)
private def cuts62 : List Bound := [b46, b54, b58, b60, b30]
private theorem lower62 : Lower b62.1 stock62 b62.2.2.2 7 :=
  lowerRelabelMasked (rowSelectPacked 0xffefef9fdebe78efcfaf1edcba70dfaf6e9ddab668cf8f2e1cd8b260bf6eed9bd6ae58af4ead1ad4aa509f2e6c99d2a6488f0e2c18d0a2407eedeb97ce9e386ecdab16cc9a305ead6a95ca96284e8d2a14c892203e6ce993c68e182e4ca912c48a101e2c6891c286080e0c2810c08200) lower59
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock79 : List Word := [0xaaaa000000000000aaaa, 0xcccc000000000000cccc, 0xf0f0000000000000f0f0, 0xff00000000000000ff00, 0xffff0000000000000000]
private def b79 : Bound := (0xffff000000000000ffff, stock79, 8, 0xfffe000000000000eca0)
private def cuts79 : List Bound := [b71, b75, b77, b78, b15]
private theorem lower79 : Lower b79.1 stock79 b79.2.2.2 8 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c03e78e9c3668c982e58a9426488901e3868c16284880e182840608080) lower47
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock87 : List Word := [0xaa00aa0000000000aa00aa, 0xcc00cc0000000000cc00cc, 0xf000f00000000000f000f0, 0xff00000000000000ff0000, 0xff00ff0000000000000000]
private def b87 : Bound := (0xff00ff0000000000ff00ff, stock87, 8, 0xff00fe0000000000fe00a0)
private def cuts87 : List Bound := [b85, b23, b71, b83, b86]
private theorem lower87 : Lower b87.1 stock87 b87.2.2.2 8 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c03e78e9c3668c982e58a9426488901e3868c16284880e182840608080) lower55
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock91 : List Word := [0xa0a0a0a000000000a0a0a0a, 0xc0c0c0c000000000c0c0c0c, 0xf000f00000000000f000f00, 0xf0f0000000000000f0f0000, 0xf0f0f0f0000000000000000]
private def b91 : Bound := (0xf0f0f0f000000000f0f0f0f, stock91, 7, 0xf0f0f0e000000000e0e0c00)
private def cuts91 : List Bound := [b75, b83, b89, b90, b27]
private theorem lower91 : Lower b91.1 stock91 b91.2.2.2 7 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c03e78e9c3668c982e58a9426488901e3868c16284880e182840608080) lower59
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock93 : List Word := [0x222222220000000022222222, 0x303030300000000030303030, 0x330033000000000033003300, 0x333300000000000033330000, 0x333333330000000000000000]
private def b93 : Bound := (0x333333330000000033333333, stock93, 8, 0x333333320000000032322020)
private def cuts93 : List Bound := [b85, b77, b89, b92, b21]
private theorem lower93 : Lower b93.1 stock93 b93.2.2.2 8 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c03e78e9c3668c982e58a9426488901e3868c16284880e182840608080) lower61
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock94 : List Word := [0x444444440000000044444444, 0x505050500000000050505050, 0x550055000000000055005500, 0x555500000000000055550000, 0x555555550000000000000000]
private def b94 : Bound := (0x555555550000000055555555, stock94, 7, 0x555555540000000054544400)
private def cuts94 : List Bound := [b78, b86, b90, b92, b30]
private theorem lower94 : Lower b94.1 stock94 b94.2.2.2 7 :=
  lowerRelabelMasked (rowSelectPacked 0xffefef9fdebe78efcfaf1edcba70dfaf6e9ddab668cf8f2e1cd8b2607eedeb97ce9e386ecdab16cc9a305ead6a95ca96284e8d2a14c89220bf6eed9bd6ae58af4ead1ad4aa509f2e6c99d2a6488f0e2c18d0a2403e6ce993c68e182e4ca912c48a101e2c6891c286080e0c2810c08200) lower59
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock103 : List Word := [0xaa000000aa000000aa000000aa, 0xcc000000cc000000cc000000cc, 0xf0000000f0000000f0000000f0, 0xff00000000000000ff00000000, 0xff000000ff0000000000000000]
private def b103 : Bound := (0xff000000ff000000ff000000ff, stock103, 8, 0xff000000fe000000fe000000a0)
private def cuts103 : List Bound := [b101, b39, b71, b99, b102]
private theorem lower103 : Lower b103.1 stock103 b103.2.2.2 8 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0bf7aedcb76acd8af5aad4a74a8d07ef9ebc76e9cb86ed9ab466c98b03e78e9c3668c982e58a942648890dfbb6ecd7ab4e8cf9b2e4c78b0e09f3a6cc972a4c88f1a2c4870a0c05eb96ac56a94a84e992a446890a01e3868c16284880e182840608080) lower55
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock107 : List Word := [0xa0a00000a0a00000a0a00000a0a, 0xc0c00000c0c00000c0c00000c0c, 0xf0000000f0000000f0000000f00, 0xf0f0000000000000f0f00000000, 0xf0f00000f0f0000000000000000]
private def b107 : Bound := (0xf0f00000f0f00000f0f00000f0f, stock107, 8, 0xf0f00000f0e00000f0e00000c00)
private def cuts107 : List Bound := [b106, b43, b75, b99, b105]
private theorem lower107 : Lower b107.1 stock107 b107.2.2.2 8 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7f7cefd7b74f7e7d78e7c7970bf76f5caf56b54b766d58a7469507ef5f3c6ed5b3476e5d3866c59303e74f1c2e54b143664d182644910dfb776ccf97364d7a7568c7871609f3674c8f16344972654887061405eb572c4e9532456a552846851201e3470c0e1430416245080604100) lower55
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock109 : List Word := [0x2222000022220000222200002222, 0x3030000030300000303000003030, 0x3300000033000000330000003300, 0x3333000000000000333300000000, 0x3333000033330000000000000000]
private def b109 : Bound := (0x3333000033330000333300003333, stock109, 8, 0x3333000033320000333200002020)
private def cuts109 : List Bound := [b101, b45, b77, b105, b108]
private theorem lower109 : Lower b109.1 stock109 b109.2.2.2 8 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbbf6f7eb9f2fbf3af4f3e38f0bf7abd6b76a9d2bb72ad4b3628d07ef9bb676e99b27af1ab472e18b03e78b9636689923a70a943260890dfbb3e6d7ab1e2dbb32e4d3a30e09f3a3c6972a1c29b322c493220c05eb93a656a91a25ab12a452a10a01e3838616281821a302841220080) lower55
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock110 : List Word := [0x4444000044440000444400004444, 0x5050000050500000505000005050, 0x5500000055000000550000005500, 0x5555000000000000555500000000, 0x5555000055550000000000000000]
private def b110 : Bound := (0x5555000055550000555500005555, stock110, 8, 0x5555000055540000555400004400)
private def cuts110 : List Bound := [b106, b46, b78, b102, b108]
private theorem lower110 : Lower b110.1 stock110 b110.2.2.2 8 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7df9efd79f1fdf3d78edd3970bf76dd9af569d1bd72d58ad529507ef5db96ed59b17cf1d386cd19303e74d992e549913c70d182c50910dfb75e9cf971e1ddb3568cd931609f365c98f161c19d325488d121405eb55a94e951a15cb15284c911201e345890e141811c305080c10100) lower55
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock115 : List Word := [0xa000a000a000a000a000a000a000a, 0xc000c000c000c000c000c000c000c, 0xf0000000f0000000f0000000f0000, 0xf000f00000000000f000f00000000, 0xf000f000f000f0000000000000000]
private def b115 : Bound := (0xf000f000f000f000f000f000f000f, stock115, 8, 0xf000f000f000e000f000e000e0000)
private def cuts115 : List Bound := [b113, b114, b51, b83, b99]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks115 : treeBlock 0 (2 ^ stock115.length) (fun token =>
    closes b115.1 b115.2.2.2 cuts115 7 (rootState stock115 7 token)) = true := by
  decide +kernel
private theorem lower115 : Lower b115.1 stock115 b115.2.2.2 8 := by
  exact deriveLower b115.1 b115.2.2.2 stock115 cuts115 7
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower99) lower83) lower51) lower114) lower113)
    (by unfold cuts115; decide +kernel) checks115

private def stock117 : List Word := [0x220022002200220022002200220022, 0x300030003000300030003000300030, 0x330000003300000033000000330000, 0x330033000000000033003300000000, 0x330033003300330000000000000000]
private def b117 : Bound := (0x330033003300330033003300330033, stock117, 10, 0x330033003300320033003200320020)
private def cuts117 : List Bound := [b53, b85, b101, b113, b116]
private def c117Index : Nat := 0xbf9af07ba12e04b612d80b22295aa502940a40a900a386864a1828419b325a99036400900240090023e18c1e2a38a82262823e06181820037a31e807909e407901e026f49a2d678998364118655e1d7805d097215a915e65705582558554154854a452813e64f813e04f053c04f013c04d8d22a48051c24494f8d39a4e603980e223804e003784da23490d203480a95205059416005801600561112444011004020d1820a00bc001
private def c117Edges : Nat := 0x153634029b1446b0cd215865042c034196014054a5000a526805e64c8d59a042accd085608032b0348d519442a8c7085405032a01c8d499a42a4ca08520683290288d419442a0c7085005032801c02e321016d9040b4c800596208d399a429cca084e068327028be67a74ef3d1306f89d7b794e0e63274f599080acc820466409eeb1f01758f40b0c7815163575931a01458a5b64c5003c62059b9a75d44d0a16468119933484c99406dc13a7a208433204020c81a0c640a13aa038055010029b2001498f00a0c696a433475201a01418d01ad89c056c4202a61c03465380a32840cf64e027b21010588166c69cab63420db02704d810ab5cc8152e6346da3144cb8d0255c668ab43282d702014b80d026805004a94c026ca440d6501f6b268db364cad6b2054b58d156669932d34095699a04cc130b5a08052d034024020012b10809387a047c387daca138d590966a6841b50420200140d000721800200c404202201b342bd10099886c8ac38065ca1831a50809726e046936022c96810e4b1c64c84db26365991a12ac8cd836408413203602001401018a13626500310280e0ca7050650808326cb3064e55832126c18d836069c13034201819b06fc13827e08403f03601d02000f40f017528403a936684fa208f310d9138700bc94301e49bae264b165ec84aaf6364d7b1506bcd0825e66c02f32a0dd82186e410827606e13903601d81580e40a866b29859a94028d49a36b5931c4ac80da563401a9a62468d01134668aad04c5928202a940d0030038da463400b80e1e58cd0e2c65001601040a31a1c50c7052806801401001a49e20458d0e2263829103400880800d71091352840336421d69a11c40ca013408401001000799400c40a001c638d149342ce31a3050ca063863802e93c688c9a1059900b36c68c1132818d98e0c8cca0058c8032233419098e0c80ca063e63802a636014b1a80a18d063c65109694090dc9a4e6d90004cc6841531c3ca81a008c0d004205402002900f8144e6e4da336c6c31b3368d118d0c88c6463c63001b0369d1013008809403c048f1362800e3183c498a2c2ac6821131c3ca81a28440a0036038aadc42552ca100b5909556c6402b631013b182a918a4820c5002534201219b4240cd003a65001a04284b32044558d212ac503163401ca99a0c54ca002c08009503400a8142648ca002405001332800998c00518c002465001693600ab1b2644cd802206cd08c3800c49bb2224b222ec6f11063684bb15c2418aa11ec4308e6201cb99b8e40cd862e65631032a18798a8c38c5012e06e09003600b81580400a801e01200e008683fa200df10d90f8703b69431d94a10cda4dc66526c33092d197c960e65908632c6c0b63430591a100d8cdc06466c03031501798a026410803206c00d01c6837a2095f10d90d8700d794302bc9bae1a4b039cc861c26420a731b85098d809cc5604262a01f31080e1881618684a8c3364c6195063010821806c00c02a0041941217d1080b87008a94200549b00264b070ec843076360439a1001ccd810987000492c0c1e1c08164dc207258085637002b15800d8809058708069372014961a198dcc0cc563026200c319b8418cac00c63e002314680e1c522e4dd90325940b6379c5b15ae0588241666f18b32b84598fa604c5091606e40b02b18580f802c04c00201000001f
private def c117Links : DagLinks :=
  dagLookupLinks c117Index c117Edges 14 5 12 7 6 6
private def c117Data : Forest := fun i => decodeNode 7 19 0xc99798f6c32159641b2c8165882cb1e58937198853c042ae1c4f640a6c794a50a7b1a506429ec56325226e21c3937878851f0f6382048c388f26d0e4b6181b4492c86c54324d9fb14400367ec42300f1ec9bb902b7326ce80a9cb100cc431a66e371099c9e346426666c340a1898a8d3141b278b9908d3202c63134c6ca18d5431a2863034c6898d08d19b1a0344604a780a8f8149f0283e04878ca0d3181c01c36084680d86c9b8e02b1d26c458d88b181231826650480d888150e0091c0103807068150c0130326c1e4b03994083360e63e098ac1c96046200662808020080f80 i
private def c117Sample : DagSample := (0x201804060081800860009808050101402050021400250200c04030080c00830008c08044101102044021100244200904024080900824008908014100502014020500214201044041081040841009048021100842021020840221200444011080440811008448005100142005020140205, 50)
private def c117Tags := dagTraceTags b117.1 50
  (dagTagBases stock117 0x3ff07c00f8000f83e0f801f0001ff801f003e00001fffc0007c0000000fffff 0x210842108421042108421084208421084210841084210842108210842108421 50) 9 c117Data
private def c117States := dagTrace b117.1 stock117 9 c117Data
private def c117MoveCert : List (DagMoveRecord 128) := [
  ([([(0xffffffff0000000000000000ffffffff, 0), (0xffffffff00000000, 32)], [(0xffffffff0000000000000000, 32)])], rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c03e78e9c3668c982e58a9426488901e3868c16284880e182840608080, rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c03e78e9c3668c982e58a9426488901e3868c16284880e182840608080),
  ([([(0xffff00000000ffffffff00000000ffff, 0), (0xffff000000000000ffff0000, 16)], [(0xffff000000000000ffff00000000, 16)])], rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0bf7aedcb76acd8af5aad4a74a8d0dfbb6ecd7ab4e8cf9b2e4c78b0e09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b03e78e9c3668c982e58a9426488905eb96ac56a94a84e992a446890a01e3868c16284880e182840608080, rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0bf7aedcb76acd8af5aad4a74a8d0dfbb6ecd7ab4e8cf9b2e4c78b0e09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b03e78e9c3668c982e58a9426488905eb96ac56a94a84e992a446890a01e3868c16284880e182840608080),
  ([([(0xffff000000000000000000000000ffff, 0), (0xffff0000, 16), (0xffff00000000, 32), (0xffff000000000000, 48)], [(0xffff0000000000000000, 48), (0xffff00000000000000000000, 32), (0xffff000000000000000000000000, 16)])], rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f07ef9ebc76e9cb86ed9ab466c98b0dfbb6ecd7ab4e8cf9b2e4c78b0e05eb96ac56a94a84e992a446890a0bf7aedcb76acd8af5aad4a74a8d03e78e9c3668c982e58a9426488909f3a6cc972a4c88f1a2c4870a0c01e3868c16284880e182840608080, rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0bf7aedcb76acd8af5aad4a74a8d07ef9ebc76e9cb86ed9ab466c98b03e78e9c3668c982e58a942648890dfbb6ecd7ab4e8cf9b2e4c78b0e09f3a6cc972a4c88f1a2c4870a0c05eb96ac56a94a84e992a446890a01e3868c16284880e182840608080),
  ([([(0xffff000000000000000000000000ffff, 0), (0xffff00000000000000000000, 16), (0xffff000000000000, 32), (0xffff0000, 48)], [(0xffff000000000000000000000000, 48), (0xffff0000000000000000, 32), (0xffff00000000, 16)])], rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0bf7aedcb76acd8af5aad4a74a8d07ef9ebc76e9cb86ed9ab466c98b03e78e9c3668c982e58a942648890dfbb6ecd7ab4e8cf9b2e4c78b0e09f3a6cc972a4c88f1a2c4870a0c05eb96ac56a94a84e992a446890a01e3868c16284880e182840608080, rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f07ef9ebc76e9cb86ed9ab466c98b0dfbb6ecd7ab4e8cf9b2e4c78b0e05eb96ac56a94a84e992a446890a0bf7aedcb76acd8af5aad4a74a8d03e78e9c3668c982e58a9426488909f3a6cc972a4c88f1a2c4870a0c01e3868c16284880e182840608080),
  ([([(0xffff0000ffff00000000ffff0000ffff, 0), (0xffff0000ffff0000, 48)], [(0xffff0000ffff0000000000000000, 48)])], rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f07ef9ebc76e9cb86ed9ab466c98b0bf7aedcb76acd8af5aad4a74a8d03e78e9c3668c982e58a942648890dfbb6ecd7ab4e8cf9b2e4c78b0e05eb96ac56a94a84e992a446890a09f3a6cc972a4c88f1a2c4870a0c01e3868c16284880e182840608080, rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f07ef9ebc76e9cb86ed9ab466c98b0bf7aedcb76acd8af5aad4a74a8d03e78e9c3668c982e58a942648890dfbb6ecd7ab4e8cf9b2e4c78b0e05eb96ac56a94a84e992a446890a09f3a6cc972a4c88f1a2c4870a0c01e3868c16284880e182840608080),
  ([([(0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f, 0), (0xf0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f0000, 12)])], rowSelectPacked 0xfffbefcdfbb6ecefdbaf4cf9b2e4f7ebcf8d7ab4e8e7cb8f0c78b0e0bf7aedc9f3a6ccaf5aad48f1a2c4b76acd8972a4c8a74a8d0870a0c07ef9ebc5eb96ac6ed9ab44e992a476e9cb856a94a866c98b046890a03e78e9c1e3868c2e58a940e182843668c98162848826488900608080, rowSelectPacked 0xfffbefcdfbb6ecefdbaf4cf9b2e4f7ebcf8d7ab4e8e7cb8f0c78b0e0bf7aedc9f3a6ccaf5aad48f1a2c4b76acd8972a4c8a74a8d0870a0c07ef9ebc5eb96ac6ed9ab44e992a476e9cb856a94a866c98b046890a03e78e9c1e3868c2e58a940e182843668c98162848826488900608080),
  ([([(0xf0f00f0f0000000000000000f0f00f0f, 0), (0xf0f000000000000000000000f0f0, 12), (0xf0f000000000000, 20), (0xf0f00f0f00000000, 32), (0xf0f000000000, 44)], [(0xf0f00000000000000000000, 44), (0xf0f00f0f0000000000000000, 32), (0xf0f00000000000000000, 20), (0xf0f000000000000000000000f0f0000, 12)])], rowSelectPacked 0xfffbefcdfbb6ecefdbaf4cf9b2e4f7ebcf8d7ab4e8e7cb8f0c78b0e07ef9ebc5eb96ac6ed9ab44e992a476e9cb856a94a866c98b046890a0bf7aedc9f3a6ccaf5aad48f1a2c4b76acd8972a4c8a74a8d0870a0c03e78e9c1e3868c2e58a940e182843668c98162848826488900608080, rowSelectPacked 0xfffbefcdfbb6ecefdbaf4cf9b2e4f7ebcf8d7ab4e8e7cb8f0c78b0e07ef9ebc5eb96ac6ed9ab44e992a476e9cb856a94a866c98b046890a0bf7aedc9f3a6ccaf5aad48f1a2c4b76acd8972a4c8a74a8d0870a0c03e78e9c1e3868c2e58a940e182843668c98162848826488900608080),
  ([([(0xf0f0000000000f0ff0f0000000000f0f, 0), (0xf0f0000000000000f0f0, 12), (0xf0f0000000000000f0f0000, 16), (0xf0f0000000000000f0f00000, 28)], [(0xf0f0000000000000f0f00000000, 28), (0xf0f0000000000000f0f000000000, 16), (0xf0f0000000000000f0f000000000000, 12)])], rowSelectPacked 0xfffbefcbf7aedcefdbaf4af5aad4f7ebcf8b76acd8e7cb8f0a74a8d0dfbb6ec9f3a6cccf9b2e48f1a2c4d7ab4e8972a4c8c78b0e0870a0c07ef9ebc3e78e9c6ed9ab42e58a9476e9cb83668c9866c98b026488905eb96ac1e3868c4e992a40e1828456a94a8162848846890a00608080, rowSelectPacked 0xfffbefcdfbb6ecefdbaf4cf9b2e4bf7aedc9f3a6ccaf5aad48f1a2c4f7ebcf8d7ab4e8e7cb8f0c78b0e0b76acd8972a4c8a74a8d0870a0c07ef9ebc5eb96ac6ed9ab44e992a43e78e9c1e3868c2e58a940e1828476e9cb856a94a866c98b046890a03668c98162848826488900608080),
  ([([(0xf0f00000000000000000000000000f0f, 0), (0xf0f0, 12), (0xf0f0000, 16), (0xf0f00000, 28), (0xf0f00000000, 32), (0xf0f000000000, 44), (0xf0f000000000000, 48), (0xf0f0000000000000, 60)], [(0xf0f0000000000000000, 60), (0xf0f00000000000000000, 48), (0xf0f00000000000000000000, 44), (0xf0f000000000000000000000, 32), (0xf0f000000000000000000000000, 28), (0xf0f0000000000000000000000000, 16), (0xf0f0000000000000000000000000000, 12)])], rowSelectPacked 0xfffbefc7ef9ebcefdbaf46ed9ab4f7ebcf876e9cb8e7cb8f066c98b0dfbb6ec5eb96accf9b2e44e992a4d7ab4e856a94a8c78b0e046890a0bf7aedc3e78e9caf5aad42e58a94b76acd83668c98a74a8d026488909f3a6cc1e3868c8f1a2c40e18284972a4c81628488870a0c00608080, rowSelectPacked 0xfffbefcdfbb6ecefdbaf4cf9b2e4bf7aedc9f3a6ccaf5aad48f1a2c47ef9ebc5eb96ac6ed9ab44e992a43e78e9c1e3868c2e58a940e18284f7ebcf8d7ab4e8e7cb8f0c78b0e0b76acd8972a4c8a74a8d0870a0c076e9cb856a94a866c98b046890a03668c98162848826488900608080),
  ([([(0xf0f00000000000000000000000000f0f, 0), (0xf0f0, 12), (0xf0f00000000000000000000, 16), (0xf0f000000000000, 20), (0xf0f000000000000000000000, 28), (0xf0f0000000000000, 32), (0xf0f0000, 48), (0xf0f00000, 60)], [(0xf0f000000000000000000000000, 60), (0xf0f0000000000000000000000000, 48), (0xf0f0000000000000000, 32), (0xf0f00000000, 28), (0xf0f00000000000000000, 20), (0xf0f000000000, 16), (0xf0f0000000000000000000000000000, 12)])], rowSelectPacked 0xfffbefcbf7aedcefdbaf4af5aad4f7ebcf8b76acd8e7cb8f0a74a8d07ef9ebc3e78e9c6ed9ab42e58a9476e9cb83668c9866c98b02648890dfbb6ec9f3a6cccf9b2e48f1a2c4d7ab4e8972a4c8c78b0e0870a0c05eb96ac1e3868c4e992a40e1828456a94a8162848846890a00608080, rowSelectPacked 0xfffbefcdfbb6ecefdbaf4cf9b2e47ef9ebc5eb96ac6ed9ab44e992a4f7ebcf8d7ab4e8e7cb8f0c78b0e076e9cb856a94a866c98b046890a0bf7aedc9f3a6ccaf5aad48f1a2c43e78e9c1e3868c2e58a940e18284b76acd8972a4c8a74a8d0870a0c03668c98162848826488900608080),
  ([([(0xf0f00000f0f0000000000f0f00000f0f, 0), (0xf0f00000f0f0, 12), (0xf0f00000f0f0000, 48), (0xf0f00000f0f00000, 60)], [(0xf0f00000f0f0000000000000000, 60), (0xf0f00000f0f00000000000000000, 48), (0xf0f00000f0f00000000000000000000, 12)])], rowSelectPacked 0xfffbefc7ef9ebcefdbaf46ed9ab4f7ebcf876e9cb8e7cb8f066c98b0bf7aedc3e78e9caf5aad42e58a94b76acd83668c98a74a8d02648890dfbb6ec5eb96accf9b2e44e992a4d7ab4e856a94a8c78b0e046890a09f3a6cc1e3868c8f1a2c40e18284972a4c81628488870a0c00608080, rowSelectPacked 0xfffbefcdfbb6ecefdbaf4cf9b2e47ef9ebc5eb96ac6ed9ab44e992a4bf7aedc9f3a6ccaf5aad48f1a2c43e78e9c1e3868c2e58a940e18284f7ebcf8d7ab4e8e7cb8f0c78b0e076e9cb856a94a866c98b046890a0b76acd8972a4c8a74a8d0870a0c03668c98162848826488900608080),
  ([([(0xf0f0000000000f0ff0f0000000000f0f, 0), (0xf0f0000000000000f0f000000000, 12), (0xf0f0000000000000f0f00000, 16), (0xf0f0000000000000f0f0, 28)], [(0xf0f0000000000000f0f000000000000, 28), (0xf0f0000000000000f0f00000000, 16), (0xf0f0000000000000f0f0000, 12)])], rowSelectPacked 0xfffbefcdfbb6ecefdbaf4cf9b2e4bf7aedc9f3a6ccaf5aad48f1a2c4f7ebcf8d7ab4e8e7cb8f0c78b0e0b76acd8972a4c8a74a8d0870a0c07ef9ebc5eb96ac6ed9ab44e992a43e78e9c1e3868c2e58a940e1828476e9cb856a94a866c98b046890a03668c98162848826488900608080, rowSelectPacked 0xfffbefcbf7aedcefdbaf4af5aad4f7ebcf8b76acd8e7cb8f0a74a8d0dfbb6ec9f3a6cccf9b2e48f1a2c4d7ab4e8972a4c8c78b0e0870a0c07ef9ebc3e78e9c6ed9ab42e58a9476e9cb83668c9866c98b026488905eb96ac1e3868c4e992a40e1828456a94a8162848846890a00608080),
  ([([(0xf0f00000000000000000000000000f0f, 0), (0xf0f0000000000000000000000000, 12), (0xf0f00000, 16), (0xf0f000000000000, 20), (0xf0f0, 28), (0xf0f00000000, 32), (0xf0f0000000000000, 48), (0xf0f000000000, 60)], [(0xf0f00000000000000000000, 60), (0xf0f0000000000000000, 48), (0xf0f000000000000000000000, 32), (0xf0f0000000000000000000000000000, 28), (0xf0f00000000000000000, 20), (0xf0f000000000000000000000000, 16), (0xf0f0000, 12)])], rowSelectPacked 0xfffbefcdfbb6ecefdbaf4cf9b2e47ef9ebc5eb96ac6ed9ab44e992a4f7ebcf8d7ab4e8e7cb8f0c78b0e076e9cb856a94a866c98b046890a0bf7aedc9f3a6ccaf5aad48f1a2c43e78e9c1e3868c2e58a940e18284b76acd8972a4c8a74a8d0870a0c03668c98162848826488900608080, rowSelectPacked 0xfffbefcbf7aedcefdbaf4af5aad4f7ebcf8b76acd8e7cb8f0a74a8d07ef9ebc3e78e9c6ed9ab42e58a9476e9cb83668c9866c98b02648890dfbb6ec9f3a6cccf9b2e48f1a2c4d7ab4e8972a4c8c78b0e0870a0c05eb96ac1e3868c4e992a40e1828456a94a8162848846890a00608080),
  ([([(0xf0f0f0f00f0f0f0ff0f0f0f00f0f0f0f, 0), (0xf0f0f0f000000000f0f0f0f0, 28)], [(0xf0f0f0f000000000f0f0f0f00000000, 28)])], rowSelectPacked 0xfffbefcbf7aedcefdbaf4af5aad4dfbb6ec9f3a6cccf9b2e48f1a2c4f7ebcf8b76acd8e7cb8f0a74a8d0d7ab4e8972a4c8c78b0e0870a0c07ef9ebc3e78e9c6ed9ab42e58a945eb96ac1e3868c4e992a40e1828476e9cb83668c9866c98b0264889056a94a8162848846890a00608080, rowSelectPacked 0xfffbefcbf7aedcefdbaf4af5aad4dfbb6ec9f3a6cccf9b2e48f1a2c4f7ebcf8b76acd8e7cb8f0a74a8d0d7ab4e8972a4c8c78b0e0870a0c07ef9ebc3e78e9c6ed9ab42e58a945eb96ac1e3868c4e992a40e1828476e9cb83668c9866c98b0264889056a94a8162848846890a00608080),
  ([([(0xf0f0f0f000000000000000000f0f0f0f, 0), (0xf0f0f0f0, 28), (0xf0f0f0f00000000, 32), (0xf0f0f0f000000000, 60)], [(0xf0f0f0f0000000000000000, 60), (0xf0f0f0f00000000000000000, 32), (0xf0f0f0f000000000000000000000000, 28)])], rowSelectPacked 0xfffbefc7ef9ebcefdbaf46ed9ab4dfbb6ec5eb96accf9b2e44e992a4f7ebcf876e9cb8e7cb8f066c98b0d7ab4e856a94a8c78b0e046890a0bf7aedc3e78e9caf5aad42e58a949f3a6cc1e3868c8f1a2c40e18284b76acd83668c98a74a8d02648890972a4c81628488870a0c00608080, rowSelectPacked 0xfffbefcbf7aedcefdbaf4af5aad4dfbb6ec9f3a6cccf9b2e48f1a2c47ef9ebc3e78e9c6ed9ab42e58a945eb96ac1e3868c4e992a40e18284f7ebcf8b76acd8e7cb8f0a74a8d0d7ab4e8972a4c8c78b0e0870a0c076e9cb83668c9866c98b0264889056a94a8162848846890a00608080),
  ([([(0xf0f000000f0f00000000f0f000000f0f, 0), (0xf0f000000000000, 20), (0xf0f00000000000000000f0f0, 28), (0xf0f000000f0f0000, 48), (0xf0f00000, 76)], [(0xf0f000000000000000000000000, 76), (0xf0f000000f0f0000000000000000, 48), (0xf0f00000000000000000f0f00000000, 28), (0xf0f00000000000000000, 20)])], rowSelectPacked 0xfffbefcbf7aedcefdbaf4af5aad47ef9ebc3e78e9c6ed9ab42e58a94f7ebcf8b76acd8e7cb8f0a74a8d076e9cb83668c9866c98b02648890dfbb6ec9f3a6cccf9b2e48f1a2c45eb96ac1e3868c4e992a40e18284d7ab4e8972a4c8c78b0e0870a0c056a94a8162848846890a00608080, rowSelectPacked 0xfffbefcbf7aedcefdbaf4af5aad47ef9ebc3e78e9c6ed9ab42e58a94f7ebcf8b76acd8e7cb8f0a74a8d076e9cb83668c9866c98b02648890dfbb6ec9f3a6cccf9b2e48f1a2c45eb96ac1e3868c4e992a40e18284d7ab4e8972a4c8c78b0e0870a0c056a94a8162848846890a00608080),
  ([([(0xf0f0f0f000000000000000000f0f0f0f, 0), (0xf0f0f0f00000000000000000, 28), (0xf0f0f0f000000000, 32), (0xf0f0f0f0, 60)], [(0xf0f0f0f000000000000000000000000, 60), (0xf0f0f0f0000000000000000, 32), (0xf0f0f0f00000000, 28)])], rowSelectPacked 0xfffbefcbf7aedcefdbaf4af5aad4dfbb6ec9f3a6cccf9b2e48f1a2c47ef9ebc3e78e9c6ed9ab42e58a945eb96ac1e3868c4e992a40e18284f7ebcf8b76acd8e7cb8f0a74a8d0d7ab4e8972a4c8c78b0e0870a0c076e9cb83668c9866c98b0264889056a94a8162848846890a00608080, rowSelectPacked 0xfffbefc7ef9ebcefdbaf46ed9ab4dfbb6ec5eb96accf9b2e44e992a4f7ebcf876e9cb8e7cb8f066c98b0d7ab4e856a94a8c78b0e046890a0bf7aedc3e78e9caf5aad42e58a949f3a6cc1e3868c8f1a2c40e18284b76acd83668c98a74a8d02648890972a4c81628488870a0c00608080),
  ([([(0xf0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f, 0), (0xf0f0f0f0f0f0f0f0, 60)], [(0xf0f0f0f0f0f0f0f0000000000000000, 60)])], rowSelectPacked 0xfffbefc7ef9ebcefdbaf46ed9ab4dfbb6ec5eb96accf9b2e44e992a4bf7aedc3e78e9caf5aad42e58a949f3a6cc1e3868c8f1a2c40e18284f7ebcf876e9cb8e7cb8f066c98b0d7ab4e856a94a8c78b0e046890a0b76acd83668c98a74a8d02648890972a4c81628488870a0c00608080, rowSelectPacked 0xfffbefc7ef9ebcefdbaf46ed9ab4dfbb6ec5eb96accf9b2e44e992a4bf7aedc3e78e9caf5aad42e58a949f3a6cc1e3868c8f1a2c40e18284f7ebcf876e9cb8e7cb8f066c98b0d7ab4e856a94a8c78b0e046890a0b76acd83668c98a74a8d02648890972a4c81628488870a0c00608080),
  ([([(0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0x50505050505050505050505050505050, 3)])], rowSelectPacked 0xffefef9fdebe78efcfaf1edcba70dfaf6e9ddab668cf8f2e1cd8b260bf6eed9bd6ae58af4ead1ad4aa509f2e6c99d2a6488f0e2c18d0a2407eedeb97ce9e386ecdab16cc9a305ead6a95ca96284e8d2a14c892203e6ce993c68e182e4ca912c48a101e2c6891c286080e0c2810c08200, rowSelectPacked 0xffefef9fdebe78efcfaf1edcba70dfaf6e9ddab668cf8f2e1cd8b260bf6eed9bd6ae58af4ead1ad4aa509f2e6c99d2a6488f0e2c18d0a2407eedeb97ce9e386ecdab16cc9a305ead6a95ca96284e8d2a14c892203e6ce993c68e182e4ca912c48a101e2c6891c286080e0c2810c08200),
  ([([(0xa5a5a5a50000000000000000a5a5a5a5, 0), (0xa0a0a0a00000000000000000a0a0a0a, 3), (0x5050505000000000, 29), (0xa5a5a5a500000000, 32), (0xa0a0a0a00000000, 35)], [(0x505050500000000000000000, 35), (0xa5a5a5a50000000000000000, 32), (0xa0a0a0a0000000000000000, 29), (0x50505050000000000000000050505050, 3)])], rowSelectPacked 0xffefef9fdebe78efcfaf1edcba70dfaf6e9ddab668cf8f2e1cd8b2607eedeb97ce9e386ecdab16cc9a305ead6a95ca96284e8d2a14c89220bf6eed9bd6ae58af4ead1ad4aa509f2e6c99d2a6488f0e2c18d0a2403e6ce993c68e182e4ca912c48a101e2c6891c286080e0c2810c08200, rowSelectPacked 0xffefef9fdebe78efcfaf1edcba70dfaf6e9ddab668cf8f2e1cd8b2607eedeb97ce9e386ecdab16cc9a305ead6a95ca96284e8d2a14c89220bf6eed9bd6ae58af4ead1ad4aa509f2e6c99d2a6488f0e2c18d0a2403e6ce993c68e182e4ca912c48a101e2c6891c286080e0c2810c08200),
  ([([(0xa5a500000000a5a5a5a500000000a5a5, 0), (0xa0a000000000a0a0a0a000000000a0a, 3), (0x505000000000000050500000, 13), (0xa5a5000000000000a5a50000, 16), (0xa0a0000000000000a0a0000, 19)], [(0x5050000000000000505000000000, 19), (0xa5a5000000000000a5a500000000, 16), (0xa0a0000000000000a0a00000000, 13), (0x50500000000050505050000000005050, 3)])], rowSelectPacked 0xffefef9fdebe78efcfaf1edcba70bf6eed9bd6ae58af4ead1ad4aa50dfaf6e9ddab668cf8f2e1cd8b2609f2e6c99d2a6488f0e2c18d0a2407eedeb97ce9e386ecdab16cc9a303e6ce993c68e182e4ca912c48a105ead6a95ca96284e8d2a14c892201e2c6891c286080e0c2810c08200, rowSelectPacked 0xffefef9fdebe78efcfaf1edcba70bf6eed9bd6ae58af4ead1ad4aa50dfaf6e9ddab668cf8f2e1cd8b2609f2e6c99d2a6488f0e2c18d0a2407eedeb97ce9e386ecdab16cc9a303e6ce993c68e182e4ca912c48a105ead6a95ca96284e8d2a14c892201e2c6891c286080e0c2810c08200),
  ([([(0xa5a5000000000000000000000000a5a5, 0), (0xa0a0000000000000000000000000a0a, 3), (0x50500000, 13), (0xa5a50000, 16), (0xa0a0000, 19), (0x505000000000, 29), (0xa5a500000000, 32), (0xa0a00000000, 35), (0x5050000000000000, 45), (0xa5a5000000000000, 48), (0xa0a000000000000, 51)], [(0x50500000000000000000, 51), (0xa5a50000000000000000, 48), (0xa0a0000000000000000, 45), (0x505000000000000000000000, 35), (0xa5a500000000000000000000, 32), (0xa0a00000000000000000000, 29), (0x5050000000000000000000000000, 19), (0xa5a5000000000000000000000000, 16), (0xa0a000000000000000000000000, 13), (0x50500000000000000000000000005050, 3)])], rowSelectPacked 0xffefef9fdebe78efcfaf1edcba707eedeb97ce9e386ecdab16cc9a30dfaf6e9ddab668cf8f2e1cd8b2605ead6a95ca96284e8d2a14c89220bf6eed9bd6ae58af4ead1ad4aa503e6ce993c68e182e4ca912c48a109f2e6c99d2a6488f0e2c18d0a2401e2c6891c286080e0c2810c08200, rowSelectPacked 0xffefef9fdebe78efcfaf1edcba70bf6eed9bd6ae58af4ead1ad4aa507eedeb97ce9e386ecdab16cc9a303e6ce993c68e182e4ca912c48a10dfaf6e9ddab668cf8f2e1cd8b2609f2e6c99d2a6488f0e2c18d0a2405ead6a95ca96284e8d2a14c892201e2c6891c286080e0c2810c08200),
  ([([(0xa0a00505a0a00505a0a00505a0a00505, 0), (0xa0a00000a0a00000a0a00000a0a, 3), (0x5050000050500000505000005050, 12), (0xa0a00000a0a00000a0a00000a0a0, 15)], [(0x5050000050500000505000005050000, 15), (0xa0a00000a0a00000a0a00000a0a0000, 12), (0x50500000505000005050000050500000, 3)])], rowSelectPacked 0xffbfeedfdbbe6cef9fae5ed9ba64f7afce9f5abc68e78f8e1e58b860bf3eecdbd3ae4caf1eac5ad1aa44b72ecc9b52ac48a70e8c1a50a8407ebdead7cb9e2c6e9daa56c99a2476adca974a9c28668d8a164898203e3ce8d3c38e0c2e1ca852c18a04362cc893428c08260c8812408800, rowSelectPacked 0xffefef9dfaf6e9efcfaf1cf8f2e1fdebe78ddab668edcba70cd8b260bf6eed99f2e6c9af4ead18f0e2c1bd6ae589d2a648ad4aa508d0a2407eedeb95ead6a96ecdab14e8d2a17ce9e385ca96286cc9a304c892203e6ce991e2c6892e4ca910e0c2813c68e181c286082c48a100c08200),
  ([([(0xa0a005050000000000000000a0a00505, 0), (0xa0a000000000000000000000a0a, 3), (0x5050000000000000000000005050, 12), (0xa0a000000000000000000000a0a0, 15), (0x505000000000000, 17), (0xa0a000000000000, 20), (0x5050000000000000, 29), (0xa0a0050500000000, 32), (0xa0a00000000, 35), (0x505000000000, 44), (0xa0a000000000, 47)], [(0x50500000000000000000000, 47), (0xa0a00000000000000000000, 44), (0x505000000000000000000000, 35), (0xa0a005050000000000000000, 32), (0xa0a0000000000000000, 29), (0x50500000000000000000, 20), (0xa0a00000000000000000, 17), (0x5050000000000000000000005050000, 15), (0xa0a000000000000000000000a0a0000, 12), (0x50500000000000000000000050500000, 3)])], rowSelectPacked 0xffbfeedfdbbe6cef9fae5ed9ba64f7afce9f5abc68e78f8e1e58b8607ebdead7cb9e2c6e9daa56c99a2476adca974a9c28668d8a16489820bf3eecdbd3ae4caf1eac5ad1aa44b72ecc9b52ac48a70e8c1a50a8403e3ce8d3c38e0c2e1ca852c18a04362cc893428c08260c8812408800, rowSelectPacked 0xffefef9dfaf6e9efcfaf1cf8f2e1fdebe78ddab668edcba70cd8b2607eedeb95ead6a96ecdab14e8d2a17ce9e385ca96286cc9a304c89220bf6eed99f2e6c9af4ead18f0e2c1bd6ae589d2a648ad4aa508d0a2403e6ce991e2c6892e4ca910e0c2813c68e181c286082c48a100c08200),
  ([([(0xa0a0000000000505a0a0000000000505, 0), (0xa0a0000000000000a0a, 3), (0x50500000000000005050, 12), (0xa0a0000000000000a0a0, 15), (0x50500000000000005050000, 16), (0xa0a0000000000000a0a0000, 19), (0x505000000000000050500000, 28), (0xa0a0000000000000a0a00000, 31)], [(0x505000000000000050500000000, 31), (0xa0a0000000000000a0a00000000, 28), (0x5050000000000000505000000000, 19), (0xa0a0000000000000a0a000000000, 16), (0x5050000000000000505000000000000, 15), (0xa0a0000000000000a0a000000000000, 12), (0x50500000000000005050000000000000, 3)])], rowSelectPacked 0xff7feddfd7be5cef5fad5ed5ba54f76fcd9f56bc58e74f8d1e54b850df3f6cddd3b64ccf1f2c5cd1b244d72f4c9d52b448c70f0c1c50b0407e7de9d7c79e1c6e5da956c59a14766dc997469c18664d89164498105e3d68d5c3960c4e1d2854c19204562d4895429408460d0814409000, rowSelectPacked 0xffefef9dfaf6e9efcfaf1cf8f2e1bf6eed99f2e6c9af4ead18f0e2c1fdebe78ddab668edcba70cd8b260bd6ae589d2a648ad4aa508d0a2407eedeb95ead6a96ecdab14e8d2a13e6ce991e2c6892e4ca910e0c2817ce9e385ca96286cc9a304c892203c68e181c286082c48a100c08200),
  ([([(0xa0a00000000000000000000000000505, 0), (0xa0a, 3), (0x5050, 12), (0xa0a0, 15), (0x5050000, 16), (0xa0a0000, 19), (0x50500000, 28), (0xa0a00000, 31), (0x50500000000, 32), (0xa0a00000000, 35), (0x505000000000, 44), (0xa0a000000000, 47), (0x505000000000000, 48), (0xa0a000000000000, 51), (0x5050000000000000, 60), (0xa0a0000000000000, 63)], [(0x5050000000000000000, 63), (0xa0a0000000000000000, 60), (0x50500000000000000000, 51), (0xa0a00000000000000000, 48), (0x50500000000000000000000, 47), (0xa0a00000000000000000000, 44), (0x505000000000000000000000, 35), (0xa0a000000000000000000000, 32), (0x505000000000000000000000000, 31), (0xa0a000000000000000000000000, 28), (0x5050000000000000000000000000, 19), (0xa0a0000000000000000000000000, 16), (0x5050000000000000000000000000000, 15), (0xa0a0000000000000000000000000000, 12), (0x50500000000000000000000000000000, 3)])], rowSelectPacked 0xfeffebdfcfbe3ceedfab5ecdba34f6efcb9f4ebc38e6cf8b1e4cb830debf6addcbb62cce9f2a5cc9b224d6af4a9d4ab428c68f0a1c48b020be7ee9dbc7ae1cae5ea95ac5aa14b66ec99b46ac18a64e891a44a8109e3e68d9c3a60c8e1e2858c1a204962e489942a408860e081840a000, rowSelectPacked 0xffefef9dfaf6e9efcfaf1cf8f2e1bf6eed99f2e6c9af4ead18f0e2c17eedeb95ead6a96ecdab14e8d2a13e6ce991e2c6892e4ca910e0c281fdebe78ddab668edcba70cd8b260bd6ae589d2a648ad4aa508d0a2407ce9e385ca96286cc9a304c892203c68e181c286082c48a100c08200),
  ([([(0xa0a0000000000505a0a0000000000505, 0), (0xa0a0000000000000a0a, 3), (0x5050000000000000505000000000, 12), (0x505000000000000050500000, 13), (0xa0a0000000000000a0a000000000, 15), (0xa0a0000000000000a0a00000, 16), (0x50500000000000005050, 28), (0xa0a0000000000000a0a0, 31)], [(0x5050000000000000505000000000000, 31), (0xa0a0000000000000a0a000000000000, 28), (0x505000000000000050500000000, 16), (0x50500000000000005050000, 15), (0xa0a0000000000000a0a00000000, 13), (0xa0a0000000000000a0a0000, 12), (0x50500000000000005050000000000000, 3)])], rowSelectPacked 0xffbfeedfdbbe6cef9fae5ed9ba64bf3eecdbd3ae4caf1eac5ad1aa44f7afce9f5abc68e78f8e1e58b860b72ecc9b52ac48a70e8c1a50a8407ebdead7cb9e2c6e9daa56c99a243e3ce8d3c38e0c2e1ca852c18a0476adca974a9c28668d8a16489820362cc893428c08260c8812408800, rowSelectPacked 0xffefef9bf6eed9efcfaf1af4ead1fdebe78bd6ae58edcba70ad4aa50dfaf6e99f2e6c9cf8f2e18f0e2c1ddab6689d2a648cd8b2608d0a2407eedeb93e6ce996ecdab12e4ca917ce9e383c68e186cc9a302c48a105ead6a91e2c6894e8d2a10e0c2815ca96281c286084c892200c08200),
  ([([(0xa0a00000000000000000000000000505, 0), (0xa0a, 3), (0x5050000000000000000000000000, 12), (0x50500000, 13), (0xa0a0000000000000000000000000, 15), (0xa0a00000, 16), (0x505000000000000, 17), (0xa0a000000000000, 20), (0x5050, 28), (0xa0a0, 31), (0x50500000000, 32), (0xa0a00000000, 35), (0x5050000000000000, 45), (0xa0a0000000000000, 48), (0x505000000000, 60), (0xa0a000000000, 63)], [(0x50500000000000000000000, 63), (0xa0a00000000000000000000, 60), (0x5050000000000000000, 48), (0xa0a0000000000000000, 45), (0x505000000000000000000000, 35), (0xa0a000000000000000000000, 32), (0x5050000000000000000000000000000, 31), (0xa0a0000000000000000000000000000, 28), (0x50500000000000000000, 20), (0xa0a00000000000000000, 17), (0x505000000000000000000000000, 16), (0x5050000, 15), (0xa0a000000000000000000000000, 13), (0xa0a0000, 12), (0x50500000000000000000000000000000, 3)])], rowSelectPacked 0xffbfeedfdbbe6cef9fae5ed9ba647ebdead7cb9e2c6e9daa56c99a24f7afce9f5abc68e78f8e1e58b86076adca974a9c28668d8a16489820bf3eecdbd3ae4caf1eac5ad1aa443e3ce8d3c38e0c2e1ca852c18a04b72ecc9b52ac48a70e8c1a50a840362cc893428c08260c8812408800, rowSelectPacked 0xffefef9bf6eed9efcfaf1af4ead1fdebe78bd6ae58edcba70ad4aa507eedeb93e6ce996ecdab12e4ca917ce9e383c68e186cc9a302c48a10dfaf6e99f2e6c9cf8f2e18f0e2c1ddab6689d2a648cd8b2608d0a2405ead6a91e2c6894e8d2a10e0c2815ca96281c286084c892200c08200),
  ([([(0xa0a0a0a005050505a0a0a0a005050505, 0), (0xa0a0a0a000000000a0a0a0a, 3), (0x505050500000000050505050, 28), (0xa0a0a0a000000000a0a0a0a0, 31)], [(0x5050505000000000505050500000000, 31), (0xa0a0a0a000000000a0a0a0a00000000, 28), (0x50505050000000005050505000000000, 3)])], rowSelectPacked 0xff7feddfd7be5cef5fad5ed5ba54df3f6cddd3b64ccf1f2c5cd1b244f76fcd9f56bc58e74f8d1e54b850d72f4c9d52b448c70f0c1c50b0407e7de9d7c79e1c6e5da956c59a145e3d68d5c3960c4e1d2854c19204766dc997469c18664d8916449810562d4895429408460d0814409000, rowSelectPacked 0xffefef9bf6eed9efcfaf1af4ead1dfaf6e99f2e6c9cf8f2e18f0e2c1fdebe78bd6ae58edcba70ad4aa50ddab6689d2a648cd8b2608d0a2407eedeb93e6ce996ecdab12e4ca915ead6a91e2c6894e8d2a10e0c2817ce9e383c68e186cc9a302c48a105ca96281c286084c892200c08200),
  ([([(0xa0a0a0a0000000000000000005050505, 0), (0xa0a0a0a, 3), (0x50505050, 28), (0xa0a0a0a0, 31), (0x505050500000000, 32), (0xa0a0a0a00000000, 35), (0x5050505000000000, 60), (0xa0a0a0a000000000, 63)], [(0x50505050000000000000000, 63), (0xa0a0a0a0000000000000000, 60), (0x505050500000000000000000, 35), (0xa0a0a0a00000000000000000, 32), (0x5050505000000000000000000000000, 31), (0xa0a0a0a000000000000000000000000, 28), (0x50505050000000000000000000000000, 3)])], rowSelectPacked 0xfeffebdfcfbe3ceedfab5ecdba34debf6addcbb62cce9f2a5cc9b224f6efcb9f4ebc38e6cf8b1e4cb830d6af4a9d4ab428c68f0a1c48b020be7ee9dbc7ae1cae5ea95ac5aa149e3e68d9c3a60c8e1e2858c1a204b66ec99b46ac18a64e891a44a810962e489942a408860e081840a000, rowSelectPacked 0xffefef9bf6eed9efcfaf1af4ead1dfaf6e99f2e6c9cf8f2e18f0e2c17eedeb93e6ce996ecdab12e4ca915ead6a91e2c6894e8d2a10e0c281fdebe78bd6ae58edcba70ad4aa50ddab6689d2a648cd8b2608d0a2407ce9e383c68e186cc9a302c48a105ca96281c286084c892200c08200),
  ([([(0xa0a00000050500000000a0a000000505, 0), (0xa0a00000000000000000a0a, 3), (0x505000000000000, 17), (0xa0a000000000000, 20), (0x505000000000000000005050, 28), (0xa0a00000000000000000a0a0, 31), (0x5050000000000000, 45), (0xa0a0000005050000, 48), (0xa0a0000, 51), (0x50500000, 76), (0xa0a00000, 79)], [(0x505000000000000000000000000, 79), (0xa0a000000000000000000000000, 76), (0x5050000000000000000000000000, 51), (0xa0a0000005050000000000000000, 48), (0xa0a0000000000000000, 45), (0x5050000000000000000050500000000, 31), (0xa0a00000000000000000a0a00000000, 28), (0x50500000000000000000, 20), (0xa0a00000000000000000, 17), (0x50500000000000000000505000000000, 3)])], rowSelectPacked 0xff7feddfd7be5cef5fad5ed5ba547e7de9d7c79e1c6e5da956c59a14f76fcd9f56bc58e74f8d1e54b850766dc997469c18664d8916449810df3f6cddd3b64ccf1f2c5cd1b2445e3d68d5c3960c4e1d2854c19204d72f4c9d52b448c70f0c1c50b040562d4895429408460d0814409000, rowSelectPacked 0xffefef9bf6eed9efcfaf1af4ead17eedeb93e6ce996ecdab12e4ca91fdebe78bd6ae58edcba70ad4aa507ce9e383c68e186cc9a302c48a10dfaf6e99f2e6c9cf8f2e18f0e2c15ead6a91e2c6894e8d2a10e0c281ddab6689d2a648cd8b2608d0a2405ca96281c286084c892200c08200),
  ([([(0xa0a00000000000000000000000000505, 0), (0xa0a, 3), (0x505000000000, 12), (0x505000000000000000000000, 13), (0xa0a000000000, 15), (0xa0a000000000000000000000, 16), (0x5050, 28), (0xa0a0, 31), (0x505000000000000, 32), (0xa0a000000000000, 35), (0x5050000, 48), (0xa0a0000, 51), (0x5050000000000000, 60), (0xa0a0000000000000, 63), (0x50500000, 76), (0xa0a00000, 79)], [(0x505000000000000000000000000, 79), (0xa0a000000000000000000000000, 76), (0x5050000000000000000, 63), (0xa0a0000000000000000, 60), (0x5050000000000000000000000000, 51), (0xa0a0000000000000000000000000, 48), (0x50500000000000000000, 35), (0xa0a00000000000000000, 32), (0x5050000000000000000000000000000, 31), (0xa0a0000000000000000000000000000, 28), (0x50500000000, 16), (0x50500000000000000000000, 15), (0xa0a00000000, 13), (0xa0a00000000000000000000, 12), (0x50500000000000000000000000000000, 3)])], rowSelectPacked 0xfeffebdfcfbe3ceedfab5ecdba34be7ee9dbc7ae1cae5ea95ac5aa14f6efcb9f4ebc38e6cf8b1e4cb830b66ec99b46ac18a64e891a44a810debf6addcbb62cce9f2a5cc9b2249e3e68d9c3a60c8e1e2858c1a204d6af4a9d4ab428c68f0a1c48b020962e489942a408860e081840a000, rowSelectPacked 0xffefef9bf6eed9efcfaf1af4ead17eedeb93e6ce996ecdab12e4ca91dfaf6e99f2e6c9cf8f2e18f0e2c15ead6a91e2c6894e8d2a10e0c281fdebe78bd6ae58edcba70ad4aa507ce9e383c68e186cc9a302c48a10ddab6689d2a648cd8b2608d0a2405ca96281c286084c892200c08200),
  ([([(0xa0a00505a0a00505a0a00505a0a00505, 0), (0xa0a00000a0a00000a0a00000a0a0000, 3), (0xa0a00000a0a00000a0a00000a0a0, 12), (0xa0a00000a0a00000a0a00000a0a, 15)], [(0x50500000505000005050000050500000, 15), (0x5050000050500000505000005050000, 12), (0x5050000050500000505000005050, 3)])], rowSelectPacked 0xffefef9dfaf6e9efcfaf1cf8f2e1fdebe78ddab668edcba70cd8b260bf6eed99f2e6c9af4ead18f0e2c1bd6ae589d2a648ad4aa508d0a2407eedeb95ead6a96ecdab14e8d2a17ce9e385ca96286cc9a304c892203e6ce991e2c6892e4ca910e0c2813c68e181c286082c48a100c08200, rowSelectPacked 0xffbfeedfdbbe6cef9fae5ed9ba64f7afce9f5abc68e78f8e1e58b860bf3eecdbd3ae4caf1eac5ad1aa44b72ecc9b52ac48a70e8c1a50a8407ebdead7cb9e2c6e9daa56c99a2476adca974a9c28668d8a164898203e3ce8d3c38e0c2e1ca852c18a04362cc893428c08260c8812408800),
  ([([(0xa0a005050000000000000000a0a00505, 0), (0xa0a000000000000000000000a0a0000, 3), (0xa0a000000000000000000000a0a0, 12), (0xa0a000000000000000000000a0a, 15), (0x5050000000000000, 17), (0x505000000000000, 20), (0x505000000000, 29), (0xa0a0050500000000, 32), (0xa0a000000000000, 35), (0xa0a000000000, 44), (0xa0a00000000, 47)], [(0x505000000000000000000000, 47), (0x50500000000000000000000, 44), (0x50500000000000000000, 35), (0xa0a005050000000000000000, 32), (0xa0a00000000000000000000, 29), (0xa0a00000000000000000, 20), (0xa0a0000000000000000, 17), (0x50500000000000000000000050500000, 15), (0x5050000000000000000000005050000, 12), (0x5050000000000000000000005050, 3)])], rowSelectPacked 0xffefef9dfaf6e9efcfaf1cf8f2e1fdebe78ddab668edcba70cd8b2607eedeb95ead6a96ecdab14e8d2a17ce9e385ca96286cc9a304c89220bf6eed99f2e6c9af4ead18f0e2c1bd6ae589d2a648ad4aa508d0a2403e6ce991e2c6892e4ca910e0c2813c68e181c286082c48a100c08200, rowSelectPacked 0xffbfeedfdbbe6cef9fae5ed9ba64f7afce9f5abc68e78f8e1e58b8607ebdead7cb9e2c6e9daa56c99a2476adca974a9c28668d8a16489820bf3eecdbd3ae4caf1eac5ad1aa44b72ecc9b52ac48a70e8c1a50a8403e3ce8d3c38e0c2e1ca852c18a04362cc893428c08260c8812408800),
  ([([(0xa0a0000000000505a0a0000000000505, 0), (0xa0a0000000000000a0a000000000000, 3), (0xa0a0000000000000a0a0, 12), (0x505000000000000050500000, 13), (0xa0a0000000000000a0a, 15), (0x50500000000000005050000, 16), (0xa0a0000000000000a0a00000, 28), (0xa0a0000000000000a0a0000, 31)], [(0x5050000000000000505000000000, 31), (0x505000000000000050500000000, 28), (0xa0a0000000000000a0a000000000, 16), (0x50500000000000005050000000000000, 15), (0xa0a0000000000000a0a00000000, 13), (0x5050000000000000505000000000000, 12), (0x50500000000000005050, 3)])], rowSelectPacked 0xffefef9bf6eed9efcfaf1af4ead1fdebe78bd6ae58edcba70ad4aa50dfaf6e99f2e6c9cf8f2e18f0e2c1ddab6689d2a648cd8b2608d0a2407eedeb93e6ce996ecdab12e4ca917ce9e383c68e186cc9a302c48a105ead6a91e2c6894e8d2a10e0c2815ca96281c286084c892200c08200, rowSelectPacked 0xffbfeedfdbbe6cef9fae5ed9ba64bf3eecdbd3ae4caf1eac5ad1aa44f7afce9f5abc68e78f8e1e58b860b72ecc9b52ac48a70e8c1a50a8407ebdead7cb9e2c6e9daa56c99a243e3ce8d3c38e0c2e1ca852c18a0476adca974a9c28668d8a16489820362cc893428c08260c8812408800),
  ([([(0xa0a00000000000000000000000000505, 0), (0xa0a0000000000000000000000000000, 3), (0xa0a0, 12), (0x50500000, 13), (0xa0a, 15), (0x5050000, 16), (0xa0a00000, 28), (0x505000000000, 29), (0xa0a0000, 31), (0x50500000000, 32), (0xa0a000000000, 44), (0x5050000000000000, 45), (0xa0a00000000, 47), (0x505000000000000, 48), (0xa0a0000000000000, 60), (0xa0a000000000000, 63)], [(0x50500000000000000000, 63), (0x5050000000000000000, 60), (0xa0a00000000000000000, 48), (0x505000000000000000000000, 47), (0xa0a0000000000000000, 45), (0x50500000000000000000000, 44), (0xa0a000000000000000000000, 32), (0x5050000000000000000000000000, 31), (0xa0a00000000000000000000, 29), (0x505000000000000000000000000, 28), (0xa0a0000000000000000000000000, 16), (0x50500000000000000000000000000000, 15), (0xa0a000000000000000000000000, 13), (0x5050000000000000000000000000000, 12), (0x5050, 3)])], rowSelectPacked 0xffefef97eedeb9efcfaf16ecdab1fdebe787ce9e38edcba706cc9a30dfaf6e95ead6a9cf8f2e14e8d2a1ddab6685ca9628cd8b2604c89220bf6eed93e6ce99af4ead12e4ca91bd6ae583c68e18ad4aa502c48a109f2e6c91e2c6898f0e2c10e0c2819d2a6481c286088d0a2400c08200, rowSelectPacked 0xffbfeedfdbbe6cef9fae5ed9ba64bf3eecdbd3ae4caf1eac5ad1aa447ebdead7cb9e2c6e9daa56c99a243e3ce8d3c38e0c2e1ca852c18a04f7afce9f5abc68e78f8e1e58b860b72ecc9b52ac48a70e8c1a50a84076adca974a9c28668d8a16489820362cc893428c08260c8812408800),
  ([([(0xa0a00000000000000000000000000505, 0), (0xa0a0000000000000000000000000000, 3), (0xa0a0, 12), (0x505000000000000000000000, 13), (0xa0a, 15), (0x50500000000000000000000, 16), (0x5050000000000000, 17), (0x505000000000000, 20), (0xa0a000000000000000000000, 28), (0xa0a00000000000000000000, 31), (0xa0a0000000000000, 32), (0xa0a000000000000, 35), (0x50500000, 45), (0x5050000, 48), (0xa0a00000, 60), (0xa0a0000, 63)], [(0x5050000000000000000000000000, 63), (0x505000000000000000000000000, 60), (0xa0a0000000000000000000000000, 48), (0xa0a000000000000000000000000, 45), (0x50500000000000000000, 35), (0x5050000000000000000, 32), (0x505000000000, 31), (0x50500000000, 28), (0xa0a00000000000000000, 20), (0xa0a0000000000000000, 17), (0xa0a000000000, 16), (0x50500000000000000000000000000000, 15), (0xa0a00000000, 13), (0x5050000000000000000000000000000, 12), (0x5050, 3)])], rowSelectPacked 0xffefef9bf6eed9efcfaf1af4ead1fdebe78bd6ae58edcba70ad4aa507eedeb93e6ce996ecdab12e4ca917ce9e383c68e186cc9a302c48a10dfaf6e99f2e6c9cf8f2e18f0e2c1ddab6689d2a648cd8b2608d0a2405ead6a91e2c6894e8d2a10e0c2815ca96281c286084c892200c08200, rowSelectPacked 0xffbfeedfdbbe6cef9fae5ed9ba647ebdead7cb9e2c6e9daa56c99a24f7afce9f5abc68e78f8e1e58b86076adca974a9c28668d8a16489820bf3eecdbd3ae4caf1eac5ad1aa443e3ce8d3c38e0c2e1ca852c18a04b72ecc9b52ac48a70e8c1a50a840362cc893428c08260c8812408800),
  ([([(0xa0a00000a0a000000000050500000505, 0), (0xa0a00000a0a00000000000000000000, 3), (0xa0a00000a0a0, 12), (0xa0a00000a0a, 15), (0x5050000050500000, 45), (0x505000005050000, 48), (0xa0a00000a0a00000, 60), (0xa0a00000a0a0000, 63)], [(0x5050000050500000000000000000, 63), (0x505000005050000000000000000, 60), (0xa0a00000a0a00000000000000000, 48), (0xa0a00000a0a0000000000000000, 45), (0x50500000505000000000000000000000, 15), (0x5050000050500000000000000000000, 12), (0x505000005050, 3)])], rowSelectPacked 0xffefef97eedeb9efcfaf16ecdab1fdebe787ce9e38edcba706cc9a30bf6eed93e6ce99af4ead12e4ca91bd6ae583c68e18ad4aa502c48a10dfaf6e95ead6a9cf8f2e14e8d2a1ddab6685ca9628cd8b2604c892209f2e6c91e2c6898f0e2c10e0c2819d2a6481c286088d0a2400c08200, rowSelectPacked 0xffbfeedfdbbe6cef9fae5ed9ba647ebdead7cb9e2c6e9daa56c99a24bf3eecdbd3ae4caf1eac5ad1aa443e3ce8d3c38e0c2e1ca852c18a04f7afce9f5abc68e78f8e1e58b86076adca974a9c28668d8a16489820b72ecc9b52ac48a70e8c1a50a840362cc893428c08260c8812408800),
  ([([(0xa0a050500a0a0505a0a050500a0a0505, 0), (0x505000000000000050500000, 13), (0xa0a000000a0a0000a0a000000a0a, 15), (0xa0a0505000000000a0a05050, 28), (0xa0a0000000000000a0a0, 43)], [(0x5050000000000000505000000000000, 43), (0xa0a0505000000000a0a050500000000, 28), (0x50500000050500005050000005050000, 15), (0xa0a0000000000000a0a00000000, 13)])], rowSelectPacked 0xffbfeedbf3eecdef9fae5af1eac5fdbbe6cbd3ae4ced9ba64ad1aa44f7afce9b72ecc9e78f8e1a70e8c1f5abc68b52ac48e58b860a50a8407ebdead3e3ce8d6e9daa52e1ca857cb9e2c3c38e0c6c99a242c18a0476adca9362cc89668d8a1260c88174a9c283428c0864898202408800, rowSelectPacked 0xffbfeedbf3eecdef9fae5af1eac5fdbbe6cbd3ae4ced9ba64ad1aa44f7afce9b72ecc9e78f8e1a70e8c1f5abc68b52ac48e58b860a50a8407ebdead3e3ce8d6e9daa52e1ca857cb9e2c3c38e0c6c99a242c18a0476adca9362cc89668d8a1260c88174a9c283428c0864898202408800),
  ([([(0xa0a0505000000000000000000a0a0505, 0), (0x50500000, 13), (0xa0a0000000000000000000000a0a, 15), (0x505000000000000, 17), (0xa0a05050, 28), (0xa0a050500000000, 32), (0xa0a0, 43), (0x5050000000000000, 45), (0xa0a00000000, 47), (0xa0a0505000000000, 60), (0xa0a000000000, 75)], [(0x50500000000000000000000, 75), (0xa0a05050000000000000000, 60), (0x505000000000000000000000, 47), (0xa0a0000000000000000, 45), (0x5050000000000000000000000000000, 43), (0xa0a050500000000000000000, 32), (0xa0a0505000000000000000000000000, 28), (0xa0a00000000000000000, 17), (0x50500000000000000000000005050000, 15), (0xa0a000000000000000000000000, 13)])], rowSelectPacked 0xffbfeed7ebdeadef9fae56e9daa5fdbbe6c7cb9e2ced9ba646c99a24f7afce976adca9e78f8e1668d8a1f5abc6874a9c28e58b8606489820bf3eecd3e3ce8daf1eac52e1ca85bd3ae4c3c38e0cad1aa442c18a04b72ecc9362cc89a70e8c1260c881b52ac483428c08a50a8402408800, rowSelectPacked 0xffbfeedbf3eecdef9fae5af1eac5fdbbe6cbd3ae4ced9ba64ad1aa447ebdead3e3ce8d6e9daa52e1ca857cb9e2c3c38e0c6c99a242c18a04f7afce9b72ecc9e78f8e1a70e8c1f5abc68b52ac48e58b860a50a84076adca9362cc89668d8a1260c88174a9c283428c0864898202408800),
  ([([(0xa0a00000000000000000000000000505, 0), (0xa0a00000000000000000000, 3), (0xa0a000000000, 12), (0xa0a, 15), (0x505000000000000000000000, 16), (0x505000000000000, 17), (0x5050, 28), (0xa0a000000000000000000000, 31), (0xa0a000000000000, 32), (0xa0a0, 43), (0x5050000000000000, 45), (0x5050000, 48), (0xa0a0000000000000, 60), (0xa0a0000, 63), (0x50500000, 76), (0xa0a00000, 91)], [(0x505000000000000000000000000, 91), (0xa0a000000000000000000000000, 76), (0x5050000000000000000000000000, 63), (0x5050000000000000000, 60), (0xa0a0000000000000000000000000, 48), (0xa0a0000000000000000, 45), (0x5050000000000000000000000000000, 43), (0x50500000000000000000, 32), (0x50500000000, 31), (0xa0a0000000000000000000000000000, 28), (0xa0a00000000000000000, 17), (0xa0a00000000, 16), (0x50500000000000000000000000000000, 15), (0x50500000000000000000000, 12), (0x505000000000, 3)])], rowSelectPacked 0xff7fedd7e7de9def5fad56e5da95fd7be5c7c79e1ced5ba546c59a14f76fcd9766dc99e74f8d1664d891f56bc587469c18e54b8506449810df3f6cd5e3d68dcf1f2c54e1d285dd3b64c5c3960ccd1b2444c19204d72f4c9562d489c70f0c1460d081d52b4485429408c50b0404409000, rowSelectPacked 0xffbfeedbf3eecdef9fae5af1eac57ebdead3e3ce8d6e9daa52e1ca85fdbbe6cbd3ae4ced9ba64ad1aa447cb9e2c3c38e0c6c99a242c18a04f7afce9b72ecc9e78f8e1a70e8c176adca9362cc89668d8a1260c881f5abc68b52ac48e58b860a50a84074a9c283428c0864898202408800),
  ([([(0xa0a0505000000000000000000a0a0505, 0), (0x505000000000000000000000, 13), (0xa0a0000000000000000000000a0a, 15), (0x5050000000000000, 17), (0xa0a050500000000000000000, 28), (0xa0a0505000000000, 32), (0xa0a00000000000000000, 43), (0x50500000, 45), (0xa0a000000000, 47), (0xa0a05050, 60), (0xa0a0, 75)], [(0x5050000000000000000000000000000, 75), (0xa0a0505000000000000000000000000, 60), (0x50500000000000000000000, 47), (0xa0a000000000000000000000000, 45), (0x505000000000000, 43), (0xa0a05050000000000000000, 32), (0xa0a050500000000, 28), (0xa0a0000000000000000, 17), (0x50500000000000000000000005050000, 15), (0xa0a00000000, 13)])], rowSelectPacked 0xffbfeedbf3eecdef9fae5af1eac5fdbbe6cbd3ae4ced9ba64ad1aa447ebdead3e3ce8d6e9daa52e1ca857cb9e2c3c38e0c6c99a242c18a04f7afce9b72ecc9e78f8e1a70e8c1f5abc68b52ac48e58b860a50a84076adca9362cc89668d8a1260c88174a9c283428c0864898202408800, rowSelectPacked 0xffbfeed7ebdeadef9fae56e9daa5fdbbe6c7cb9e2ced9ba646c99a24f7afce976adca9e78f8e1668d8a1f5abc6874a9c28e58b8606489820bf3eecd3e3ce8daf1eac52e1ca85bd3ae4c3c38e0cad1aa442c18a04b72ecc9362cc89a70e8c1260c881b52ac483428c08a50a8402408800),
  ([([(0xa0a05050a0a050500a0a05050a0a0505, 0), (0xa0a00000a0a000000a0a00000a0a, 15), (0x5050000050500000, 45), (0xa0a05050a0a05050, 60), (0xa0a00000a0a0, 75)], [(0x5050000050500000000000000000000, 75), (0xa0a05050a0a05050000000000000000, 60), (0xa0a00000a0a0000000000000000, 45), (0x50500000505000000505000005050000, 15)])], rowSelectPacked 0xffbfeed7ebdeadef9fae56e9daa5fdbbe6c7cb9e2ced9ba646c99a24bf3eecd3e3ce8daf1eac52e1ca85bd3ae4c3c38e0cad1aa442c18a04f7afce976adca9e78f8e1668d8a1f5abc6874a9c28e58b8606489820b72ecc9362cc89a70e8c1260c881b52ac483428c08a50a8402408800, rowSelectPacked 0xffbfeed7ebdeadef9fae56e9daa5fdbbe6c7cb9e2ced9ba646c99a24bf3eecd3e3ce8daf1eac52e1ca85bd3ae4c3c38e0cad1aa442c18a04f7afce976adca9e78f8e1668d8a1f5abc6874a9c28e58b8606489820b72ecc9362cc89a70e8c1260c881b52ac483428c08a50a8402408800),
  ([([(0xa0a00000000000000000000000000505, 0), (0xa0a0000000000000000000000000000, 3), (0xa0a000000000, 12), (0xa0a00000000, 15), (0xa0a000000000000000000000, 16), (0xa0a00000000000000000000, 19), (0xa0a0, 28), (0x5050000000000000, 29), (0xa0a, 31), (0x505000000000000, 32), (0x50500000, 45), (0x5050000, 48), (0xa0a0000000000000, 60), (0xa0a000000000000, 63), (0xa0a00000, 76), (0xa0a0000, 79)], [(0x5050000000000000000000000000, 79), (0x505000000000000000000000000, 76), (0x50500000000000000000, 63), (0x5050000000000000000, 60), (0xa0a0000000000000000000000000, 48), (0xa0a000000000000000000000000, 45), (0xa0a00000000000000000, 32), (0x50500000000000000000000000000000, 31), (0xa0a0000000000000000, 29), (0x5050000000000000000000000000000, 28), (0x505000000000, 19), (0x50500000000, 16), (0x505000000000000000000000, 15), (0x50500000000000000000000, 12), (0x5050, 3)])], rowSelectPacked 0xffefef97eedeb9efcfaf16ecdab1bf6eed93e6ce99af4ead12e4ca91fdebe787ce9e38edcba706cc9a30bd6ae583c68e18ad4aa502c48a10dfaf6e95ead6a9cf8f2e14e8d2a19f2e6c91e2c6898f0e2c10e0c281ddab6685ca9628cd8b2604c892209d2a6481c286088d0a2400c08200, rowSelectPacked 0xff7feddfd7be5cef5fad5ed5ba547e7de9d7c79e1c6e5da956c59a14df3f6cddd3b64ccf1f2c5cd1b2445e3d68d5c3960c4e1d2854c19204f76fcd9f56bc58e74f8d1e54b850766dc997469c18664d8916449810d72f4c9d52b448c70f0c1c50b040562d4895429408460d0814409000),
  ([([(0xaaaaaaaa55555555aaaaaaaa55555555, 0), (0xaaaaaaaa00000000aaaaaaaa, 31)], [(0x55555555000000005555555500000000, 31)])], rowSelectPacked 0xff7feddf76fcd9ef5fad5e74f8d1df3f6cdd72f4c9cf1f2c5c70f0c1fd7be5cf56bc58ed5ba54e54b850dd3b64cd52b448cd1b244c50b0407e7de9d766dc996e5da95664d8915e3d68d562d4894e1d285460d0817c79e1c7469c186c59a1464498105c3960c54294084c192044409000, rowSelectPacked 0xff7feddf76fcd9ef5fad5e74f8d1df3f6cdd72f4c9cf1f2c5c70f0c1fd7be5cf56bc58ed5ba54e54b850dd3b64cd52b448cd1b244c50b0407e7de9d766dc996e5da95664d8915e3d68d562d4894e1d285460d0817c79e1c7469c186c59a1464498105c3960c54294084c192044409000),
  ([([(0xa0a0000000000505a0a0000000000505, 0), (0xa0a0000000000000a0a00000000, 3), (0x50500000000000005050, 12), (0xa0a0000000000000a0a000000000, 15), (0xa0a0000000000000a0a0000, 16), (0xa0a0000000000000a0a00000, 28), (0xa0a0000000000000a0a, 31), (0xa0a0000000000000a0a0, 43)], [(0x5050000000000000505000000000000, 43), (0x50500000000000005050000000000000, 31), (0x505000000000000050500000000, 28), (0x5050000000000000505000000000, 16), (0x50500000000000005050000, 15), (0xa0a0000000000000a0a000000000000, 12), (0x505000000000000050500000, 3)])], rowSelectPacked 0xffbfeedbf3eecdef9fae5af1eac5f7afce9b72ecc9e78f8e1a70e8c1fdbbe6cbd3ae4ced9ba64ad1aa44f5abc68b52ac48e58b860a50a8407ebdead3e3ce8d6e9daa52e1ca8576adca9362cc89668d8a1260c8817cb9e2c3c38e0c6c99a242c18a0474a9c283428c0864898202408800, rowSelectPacked 0xff7fedddf3f6cdef5fad5cf1f2c5fd7be5cdd3b64ced5ba54cd1b244f76fcd9d72f4c9e74f8d1c70f0c1f56bc58d52b448e54b850c50b0407e7de9d5e3d68d6e5da954e1d2857c79e1c5c3960c6c59a144c19204766dc99562d489664d891460d0817469c18542940864498104409000),
  ([([(0xa0a00000000000000000000000000505, 0), (0xa0a00000000, 3), (0x50500000000000000000, 12), (0xa0a0000000000000000000000000, 15), (0xa0a0000, 16), (0x5050000000000000, 17), (0xa0a000000000000000000000, 28), (0xa0a, 31), (0x505000000000, 32), (0xa0a00000000000000000, 43), (0x50500000, 45), (0xa0a0000000000000, 48), (0x5050, 60), (0xa0a000000000, 63), (0xa0a00000, 76), (0xa0a0, 91)], [(0x5050000000000000000000000000000, 91), (0x505000000000000000000000000, 76), (0x50500000000000000000000, 63), (0xa0a0000000000000000000000000000, 60), (0x5050000000000000000, 48), (0xa0a000000000000000000000000, 45), (0x505000000000000, 43), (0xa0a00000000000000000000, 32), (0x50500000000000000000000000000000, 31), (0x50500000000, 28), (0xa0a0000000000000000, 17), (0x5050000000000000000000000000, 16), (0x5050000, 15), (0xa0a000000000000, 12), (0x505000000000000000000000, 3)])], rowSelectPacked 0xffbfeedbf3eecdef9fae5af1eac57ebdead3e3ce8d6e9daa52e1ca85fdbbe6cbd3ae4ced9ba64ad1aa447cb9e2c3c38e0c6c99a242c18a04f7afce9b72ecc9e78f8e1a70e8c176adca9362cc89668d8a1260c881f5abc68b52ac48e58b860a50a84074a9c283428c0864898202408800, rowSelectPacked 0xff7fedd7e7de9def5fad56e5da95fd7be5c7c79e1ced5ba546c59a14f76fcd9766dc99e74f8d1664d891f56bc587469c18e54b8506449810df3f6cd5e3d68dcf1f2c54e1d285dd3b64c5c3960ccd1b2444c19204d72f4c9562d489c70f0c1460d081d52b4485429408c50b0404409000),
  ([([(0xa0a000005050000000000a0a00000505, 0), (0xa0a0000050500000000000000000, 12), (0x5050000000000000, 17), (0xa0a0000, 19), (0x505000000000, 29), (0xa0a000000000000000000a0a, 31), (0xa0a00000000000000000, 43), (0xa0a0000050500000, 48), (0xa0a000005050, 60), (0xa0a00000, 79), (0xa0a0, 91)], [(0x5050000000000000000000000000000, 91), (0x505000000000000000000000000, 79), (0xa0a0000050500000000000000000000, 60), (0xa0a000005050000000000000000, 48), (0x505000000000000, 43), (0x50500000000000000000050500000000, 31), (0xa0a00000000000000000000, 29), (0x5050000000000000000000000000, 19), (0xa0a0000000000000000, 17), (0xa0a000005050000, 12)])], rowSelectPacked 0xff7fedddf3f6cdef5fad5cf1f2c57e7de9d5e3d68d6e5da954e1d285fd7be5cdd3b64ced5ba54cd1b2447c79e1c5c3960c6c59a144c19204f76fcd9d72f4c9e74f8d1c70f0c1766dc99562d489664d891460d081f56bc58d52b448e54b850c50b0407469c18542940864498104409000, rowSelectPacked 0xff7fedd7e7de9def5fad56e5da95f76fcd9766dc99e74f8d1664d891fd7be5c7c79e1ced5ba546c59a14f56bc587469c18e54b8506449810df3f6cd5e3d68dcf1f2c54e1d285d72f4c9562d489c70f0c1460d081dd3b64c5c3960ccd1b2444c19204d52b4485429408c50b0404409000)]
private def c117Moves := dagMoves c117MoveCert

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Autos : DagMovesOK b117.1 b117.2.2.2 128 c117Moves :=
  dagMovesOfCheck (by decide +kernel)

private def c117Check := dagCheckNode b117.1 b117.2.2.2 none (dagKnownCloses b117.2.2.2 cuts117) 95
  c117States c117Moves c117Links c117Sample c117Tags

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Roots :
    dagCheckRoots b117.1 b117.2.2.2 none (dagKnownCloses b117.2.2.2 cuts117) []
      (dagRef 95 c117States c117Moves c117Links 0) stock117 9 = true := by
  decide +kernel

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block0 : treeBlock 0 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block4 : treeBlock 4 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block8 : treeBlock 8 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block12 : treeBlock 12 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block16 : treeBlock 16 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block20 : treeBlock 20 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block24 : treeBlock 24 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block28 : treeBlock 28 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block32 : treeBlock 32 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block36 : treeBlock 36 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block40 : treeBlock 40 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block44 : treeBlock 44 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block48 : treeBlock 48 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block52 : treeBlock 52 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block56 : treeBlock 56 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block60 : treeBlock 60 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block64 : treeBlock 64 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block68 : treeBlock 68 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block72 : treeBlock 72 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block76 : treeBlock 76 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block80 : treeBlock 80 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block84 : treeBlock 84 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block88 : treeBlock 88 4 c117Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c117Block92 : treeBlock 92 3 c117Check = true := by decide +kernel

private theorem c117Checked : treeBlock 0 95 c117Check = true :=
  (@treeBlock_merge 0 48 47 c117Check
    (@treeBlock_merge 0 24 24 c117Check
    (@treeBlock_merge 0 12 12 c117Check
    (@treeBlock_merge 0 4 8 c117Check
    c117Block0
    (@treeBlock_merge 4 4 4 c117Check
    c117Block4
    c117Block8))
    (@treeBlock_merge 12 4 8 c117Check
    c117Block12
    (@treeBlock_merge 16 4 4 c117Check
    c117Block16
    c117Block20)))
    (@treeBlock_merge 24 12 12 c117Check
    (@treeBlock_merge 24 4 8 c117Check
    c117Block24
    (@treeBlock_merge 28 4 4 c117Check
    c117Block28
    c117Block32))
    (@treeBlock_merge 36 4 8 c117Check
    c117Block36
    (@treeBlock_merge 40 4 4 c117Check
    c117Block40
    c117Block44))))
    (@treeBlock_merge 48 24 23 c117Check
    (@treeBlock_merge 48 12 12 c117Check
    (@treeBlock_merge 48 4 8 c117Check
    c117Block48
    (@treeBlock_merge 52 4 4 c117Check
    c117Block52
    c117Block56))
    (@treeBlock_merge 60 4 8 c117Check
    c117Block60
    (@treeBlock_merge 64 4 4 c117Check
    c117Block64
    c117Block68)))
    (@treeBlock_merge 72 12 11 c117Check
    (@treeBlock_merge 72 4 8 c117Check
    c117Block72
    (@treeBlock_merge 76 4 4 c117Check
    c117Block76
    c117Block80))
    (@treeBlock_merge 84 4 7 c117Check
    c117Block84
    (@treeBlock_merge 88 4 3 c117Check
    c117Block88
    c117Block92)))))

private theorem lower117 : Lower b117.1 stock117 b117.2.2.2 10 := by
  exact lowerDag (width := 128) (chart := none)
    (by unfold Masked; decide +kernel) (by unfold Masked; decide +kernel)
    (by unfold properWord; decide +kernel) (by simp) c117Autos
    (by unfold Masked; decide +kernel) (by decide +kernel) (by decide +kernel)
    (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower116) lower113) lower101) lower85) lower53) (by decide +kernel)
    c117Roots c117Checked

private def stock118 : List Word := [0x440044004400440044004400440044, 0x500050005000500050005000500050, 0x550000005500000055000000550000, 0x550055000000000055005500000000, 0x550055005500550000000000000000]
private def b118 : Bound := (0x550055005500550055005500550055, stock118, 8, 0x550055005500540055005400540000)
private def cuts118 : List Bound := [b114, b116, b54, b86, b102]
private theorem lower118 : Lower b118.1 stock118 b118.2.2.2 8 :=
  lowerRelabelMasked (rowSelectPacked 0xfff7df9fdf3d78efd79f1edd3970dfb75e9ddb3568cf971e1cd93160bf76dd9bd72d58af569d1ad529509f365c99d325488f161c18d121407ef5db97cf1d386ed59b16cd19305eb55a95cb15284e951a14c911203e74d993c70d182e549912c509101e345891c305080e141810c10100) lower115
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock121 : List Word := [0x2020202020202020202020202020202, 0x3000300030003000300030003000300, 0x3030000030300000303000003030000, 0x3030303000000000303030300000000, 0x3030303030303030000000000000000]
private def b121 : Bound := (0x3030303030303030303030303030303, stock121, 8, 0x3030303030303020303030202020000)
private def cuts121 : List Bound := [b113, b57, b89, b105, b120]
private theorem lower121 : Lower b121.1 stock121 b121.2.2.2 8 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbbf6dfbb3e6fbf3af4dbb32e4bf7abd69f3a3c6bb72ad49b322c47ef9bb65eb93a67af1ab45ab12a43e78b961e383863a70a941a30284f7eb9f2d7ab1e2f3e38f0d3a30e0b76a9d2972a1c2b3628d093220c076e99b256a91a272e18b052a10a03668992162818232608901220080) lower55
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock122 : List Word := [0x4040404040404040404040404040404, 0x5000500050005000500050005000500, 0x5050000050500000505000005050000, 0x5050505000000000505050500000000, 0x5050505050505050000000000000000]
private def b122 : Bound := (0x5050505050505050505050505050505, stock122, 8, 0x5050505050505040505050404040400)
private def cuts122 : List Bound := [b106, b114, b58, b90, b120]
private theorem lower122 : Lower b122.1 stock122 b122.2.2.2 8 :=
  lowerRelabelMasked (rowSelectPacked 0xffdf7e7fddb766f7cf5e3f5cb562fbd76e5f9d3664f3c74e1f1c3460bf5e7c7bd5a746b74e5c3b54a542bb566c5b952644b3464c1b1424407edd7a77cd972676cd5a374c95227ad56a578d162472c54a170c14203e5c7873c58706364c58334485023a54685385060432444813040400) lower115
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock124 : List Word := [0x10101010101010101010101010101010, 0x11001100110011001100110011001100, 0x11110000111100001111000011110000, 0x11111111000000001111111100000000, 0x11111111111111110000000000000000]
private def b124 : Bound := (0x11111111111111111111111111111111, stock124, 8, 0x11111111111111101111111010100000)
private def cuts124 : List Bound := [b116, b60, b92, b108, b120]
private theorem lower124 : Lower b124.1 stock124 b124.2.2.2 8 :=
  lowerRelabelMasked (rowSelectPacked 0xffefbf3dfaf3e3fdebb72ddab362bf6ebd39f2e3c3bd6ab529d2a3427eedbb35ead3a37ce9b325ca93223e6cb931e2c3833c68b121c28302fbe7af1dba72e1f9e3a70d9a3260bb66ad19b262c1b962a5099222407ae5ab15aa52a178e1a3058a12203a64a911a242813860a101820200) lower55
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock63 : List Word := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
private def b63 : Bound := (0xffffffffffffffff, stock63, 10, 0xfffffffefefeeca0)
private def cuts63 : List Bound := [b47, b55, b61, b31, b59, b62]
private def c63Index : Nat := 0xfbf8f8f1f0e9b7b0b0b0a9a8a8a1a09967595858513b0e01
private def c63Edges : Nat := 0x254961e32b14628a00a8800e2b2514e4a09193cc326a264190c4038078d9281404e206807c940e4a79894e2d25a4a4b273270e04e0d2581bd1057a20864308c40b3d130321c2620400863007c10040003f
private def c63Links : DagLinks :=
  dagLookupLinks c63Index c63Edges 8 3 13 5 1 4
private def c63Data : Forest := fun i => decodeNode 5 18 0x1e881928c4055492844c9f1320c408619281d29e79283529c74969c09ca4961c68080271c03e17a208c8627a20cc4020040407e0 i
private def c63Sample : DagSample := (0x100c03030060c01230030c00630100a03028060a01228030a0062810090302406090122403090062410050301406050121403050061410088302206088122203088062210048301206048121203048061210028300a06028120a03028060a100843021060841221030840621100443011060441211030440611100143005060141205030140605, 60)
private def c63Tags := dagTraceTags b63.1 60
  (dagTagBases stock63 0xffffc0fc003f000fc003f03f000fc003f000000fc0000000fff00000003f000000ffffc000000000000003ffff 0x82082082082082041041041041041071c71c71c71c71c28a28a28a28a28a0c30c30c30c30c3145145145145145 60) 9 c63Data
private def c63States := dagTrace b63.1 stock63 9 c63Data
private def c63MoveCert : List (DagMoveRecord 128) := [
  ([([(0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0x50505050505050505050505050505050, 3)])], rowSelectPacked 0xffefef9fdebe78efcfaf1edcba70dfaf6e9ddab668cf8f2e1cd8b260bf6eed9bd6ae58af4ead1ad4aa509f2e6c99d2a6488f0e2c18d0a2407eedeb97ce9e386ecdab16cc9a305ead6a95ca96284e8d2a14c892203e6ce993c68e182e4ca912c48a101e2c6891c286080e0c2810c08200, rowSelectPacked 0xffefef9fdebe78efcfaf1edcba70dfaf6e9ddab668cf8f2e1cd8b260bf6eed9bd6ae58af4ead1ad4aa509f2e6c99d2a6488f0e2c18d0a2407eedeb97ce9e386ecdab16cc9a305ead6a95ca96284e8d2a14c892203e6ce993c68e182e4ca912c48a101e2c6891c286080e0c2810c08200)]
private def c63Moves := dagMoves c63MoveCert

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c63Autos : DagMovesOK b63.1 b63.2.2.2 128 c63Moves :=
  dagMovesOfCheck (by decide +kernel)

private def c63Check := dagCheckNode b63.1 b63.2.2.2 none (dagKnownCloses b63.2.2.2 cuts63) 23
  c63States c63Moves c63Links c63Sample c63Tags

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c63Roots :
    dagCheckRoots b63.1 b63.2.2.2 none (dagKnownCloses b63.2.2.2 cuts63) []
      (dagRef 23 c63States c63Moves c63Links 0) stock63 9 = true := by
  decide +kernel

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c63Block0 : treeBlock 0 6 c63Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c63Block6 : treeBlock 6 6 c63Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c63Block12 : treeBlock 12 6 c63Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c63Block18 : treeBlock 18 5 c63Check = true := by decide +kernel

private theorem c63Checked : treeBlock 0 23 c63Check = true :=
  (@treeBlock_merge 0 12 11 c63Check
    (@treeBlock_merge 0 6 6 c63Check
    c63Block0
    c63Block6)
    (@treeBlock_merge 12 6 5 c63Check
    c63Block12
    c63Block18))

private theorem lower63 : Lower b63.1 stock63 b63.2.2.2 10 := by
  exact lowerDag (width := 128) (chart := none)
    (by unfold Masked; decide +kernel) (by unfold Masked; decide +kernel)
    (by unfold properWord; decide +kernel) (by simp) c63Autos
    (by unfold Masked; decide +kernel) (by decide +kernel) (by decide +kernel)
    (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower62) lower59) lower31) lower61) lower55) lower47) (by decide +kernel)
    c63Roots c63Checked

private def stock95 : List Word := [0xaaaaaaaa00000000aaaaaaaa, 0xcccccccc00000000cccccccc, 0xf0f0f0f000000000f0f0f0f0, 0xff00ff0000000000ff00ff00, 0xffff000000000000ffff0000, 0xffffffff0000000000000000]
private def b95 : Bound := (0xffffffff00000000ffffffff, stock95, 10, 0xfffffffe00000000fefeeca0)
private def cuts95 : List Bound := [b79, b87, b93, b31, b91, b94]
private theorem lower95 : Lower b95.1 stock95 b95.2.2.2 10 :=
  lowerRelabelMasked (rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c03e78e9c3668c982e58a9426488901e3868c16284880e182840608080) lower63
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock111 : List Word := [0xaaaa0000aaaa0000aaaa0000aaaa, 0xcccc0000cccc0000cccc0000cccc, 0xf0f00000f0f00000f0f00000f0f0, 0xff000000ff000000ff000000ff00, 0xffff000000000000ffff00000000, 0xffff0000ffff0000000000000000]
private def b111 : Bound := (0xffff0000ffff0000ffff0000ffff, stock111, 11, 0xffff0000fffe0000fffe0000eca0)
private def cuts111 : List Bound := [b47, b79, b103, b107, b109, b110]
private def c111Index : Nat := 0xf523f330f320f2c3ef9aef80ef80ef23ef01ef00eee1eec1ec92e91ce7cae5efe48be480e480e480e423e420e26ee260e241e1a5e1a0e1a0e1a0e1a0e105e100e100e0c2e025e020e001dd94dd61dd60dd03dca3dc62daaedaa0daa0da43da40d9a5d9a0d943d658d640d602d5e1d5e0d5a2d581d542d502d1bbd162d0a6d0a0d062d003cfe1cf83cdedcde0cde0cda2cd43cd40cce3ccc1cc82cc80cc42caebc8f0c57cc560c560c560c522c501c4e1c4a2c4a0c4a0c4a0c424c28dc261c222c166c160c122c101bdf9bdc1bdc0bda1bd24bd20bd20bce2bce0bce0bca2bab0ba05b718b700b700b700b6c2b6c0b6a1b662b660b660b622b620b601b42fb420b3e2b3c1b3c0b3c0b3c0b3c0b3c0b3c0b05cb040b002b000afc2afc0af82af80af80ae4aae40ae21ab19a7daa7c0a7c0a782a780a6c6a5c8a5c0a582a580a580a561a560a560a487a480a442a440a3c4a05ca0409f299f209f209ee29e839e809e619d0b9d009d009cc29c639c609c039c009c009ba39ae69ae098d198a198a09843982196ac96a09662966096609660960396009600958492d692a1924392409240922191e2912690c390a190a090628fe48fe08fe08fe08fe08fe08fe08f838f808f808f428f028ea38c348c208be28be08be08be08b838b808b808b428b02889488808880888088428840884088218820866e864186028584858085428521850184a384a0836a8360832282e2826482608222820181e181c1818280e580e080e080e080c1802580207fc37fc07fa17f437e867d4a7d407d407d027d007d007d007cc27cc07cc0799a7942790278847880786178417802780077e1751772187200720071c271c07106700870006fc26fc06fc06fa16fa06fa06ec76e826e426de36d646d606ce4693e692067cb67a166c766c066c066c06663654964a563c763c063a1636263606360636062c562a15fb85f625f225f205e855bd65bc05bc05b825b235b205b01596d5960596059605922592059015827582057c357c057c05763566856225601558454a754a0546253e451935180518051805180514251405102510051004f2f4ee24e264c8d4c804c614be44be04be04be04b834aa74aa04aa04aa0494b494048e348e048e04883461445e145c145c0456345604522436e436043224320432042e242e04264426042604203420042004200420041843e983e803e803e803da73da03d813d803d423d023c843c803c613c603c223c013a8c3a2339663960392238a438813823378536693660362235c335c035633560356033ec33c133a13305330032e13264322231663160316031413140312130a430a03081308030422f672f602f412f402ee32e642e602e222e012de12de02dc12d442d402d402d402ca52bc72bc02ba12ba02ba02b622ac52a822a802a802a422967265924cc24c024a123e623e023e0238323612360234123022227222022202201220021c2214421402102210020e120a220a0208120611fe41fe01f641f601f601f221e091de11da21d811d611d031d001cc21cc01cc01c821ace1ac01aa11a8118ce159a125a124010ad10430f0a0f000f000ee10ec10ec00ea10ea00e810d2b0d200d200cc30b8a0b800b800b800b610b410b400b400b2109ac09a009a009a009a009a00981082b082008200820082008200820082006ac06a006a00643064006400640064005e304aa02cf00350001
private def c111Edges : Nat := 0x9380b0319013023202034bcc5978c589ad18b10625e4accc6294d88c528292f1965631326a46264109786b23188d342311a0b4cc03689980549330078266009126c336074065409b0c79e30626b460c4160cd87131825362304a0d26893780cd258b181935230320a39c63784d0c5681998806301a6846034124d066e0e70cac13418f8066314699006ed3180da264015c4c602a499003e931807826400984c601219840981308100260014049c0100700038092004025faae04bd25024cd2b252da535e2b4a0b4569350734cb212e995825c326cc5864188b0c6a0998d6425b1a6ac5634148ac66a49180a81bf00f024601209964a21314941a5a4a7b48294d78a9282d1524d583249644b464f8904c9b315190622a31ad24462b80c8c4092d0d3d2411a6ac5434148a866a8df0cae12218fa064314096809e120813462a020845403524880560df007c122009806400860c5e89490b10e03161c237a943848526e818a4b0921321837a6370484c5601898802587a23cacc4360c187132b250e92049bc06092c5958c868de18de120315a06062019586864900cdc1bc195824031f00c062811d4940901626b044c3806d129a104250602f496020264d4088c4045b0cd816c195016c31e095408012a00a025300804a555c0901e884fa25649f04a084286590944cad30f1934210320840e63507d06b20f80d048b501502d601e02d402412319202454aa047e04c18fc08012780a024e0081492036093005412580a424a014049201e80b80501230040245928148694d090c69a45a00a80b4009048664809364a21244940a424a791f694d6085258123993c1b1326848864a1818c8210318d691e315c058620090869e07d8d35198195c23c31f408462845980a816a00f016601208fc09811fbd3022f62603ce04c86c0c98102990016900e21f434c02c8020120496822e7ad13dec4d083d29a10225041ef32683cc35a22c466c0b40ca80b118f047c05a28f006c11e80a823c00f13fa94d0884c9a0fe8d342214a7523a936a46cc6d08e8ca611b18e83fa64e465cc6d08e98a823a928045af4e27ed89ec1030e021f4a78406941a46926f015a4b01fb327a3286378468c5681018801e51a71160336059c6540580c78239027847004e28d406e51a00d8237015846c02a08d403e11a00781e41a60464010078c6980f10d3022f02603c234007800800b200701df020015001008c64a2118494022e61c845ac3828ad29e4fba5049ee49b91ea935607d258116193e206326842c6410838c6e0d598d6919315c05462008ac69e0fb8d041ee19b81ea335464c65708c8c7d01f18a03bc040229c0540b180780a7009043a94c876c65010e3160a294a0041a64c8768c681148d0015b00e0436640056802010d253022631a02b2010086589810c2502ca318f114601e089de8810bb130a254a11448941288d28165118a82251a10448341088c6812510c748a201502b001c0288024110816022002a4c1804c17640800ab8070a1d49a043a33405580380aa804021b31402a8010b28463c4508078a1a49b1432935286126965018a821a19b043233508606692500c748a001502a601c028002530e30f821c61e842ec3cb3c928247924d420b31b4ac0634b27cc552790d040f219ac93e31d982c0840b0010089f015029a01c027c02530fd5726147ad0428f5906c5eb13143d582287aa8444f549879e9a3033d3021f7a2043cc5a88198b010b3132cf14ac91e29410828c852af99021d531a593c62a93c46b20788d0649e18ecc1405a057c0b02ea813089e015029801c02780241098100212008041864c86c005010599301dd026041ac540831898105a5305d7026042925a08464a01083d6820f7a2041cc5aa45929a4f6250420a32d422c34d07b06820ee016889d015013a012052c6510ec993014a00e43b0640a270c5504e0c7489b015029201c026c0240a40ca0205014028e32808224a1103bd3e2067a74408f45880de88103b13c2066270408c39080d8704fb253e9eb4a193d693760792590ea993a89631503ec34f87ac6860f58cdd192195c12c31d40786280ea8138896015028401c02580240fd31601f96260400f4407e1898affa5041ff32083fa05807f00a8afca4d41f931aabf4c3e07e987a0fc30f118f4a0b1e493593c8c822c798d41ea19b29203345504655a530c795ea021012004022980540a0807806c008411e65881ac638047816014000e00d601057eeab8afa3d681f47ac81f6f585805eac100bd541fe7aa03f6f4407dd8988c725655f64a6b1e294193c4cb22c719041f631a83d23425238680a9f8cab4a518f2bd205a02380b045280a813f00f00ce01007cc0800f900410fa00e03d434c075009904b8c7013e00e03d494c07d24b40f8c9401f07ad03def4407b98b48c6a5341ed4a0c22c64d07b0c820f598d41e91ad421e31e074c0b445200a813d00f03c4c4c079c0980f0b1001e47a283c6f4417898722f0b0e01e249683c292c277cc866ea18dc89031a93a862b3240c52c0e18801e01a183b0341177466e0b00cd41dd1958ac0329a46063f0148c501df0218ba8037024006a0ea00ac490014a30601f846002680e00201dd4a60bae34c276cc680ed80d289a18f413401107698920ecb1041d8620111e64d075c69c0a28d301d61a0513231e023c09b04c80441d44a60bcd25117964a00f330e41e561c03bc940374cc9e44719349d331b991c635606cc402ee0d3c15f1a68baa341077066e2af8cd41d5194d22e31f80a06282e9813c08e02683a6037123806a8c1007e117009a036008095a4a01283d3c2417a70476f4508cde8811531389f54a793d094323b5282c0d24b0215327841264306a4c8210118d690e315c04e62007d469e0f40d0c0ed1a0a30232b843863e80d0c501d202710cc02a04e003c03300481d001a039e03087086992b30d0216619a038404c15980800b300d09cc49a43826589594c990b299001cc194038205815940980b281009ca4a00394328071cc684e2a4d89c649a938893407212580e30ca81c519483883282708c500e100701c1324038034c95906810b20cd01ceaae1330c59364d89a4c9b1041cd4ad037695906c52b00e5a5581c94aa838695416e129a2d5a5301b84a08356940238126c0d124b21bf32d42d4658958cc990b199001981ac8b2634d064c6820700ca41bf02d02d4058158c0980b181001bd9283032f4416d189c46fb1081a161c4ad894e037cc6a80c988056c1a7437402806e80200dba5325623260ac404c06dd8980ddc9681b99280370f5a25d589a0db256897149b035092c9584cb40ba8d341711948ac205a80b805001700401b292811b694d036c69a0d381021b0014036001006b809c4d680d81ad00f1b1e941236526b2b0190058f1a081b233515800800da49401b37a78362f4e06bde8a0d63d101ab6271b1c94f26a928646c25058184964abe64e163869e0d50d0c0d81a082fe32b40606282af81381a7020034e9408578c800af01000d319a0b50c5a06a189c4b7b10a55d4ad42ba94e05bcc6a2ae8d6815d1a70b4c05a069809c4d281081a500f033e058068c0a80cfbd389864a0830c3411618c9c0c3190817a31b033863116864a00d13d3c1a17a21b08c4f2611886c0bb0e255c4a742b89421610c9e0c2190c17731ba02e620157069c0ae0d085a00278b3c04e06800860cf010899d01b9336036067403e0cd807908c19401b695806652a88458ca019601a032e03406540600c7a5300d94a04a8264c060c6988440ca0541026310893444f06688420ca01906260320c3c421c68006dbd601917aa031ec4c42186b00c5253818949b031092c06180980c28121087320290e634060d8988431961486320033125a06524a00c9bd6917f6268324c4106392b40c6a5381754a681b094c06312940c5a5241874a411ba936061125929f99681821ad227633605b86548418ca053f02d01acc4c06018902bea53817d4a102f892c85e40500bc804017a02002f003c55fdeb48bfbd391777a23a76c5a64ed89c2bfa56817f4a722e894205d128206a250117e49f02fc93d05ed2780bba4b253b32d427664e54ec6b489d8d3853b02d027604e85cc0500b980400d300e0aeac5a05d589c0ba310817261c0ae295a05c529c0b8250816f4964a7265a84e4c9c2b70d6816e1a70a7205a04e409c0a599025571a6029433421fcc542a48d0014919a00fe01d0520c800b48070147320029e0342598c500a70d0016600e12829410594c940b1190416032010fc62a059069d0a48d3014d1a0028204101f803a0b1313014619a10fa63501f406a0b0250087c326828a32801f009a0a2190015e020028663405592980aa8cd015432002b4328054d2804ac98d887a18f02b203601e80220aa8c7095431502a233221e463c0aa00a807900882a432825406380a8004015031202a2930253c6380a7804255649902ac931054d2600a70cf887818f00f0011956d8940adb1241586244aaec4115258800aba53a1494a6029a94021dc63c03b804487618f00ec01121d468203a810414b7a24294c4385258850a430e614761c029494305252840a424b41474961280643a4f8c6e49f18ad815310028c343051468449d0c7c87318f0288315050c6280a0010e13e01b827c02b04f003e09d004c073008a02a00801f4c8003500700751a600d2010050589803e196014019a00d001c04f866803a0ca007b31a027834004e86800b6494016b7a782d4f4e05a1e8a0b3bd10163627127e94f24f5286c0a24b016132782be64e24e4c5643918a815d31082b8620053069c0a10cd013f027827a04304ec05609c807c07200ea02800816f24a00df3d3c1bc7a21b02c4f2605886c09b0e05b54a78b5294e06d52860d4a50896d49b919c936069125a0cd24b25383274270642160469e0c08d0c17619b82da32b03386528098c50538027027004204d805009a80911281a6295e34042bc66809301304ae020015c03444c8c6809918a11251ac295a34c42b468009281604ad026015a04044c0c8009818d012d31a225c63644b0c6a89598d012e315025862904acc5009518814aa01a215402852b006885600a012719e295603442ac0500940ca012618e295204042a40680928d20124026295004042a006809a557111e62caa32c4d446588208f25645194a6823294104cccb408419640fb32c026265604bccaa094995050532689ea64c0414c8207a99010e031b01c062a0314c408918d690b31ac294e34c429c6808328ca812302d0166058129c098053810006501b02432506049e8900930e05014a721be942037d26c06224b14b632720c863612d869c0320d0a08031401b6658047cca903f98a30601ac60aa328127009804e010011d0140238024046c02008c25304f232601b264081f8c50a530d3305f1a060a8328026c0b024f813207d32048fa634c120681a240cd009a0260230c4c81f0cb123e19030461ac688c340126409804c80d009802001ce934c14466944aa4d811332702246360444c4003180d809701a023d25a046a4a008cbd6a8ee626822e95aa24d26c278996811632701d864d0360c9808a992811432482206484374c6c07318a6072314018462052946b40878d3b05a1a6608a32812780b404b010006201b408433461080810208c708410140a1864e0430c8408598820401941080034b3b9eb54773d3a8c07a27926c5ae24d89d649a56a8934a709dc65a03b8c9d47599080eb32081a8640a434c7c08698f410a31e0180620524c6b48498d3a036194092605a024c09c41b00d110700e020e0100410c98a490d304920260208c4c04224b408349401057ad21d8c4d03b129a08199690e531b01ca62a0334c40a488d69061195092205a018406c87f80d00ff01401fa94803fa4a086da5350fc4a501b664d03f0c948300c78060015019604043e803807d00400f802721ee03603dc05487925050d949a81e46410364c6aa480d0105f18f0920040017c054079b13105e1a020ba33403cd87923e98d105c1a068a631c036deb007a3d500f262648f8640416c6b1a290c7048f026408831c611005006b31300ef624408631c610c050080c9401007a781f6f4e03e5e8a07b3d100f562721e294f43c128686c250581149601e264f03c0c8606c19040ee315c022620523869c82d0c7848e02700b402a03a803807480400e7324010404013b18b407631380eb62101d0c3813992b407325384e532d01ca64e0390c84066188148d1ad211a34e12040b404081380590212914340422866807124d2080314291234c42246808460ca008001401b695803852a826ca5300d94a040fe65891f8c9903f190108b1ac291034c422068003f816047e02600fc040421468006b25300de4a430f6934421068123e99014871a008fa040036de9c06d3d100d962701ac94191f0c9ca430d3847c02709acc4e035988406ab0e1c7b4a730f694291ecc9d03d990947b1a720f634211ec09c03d81080c901401a601c832402026881380d102101a0036137e4a00703d3c0df7a209bac4f0375886c0830e04dc4a789b094e037128606c25080d749b81a8936034925a067a4b247232740e4642520c69c8418d0847202700e4042032c08006480a00cb32020e234001c408006498a1058194099a95a033529c86625080cc49b28e065a41c0c9c82b98d84701ad00e034e015c68426501680ca0272190042032006c05f01600c602a017604c030c09005d01000c101e217203402e405005f3d390bb4a0817664112ed29c05da5080ba49b017263613124a0062bd3c0c47a22984c4f4309886c07b0e04c24a78184943030126f007a4b146f32720de6424158c542378d3806f1a100ac33612fc09e25e81380bf021817a04242f006e85c00d80bc015817002a218129a05a192849b3208136635022c65403f8c7905500f016401002ac080a3700d00aa02000dc03402bc6500570c700a902600da04002b066005580700aa008015203c029928242fa4d409c326813e64102b46940490d040901a0011032a01f863c054013806c02020a801e31212680438d01c6a19410c0f58029989862325000861ac38d032851ac098050a50105000e0140c4c028d28003d0c7104f00e209c01c028526803c8c7104d00e0140c3c01f468003c0c71053020209801c0289ea824dbd3009c62c013ec4c0264c6803e0d6007718e20a4058412c03903b0c7304a00e013464001d8638825007009a4a000ea34cc11c09804e3d3809b627013264e0250c540478d3809819f010832a020863a0398c7006b027012e042412403901f8070074194012ac4820dd29804a190007b19a407c01c024989804398d445c31480fa335412002403a8d3104700801209400218c9a22d98d407c1a6811e3294118024046252008a1940112948021d280e35190146a020010e940021527803a0ca008b7a70110c4e021929ce34193808419a80f632951a009c041190008032408ec34001d866803e99020761a600f034001a808003ea50007519400e833401e528003ca4c007a62408ecc4081d929803c250207662100ec94201d468403a0c7806902100fef4e01f989c03e193807b31500ee34e01cc668034013807102028dc01c01b802022998a505319a80da03e51a803c035004b0471a600d201001a928003480a006c4a028d66411148c6a8290d3406b194a8d001e01a002405b49400b57a78166f4e02c5e8a0583d100a7627014a94f029128642d250580c496013c64f0274c8604b18d4093315c01c620024469e0470d3808d195810632a020463e0390c7807018a80de314019c09c822807886062c18bec4c217d88042aa560c544a610a894001806b022f8d3005f1a000aa058115009802a010083f31410c6c48210d29841f18a00631a4008604c00f803802e2500c533200890040017528002ea4c005e62400b89400181e9c02fb13805b4a718a464e610c63a223013803700900b00341128c8002518d00534a0109464c0130c8002401000534a0108e6280138c68026a50005019a009c3280135260027b12044a620109494c0131280425310804a4a1108e642011c084024250004719400aaf4e015189c029253805149e809664e0124c680218d0583e18e808c04e80e463802224f203818e407a33420f0638220990804131b107632800fd27941c190043c01b007802ab0e128541c24d8c38321107063690e068501c0cd883d18d407a31920ec63021c010803801b507a02600f404a01d8090039318007001c510d89c821b10943e4a7207c942110cc9c021990904231900846310100c6021f0d3803e1a1007432810dc09c01b810846492800caf4f0191e88630b13cc5a62710c2c43216988442bb0e485661c188a94e2115284231193c06232190b263720d8c5300698804611a788b434e018468602d0d0805918f80ae31501586282228138045021006c01e14824a00913d3c1207a22a1cc4f4439886c05b0e050e4a7821c943042526f005a4b050232789da64e0408c8607699090e331ba19c636038cc5606718a80c7310816e620519869c8330d0903519508cc04e019808401a80d8033928104294d307d28240fa4d480a496005864d10a8c8201518d4026310004234d107c68200f8cd400a18a1012f440095870004a4b00317a21844c432021870217a50c81249b804892c1088c8600c98dc012315801062000b80100168120029320005294000be4a00163d3802b7a20054c4e2045282403a4b0028327101c62a00446820070c7400718a004af442015870002a4b04247a2004cc43009187060ea50c81d49b900692c1074c8600e98dc0163158006620007068000a8ca001c4a000452500085e9c0103d1001f6270030941007926ac03a4b0011320803a620006c69c00a0ca800c18f002a63410664a000cbd104186270030c42005d87060a25388144a100206350058c4020a0d380141a108252500049e8840330e04114a70022942004126c007a4b040e327001c6420034c6c2060d3800c1a10012f444015870002a4b04057a2000ac3800112582043d1000a6218010c38501d286803a4dd003496080e643001cc6e00318ac0033100860f4400c988601830e0c1a4a190349372009258213990c02731b901662b008cc4020d0d0c01a19b802632b002c63e0010c506577a204b2c43095d870ee8a50d9d149bb00292c9744c870e898de834315c00262057446868e88cdd137195c06831f40046282e8810c1d101b906802b04dc03e01a004c001004000003f
private def c111Links : DagLinks :=
  dagLookupLinks c111Index c111Edges 16 5 13 10 4 6
private def c111Data : Forest := fun i => decodeNode 10 23 0x1299a4a32d004e630094c72509680813000a260aae4b725096ccad2d99365b1a6cb604f96988600bd125861c0032507480812980a2530084a755c944cad28bd3dd201449c01093a4a32100aa49014c9202892403d24c94242327c8401091a4a122992a4232448634f909e9ce9496a3c7a647e05a8f00551e007a3c7a2ba52508d009f1a013a34015c6802a8d003f1a007a347a23a40108ca4a315c9422b02645ec398ad87115993e2b1a7c56c4e74868114bd56167a2446634898685118d06231a0446f548580b1100152207a242cc5a8586690eb0f61731443633686066b0c0cd21861e42ec4c858c9ee9496a0a02042401084a4a1053d6a0a7a2414c5a8298a905b1320b4a641665a828c86e9494203627c06c4e80c05102b0e60361c406635749eaafb3d11ff320bfef547d80b0fe0151fc7a23ecc3d7e0c6afcb0f1f86263ec6357d869ee94969e90203e40107ca4a0f4bd69e97a23d2c5a7a5282f49905e931abd294c7a86b4f48d0dd20263cec3974d870e9bd15df7a23be92d77d258ef8d0ddf021bbe94074d298ee8cddd301a3b6c49759882eb3101d61a73ac340758652e9a531d401bba604e74806e0080d1cf01839f55c6fd2b4df8ca1cc4ab37e3287292aadfa4b1c431a38e32a710652e20ca1c44aa37e01c708c90e00d31c002d37ef4f4e24a0debd113892d36c0106ea4a0db3d69b662636e95a6d92869c4941aa7a7b552506c9e9cd50041b07a2b5404e6b403cd6bd11aa6273543436a92849c3139a54a034e04e69403cd2a4b53802a346f4f66de88cd810d9b7a733e04266c03ecd98c59c00f33692c4e12a8ccc9698201a32a034658060cac941827ad304c41609ea8c7b0f19062631e95a60929cc12529824a4b0494e62126cc424b1884a430404c614090c2a4b18262630635a6086869c3121804a72ee93d5dd284be24b17c49e2ee0405e0020bc80f1784962ee3374e189cb731096e0082e6c385b929cb725096e4962dc34e5b86569c4941397a7a72f4e4e4038b4bd15397a227201c598c94b20d3964627272c4c588c9e9ca50160327272040578c429c988139624a9a32856806cacb1214d4a729a931538638aa80a95449829c328549260a798915000829e33e539280a68d39397a228694350d284a1a4b54349628634350c684a18c554318a2863344e5898a00cd140027a723344f80869c8d013c015a723404e803e9c81093800f8020284d40489ad5712332d2466284c8cac9198d13032aa4662a4a8c689698a52a3142546204a8ca8918ca12619e24e31c4986909201312402d246f4f0d64a090bd103532a23f25a43c0508d80911b00823725043deb487b131184ad21e64e43cc948799250f327222636444c408899210f1a721e9430d4c7a8519090b31021663c42926e1ac9690300820f25040deb481b1310432d2066430d64a0773d3cee0141ff2503f12907e9928fc7a71dc0103e9e8a770138f70151eef443b989c773d50f261e1e6c4c3c8c9e77190cee6241de62b3b8c841ab138e46211c801c3a402074b0e0e43241ce94e390c9c721908e431586a9343892a870bd3ccf7a219e94837988667a50ccf7a71b2f4436589c6ca508cf49b99ec423558706aa4d8cf00e1a692d33c0846800d8d049619e62a0d529c6424d8c832019604e320c506480d8c831086a054319e9e5c3d10b80241869432e007860a4dcb8021970f4e2f80845c00acb84a11729362e4c6c5c80a8b831006b25019de9e339928b47a70ce0102c9e8a33bd106719415c31c2b8694540cc0ac00e1540102a8078548138a86270cec4c29929e33a50c674a0146f5427d26850b0f0a062613e64f19cc8633bd389762712e940268c9c4b8cf89702112e63519d8904a1900943158cec4c24869e33a5008f19491e34e19c65633a5208c7a710832822929044b138844a010e94e211278428cd4841950ce64020863e339920807a70e6c4e1cd2803e9938733150e6c481e12603ca500781a70e69421d06843a0c787419a0e631e19c080388c546718a0ce0101b807c36a500681948d09401a4050348048680270ce0420d5e9e1b3d10361a40c66430d86861b3d385b6270b6c481712602ea5005c4a70b63420d863e1b00d05818a86c3140d9e9c233138464a00a694e11927a230cd05062409832813926026a5004c32708c942128c682325004719408e04e1180841b24f04432106e6310dcc6c2098c03749e07e3420dc04a1d80a83c0120763280dcc601c80703802106e01e0d806c1a804c01928066c43009e8818b0e0029280500080b809016bd38287a2050c4e0a12801499382831b804c43091e8812b0e02431000525006de9c0dbd101b62703693506cc400da5001c1a7036337009e880a31081461c028620050c680a8d0814195804f440312840624d80c496018642030c6c060d080c18f804c4300de8804b0e00331b80662b00d8700224b0043100063140080100080fc00 i
private def c111Sample : DagSample := (0x201804060061801260031800660201204048061201248031200648200a04028060a01228030a0062820110404406110124403110064420090402406090122403090062420108404206108124203108064220088402206088122203088062220028400a06028120a03028060a201044041061041241031040641200844021060841221030840621200144005060141205030140605, 66)
private def c111Tags := dagTraceTags b111.1 66
  (dagTagBases stock111 0xfff03f03f000fc003f03f03f03f000fc003ffc000003f000000000fff00000003f00000003ffff00000000000000003ffff 0x82082082082082081041041041041041030c30c30c30c30c30a28a28a28a28a28a0c30c30c30c30c30c5145145145145145 66) 10 c111Data
private def c111States := dagTrace b111.1 stock111 10 c111Data
private def c111MoveCert : List (DagMoveRecord 128) := [
  ([([(0xffffffff0000000000000000ffffffff, 0), (0xffffffff00000000, 32)], [(0xffffffff0000000000000000, 32)])], rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c03e78e9c3668c982e58a9426488901e3868c16284880e182840608080, rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c03e78e9c3668c982e58a9426488901e3868c16284880e182840608080),
  ([([(0xcc33cc33cc33cc33cc33cc33cc33cc33, 0), (0xcc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0x33003300330033003300330033003300, 6)])], rowSelectPacked 0xfffbbf6f7eb9f2fbf3af4f3e38f0dfbb3e6d7ab1e2dbb32e4d3a30e0bf7abd6b76a9d2bb72ad4b3628d09f3a3c6972a1c29b322c493220c07ef9bb676e99b27af1ab472e18b05eb93a656a91a25ab12a452a10a03e78b9636689923a70a9432608901e3838616281821a302841220080, rowSelectPacked 0xfffbbf6f7eb9f2fbf3af4f3e38f0dfbb3e6d7ab1e2dbb32e4d3a30e0bf7abd6b76a9d2bb72ad4b3628d09f3a3c6972a1c29b322c493220c07ef9bb676e99b27af1ab472e18b05eb93a656a91a25ab12a452a10a03e78b9636689923a70a9432608901e3838616281821a302841220080),
  ([([(0xcc33cc330000000000000000cc33cc33, 0), (0xcc00cc000000000000000000cc00cc, 6), (0x3300330000000000, 26), (0xcc33cc3300000000, 32), (0xcc00cc00000000, 38)], [(0x330033000000000000000000, 38), (0xcc33cc330000000000000000, 32), (0xcc00cc0000000000000000, 26), (0x33003300000000000000000033003300, 6)])], rowSelectPacked 0xfffbbf6f7eb9f2fbf3af4f3e38f0dfbb3e6d7ab1e2dbb32e4d3a30e07ef9bb676e99b27af1ab472e18b05eb93a656a91a25ab12a452a10a0bf7abd6b76a9d2bb72ad4b3628d09f3a3c6972a1c29b322c493220c03e78b9636689923a70a9432608901e3838616281821a302841220080, rowSelectPacked 0xfffbbf6f7eb9f2fbf3af4f3e38f0dfbb3e6d7ab1e2dbb32e4d3a30e07ef9bb676e99b27af1ab472e18b05eb93a656a91a25ab12a452a10a0bf7abd6b76a9d2bb72ad4b3628d09f3a3c6972a1c29b322c493220c03e78b9636689923a70a9432608901e3838616281821a302841220080),
  ([([(0x90099009900990099009900990099009, 0), (0x20022002200220022002200220022002, 1), (0x400040004000400040004000400040, 3), (0x900090009000900090009000900090, 4), (0x200020002000200020002000200020, 5)], [(0x4000400040004000400040004000400, 5), (0x9000900090009000900090009000900, 4), (0x2000200020002000200020002000200, 3), (0x40044004400440044004400440044004, 1)])], rowSelectPacked 0xfff7f7cefd7b74f7e7d78e7c7970dfb776ccf97364d7a7568c787160bf76f5caf56b54b766d58a7469509f3674c8f16344972654887061407ef5f3c6ed5b3476e5d3866c59305eb572c4e9532456a552846851203e74f1c2e54b143664d1826449101e3470c0e1430416245080604100, rowSelectPacked 0xfff7f7cefd7b74f7e7d78e7c7970dfb776ccf97364d7a7568c787160bf76f5caf56b54b766d58a7469509f3674c8f16344972654887061407ef5f3c6ed5b3476e5d3866c59305eb572c4e9532456a552846851203e74f1c2e54b143664d1826449101e3470c0e1430416245080604100),
  ([([(0x90099009000000000000000090099009, 0), (0x20022002000000000000000020022002, 1), (0x400040000000000000000000400040, 3), (0x900090000000000000000000900090, 4), (0x200020000000000000000000200020, 5), (0x400040000000000, 27), (0x900090000000000, 28), (0x200020000000000, 29), (0x4004400400000000, 31), (0x9009900900000000, 32), (0x2002200200000000, 33), (0x40004000000000, 35), (0x90009000000000, 36), (0x20002000000000, 37)], [(0x40004000000000000000000, 37), (0x90009000000000000000000, 36), (0x20002000000000000000000, 35), (0x400440040000000000000000, 33), (0x900990090000000000000000, 32), (0x200220020000000000000000, 31), (0x4000400000000000000000, 29), (0x9000900000000000000000, 28), (0x2000200000000000000000, 27), (0x4000400000000000000000004000400, 5), (0x9000900000000000000000009000900, 4), (0x2000200000000000000000002000200, 3), (0x40044004000000000000000040044004, 1)])], rowSelectPacked 0xfff7f7cefd7b74f7e7d78e7c7970dfb776ccf97364d7a7568c7871607ef5f3c6ed5b3476e5d3866c59305eb572c4e9532456a55284685120bf76f5caf56b54b766d58a7469509f3674c8f16344972654887061403e74f1c2e54b143664d1826449101e3470c0e1430416245080604100, rowSelectPacked 0xfff7f7cefd7b74f7e7d78e7c7970dfb776ccf97364d7a7568c7871607ef5f3c6ed5b3476e5d3866c59305eb572c4e9532456a55284685120bf76f5caf56b54b766d58a7469509f3674c8f16344972654887061403e74f1c2e54b143664d1826449101e3470c0e1430416245080604100),
  ([([(0x80018001800180018001800180018001, 0), (0x20002000200020002000200020002, 1), (0x40004000400040004000400040004, 2), (0x80008000800080008000800080008, 3), (0x100010001000100010001000100010, 4), (0x200020002000200020002000200020, 5), (0x400040004000400040004000400040, 6), (0x800080008000800080008000800080, 7)], [(0x1000100010001000100010001000100, 7), (0x2000200020002000200020002000200, 6), (0x4000400040004000400040004000400, 5), (0x8000800080008000800080008000800, 4), (0x10001000100010001000100010001000, 3), (0x20002000200020002000200020002000, 2), (0x40004000400040004000400040004000, 1)])], rowSelectPacked 0xffdff76fbd7e74f7cfd72f3c7c70df9f766db97664d78f562d387460bf5ef56bb56e54b74ed52b346c509f1e7469b16644970e54293064407eddf367ad5e3476cdd3272c5c305e9d7265a95624568d52252854203e5cf163a54e14364cd123244c101e1c7061a14604160c5021204400, rowSelectPacked 0xfff7df9efd79f1fdf3d78edd3970dfb75e9cf971e1ddb3568cd93160bf76dd9af569d1bd72d58ad529509f365c98f161c19d325488d121407ef5db96ed59b17cf1d386cd19305eb55a94e951a15cb15284c911203e74d992e549913c70d182c509101e345890e141811c305080c10100),
  ([([(0x80018001000000000000000080018001, 0), (0x20002000000000000000000020002, 1), (0x40004000000000000000000040004, 2), (0x80008000000000000000000080008, 3), (0x100010000000000000000000100010, 4), (0x200020000000000000000000200020, 5), (0x400040000000000000000000400040, 6), (0x800080000000000000000000800080, 7), (0x100010000000000, 25), (0x200020000000000, 26), (0x400040000000000, 27), (0x800080000000000, 28), (0x1000100000000000, 29), (0x2000200000000000, 30), (0x4000400000000000, 31), (0x8001800100000000, 32), (0x2000200000000, 33), (0x4000400000000, 34), (0x8000800000000, 35), (0x10001000000000, 36), (0x20002000000000, 37), (0x40004000000000, 38), (0x80008000000000, 39)], [(0x10001000000000000000000, 39), (0x20002000000000000000000, 38), (0x40004000000000000000000, 37), (0x80008000000000000000000, 36), (0x100010000000000000000000, 35), (0x200020000000000000000000, 34), (0x400040000000000000000000, 33), (0x800180010000000000000000, 32), (0x200020000000000000000, 31), (0x400040000000000000000, 30), (0x800080000000000000000, 29), (0x1000100000000000000000, 28), (0x2000200000000000000000, 27), (0x4000400000000000000000, 26), (0x8000800000000000000000, 25), (0x1000100000000000000000001000100, 7), (0x2000200000000000000000002000200, 6), (0x4000400000000000000000004000400, 5), (0x8000800000000000000000008000800, 4), (0x10001000000000000000000010001000, 3), (0x20002000000000000000000020002000, 2), (0x40004000000000000000000040004000, 1)])], rowSelectPacked 0xffdff76fbd7e74f7cfd72f3c7c70df9f766db97664d78f562d3874607eddf367ad5e3476cdd3272c5c305e9d7265a95624568d5225285420bf5ef56bb56e54b74ed52b346c509f1e7469b16644970e54293064403e5cf163a54e14364cd123244c101e1c7061a14604160c5021204400, rowSelectPacked 0xfff7df9efd79f1fdf3d78edd3970dfb75e9cf971e1ddb3568cd931607ef5db96ed59b17cf1d386cd19305eb55a94e951a15cb15284c91120bf76dd9af569d1bd72d58ad529509f365c98f161c19d325488d121403e74d992e549913c70d182c509101e345890e141811c305080c10100),
  ([([(0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0x50505050505050505050505050505050, 3)])], rowSelectPacked 0xffefef9fdebe78efcfaf1edcba70dfaf6e9ddab668cf8f2e1cd8b260bf6eed9bd6ae58af4ead1ad4aa509f2e6c99d2a6488f0e2c18d0a2407eedeb97ce9e386ecdab16cc9a305ead6a95ca96284e8d2a14c892203e6ce993c68e182e4ca912c48a101e2c6891c286080e0c2810c08200, rowSelectPacked 0xffefef9fdebe78efcfaf1edcba70dfaf6e9ddab668cf8f2e1cd8b260bf6eed9bd6ae58af4ead1ad4aa509f2e6c99d2a6488f0e2c18d0a2407eedeb97ce9e386ecdab16cc9a305ead6a95ca96284e8d2a14c892203e6ce993c68e182e4ca912c48a101e2c6891c286080e0c2810c08200),
  ([([(0xa5a5a5a50000000000000000a5a5a5a5, 0), (0xa0a0a0a00000000000000000a0a0a0a, 3), (0x5050505000000000, 29), (0xa5a5a5a500000000, 32), (0xa0a0a0a00000000, 35)], [(0x505050500000000000000000, 35), (0xa5a5a5a50000000000000000, 32), (0xa0a0a0a0000000000000000, 29), (0x50505050000000000000000050505050, 3)])], rowSelectPacked 0xffefef9fdebe78efcfaf1edcba70dfaf6e9ddab668cf8f2e1cd8b2607eedeb97ce9e386ecdab16cc9a305ead6a95ca96284e8d2a14c89220bf6eed9bd6ae58af4ead1ad4aa509f2e6c99d2a6488f0e2c18d0a2403e6ce993c68e182e4ca912c48a101e2c6891c286080e0c2810c08200, rowSelectPacked 0xffefef9fdebe78efcfaf1edcba70dfaf6e9ddab668cf8f2e1cd8b2607eedeb97ce9e386ecdab16cc9a305ead6a95ca96284e8d2a14c89220bf6eed9bd6ae58af4ead1ad4aa509f2e6c99d2a6488f0e2c18d0a2403e6ce993c68e182e4ca912c48a101e2c6891c286080e0c2810c08200),
  ([([(0x84218421842184218421842184218421, 0), (0x8420842084208420842084208420842, 3), (0x840084008400840084008400840084, 6), (0x80008000800080008000800080008, 9)], [(0x10001000100010001000100010001000, 9), (0x21002100210021002100210021002100, 6), (0x42104210421042104210421042104210, 3)])], rowSelectPacked 0xffefbf3fdebb72fbe7af1f9e3a70dfaf3e3ddab362dba72e1d9a3260bf6ebd3bd6ab52bb66ad1b962a509f2e3c39d2a3429b262c199222407eedbb37ce9b327ae5ab178e1a305ead3a35ca93225aa52a158a12203e6cb933c68b123a64a913860a101e2c3831c283021a242811820200, rowSelectPacked 0xffefbf3fdebb72fbe7af1f9e3a70dfaf3e3ddab362dba72e1d9a3260bf6ebd3bd6ab52bb66ad1b962a509f2e3c39d2a3429b262c199222407eedbb37ce9b327ae5ab178e1a305ead3a35ca93225aa52a158a12203e6cb933c68b123a64a913860a101e2c3831c283021a242811820200),
  ([([(0x84218421000000000000000084218421, 0), (0x8420842000000000000000008420842, 3), (0x840084000000000000000000840084, 6), (0x80008000000000000000000080008, 9), (0x1000100000000000, 23), (0x2100210000000000, 26), (0x4210421000000000, 29), (0x8421842100000000, 32), (0x842084200000000, 35), (0x84008400000000, 38), (0x8000800000000, 41)], [(0x100010000000000000000000, 41), (0x210021000000000000000000, 38), (0x421042100000000000000000, 35), (0x842184210000000000000000, 32), (0x84208420000000000000000, 29), (0x8400840000000000000000, 26), (0x800080000000000000000, 23), (0x10001000000000000000000010001000, 9), (0x21002100000000000000000021002100, 6), (0x42104210000000000000000042104210, 3)])], rowSelectPacked 0xffefbf3fdebb72fbe7af1f9e3a70dfaf3e3ddab362dba72e1d9a32607eedbb37ce9b327ae5ab178e1a305ead3a35ca93225aa52a158a1220bf6ebd3bd6ab52bb66ad1b962a509f2e3c39d2a3429b262c199222403e6cb933c68b123a64a913860a101e2c3831c283021a242811820200, rowSelectPacked 0xffefbf3fdebb72fbe7af1f9e3a70dfaf3e3ddab362dba72e1d9a32607eedbb37ce9b327ae5ab178e1a305ead3a35ca93225aa52a158a1220bf6ebd3bd6ab52bb66ad1b962a509f2e3c39d2a3429b262c199222403e6cb933c68b123a64a913860a101e2c3831c283021a242811820200),
  ([([(0x80018001800180018001800180018001, 0), (0x20002000200020002000200020002000, 1), (0x8000800080008000800080008000800, 2), (0x2000200020002000200020002000200, 3), (0x800080008000800080008000800080, 4), (0x200020002000200020002000200020, 5), (0x80008000800080008000800080008, 6), (0x20002000200020002000200020002, 7)], [(0x40004000400040004000400040004000, 7), (0x10001000100010001000100010001000, 6), (0x4000400040004000400040004000400, 5), (0x1000100010001000100010001000100, 4), (0x400040004000400040004000400040, 3), (0x100010001000100010001000100010, 2), (0x40004000400040004000400040004, 1)])], rowSelectPacked 0xfff7df9efd79f1fdf3d78edd3970dfb75e9cf971e1ddb3568cd93160bf76dd9af569d1bd72d58ad529509f365c98f161c19d325488d121407ef5db96ed59b17cf1d386cd19305eb55a94e951a15cb15284c911203e74d992e549913c70d182c509101e345890e141811c305080c10100, rowSelectPacked 0xffdff76fbd7e74f7cfd72f3c7c70df9f766db97664d78f562d387460bf5ef56bb56e54b74ed52b346c509f1e7469b16644970e54293064407eddf367ad5e3476cdd3272c5c305e9d7265a95624568d52252854203e5cf163a54e14364cd123244c101e1c7061a14604160c5021204400),
  ([([(0x80018001000000000000000080018001, 0), (0x20002000000000000000000020002000, 1), (0x8000800000000000000000008000800, 2), (0x2000200000000000000000002000200, 3), (0x800080000000000000000000800080, 4), (0x200020000000000000000000200020, 5), (0x80008000000000000000000080008, 6), (0x20002000000000000000000020002, 7), (0x4000400000000000, 25), (0x1000100000000000, 26), (0x400040000000000, 27), (0x100010000000000, 28), (0x40004000000000, 29), (0x10001000000000, 30), (0x4000400000000, 31), (0x8001800100000000, 32), (0x2000200000000000, 33), (0x800080000000000, 34), (0x200020000000000, 35), (0x80008000000000, 36), (0x20002000000000, 37), (0x8000800000000, 38), (0x2000200000000, 39)], [(0x400040000000000000000000, 39), (0x100010000000000000000000, 38), (0x40004000000000000000000, 37), (0x10001000000000000000000, 36), (0x4000400000000000000000, 35), (0x1000100000000000000000, 34), (0x400040000000000000000, 33), (0x800180010000000000000000, 32), (0x200020000000000000000000, 31), (0x80008000000000000000000, 30), (0x20002000000000000000000, 29), (0x8000800000000000000000, 28), (0x2000200000000000000000, 27), (0x800080000000000000000, 26), (0x200020000000000000000, 25), (0x40004000000000000000000040004000, 7), (0x10001000000000000000000010001000, 6), (0x4000400000000000000000004000400, 5), (0x1000100000000000000000001000100, 4), (0x400040000000000000000000400040, 3), (0x100010000000000000000000100010, 2), (0x40004000000000000000000040004, 1)])], rowSelectPacked 0xfff7df9efd79f1fdf3d78edd3970dfb75e9cf971e1ddb3568cd931607ef5db96ed59b17cf1d386cd19305eb55a94e951a15cb15284c91120bf76dd9af569d1bd72d58ad529509f365c98f161c19d325488d121403e74d992e549913c70d182c509101e345890e141811c305080c10100, rowSelectPacked 0xffdff76fbd7e74f7cfd72f3c7c70df9f766db97664d78f562d3874607eddf367ad5e3476cdd3272c5c305e9d7265a95624568d5225285420bf5ef56bb56e54b74ed52b346c509f1e7469b16644970e54293064403e5cf163a54e14364cd123244c101e1c7061a14604160c5021204400),
  ([([(0x82418241824182418241824182418241, 0), (0x8040804080408040804080408040804, 2), (0x200020002000200020002000200020, 5), (0x820082008200820082008200820082, 7), (0x80008000800080008000800080008, 9)], [(0x10001000100010001000100010001000, 9), (0x41004100410041004100410041004100, 7), (0x4000400040004000400040004000400, 5), (0x20102010201020102010201020102010, 2)])], rowSelectPacked 0xffdfdf3fbd7cf1fddbd72f9d3c70df9f5e3db974e1dd9b562d993460bf5edd3bb56cd1bd5ad52b952c509f1e5c39b164c19d1a54299124407edddb37ad5cb17cd9d3278d1c305e9d5a35a954a15c9952258914203e5cd933a54c913c58d123850c101e1c5831a144811c185021810400, rowSelectPacked 0xffdfdf3fbd7cf1fddbd72f9d3c70df9f5e3db974e1dd9b562d993460bf5edd3bb56cd1bd5ad52b952c509f1e5c39b164c19d1a54299124407edddb37ad5cb17cd9d3278d1c305e9d5a35a954a15c9952258914203e5cd933a54c913c58d123850c101e1c5831a144811c185021810400),
  ([([(0x82418241000000000000000082418241, 0), (0x8040804000000000000000008040804, 2), (0x200020000000000000000000200020, 5), (0x820082000000000000000000820082, 7), (0x80008000000000000000000080008, 9), (0x1000100000000000, 23), (0x4100410000000000, 25), (0x400040000000000, 27), (0x2010201000000000, 30), (0x8241824100000000, 32), (0x804080400000000, 34), (0x20002000000000, 37), (0x82008200000000, 39), (0x8000800000000, 41)], [(0x100010000000000000000000, 41), (0x410041000000000000000000, 39), (0x40004000000000000000000, 37), (0x201020100000000000000000, 34), (0x824182410000000000000000, 32), (0x80408040000000000000000, 30), (0x2000200000000000000000, 27), (0x8200820000000000000000, 25), (0x800080000000000000000, 23), (0x10001000000000000000000010001000, 9), (0x41004100000000000000000041004100, 7), (0x4000400000000000000000004000400, 5), (0x20102010000000000000000020102010, 2)])], rowSelectPacked 0xffdfdf3fbd7cf1fddbd72f9d3c70df9f5e3db974e1dd9b562d9934607edddb37ad5cb17cd9d3278d1c305e9d5a35a954a15c995225891420bf5edd3bb56cd1bd5ad52b952c509f1e5c39b164c19d1a54299124403e5cd933a54c913c58d123850c101e1c5831a144811c185021810400, rowSelectPacked 0xffdfdf3fbd7cf1fddbd72f9d3c70df9f5e3db974e1dd9b562d9934607edddb37ad5cb17cd9d3278d1c305e9d5a35a954a15c995225891420bf5edd3bb56cd1bd5ad52b952c509f1e5c39b164c19d1a54299124403e5cd933a54c913c58d123850c101e1c5831a144811c185021810400)]
private def c111Moves := dagMoves c111MoveCert

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Autos : DagMovesOK b111.1 b111.2.2.2 128 c111Moves :=
  dagMovesOfCheck (by decide +kernel)

private def c111Check := dagCheckNode b111.1 b111.2.2.2 none (dagKnownCloses b111.2.2.2 cuts111) 615
  c111States c111Moves c111Links c111Sample c111Tags

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Roots :
    dagCheckRoots b111.1 b111.2.2.2 none (dagKnownCloses b111.2.2.2 cuts111) []
      (dagRef 615 c111States c111Moves c111Links 0) stock111 10 = true := by
  decide +kernel

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block0 : treeBlock 0 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block8 : treeBlock 8 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block16 : treeBlock 16 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block24 : treeBlock 24 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block32 : treeBlock 32 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block40 : treeBlock 40 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block48 : treeBlock 48 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block56 : treeBlock 56 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block64 : treeBlock 64 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block72 : treeBlock 72 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block80 : treeBlock 80 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block88 : treeBlock 88 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block96 : treeBlock 96 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block104 : treeBlock 104 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block112 : treeBlock 112 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block120 : treeBlock 120 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block128 : treeBlock 128 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block136 : treeBlock 136 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block144 : treeBlock 144 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block152 : treeBlock 152 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block160 : treeBlock 160 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block168 : treeBlock 168 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block176 : treeBlock 176 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block184 : treeBlock 184 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block192 : treeBlock 192 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block200 : treeBlock 200 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block208 : treeBlock 208 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block216 : treeBlock 216 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block224 : treeBlock 224 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block232 : treeBlock 232 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block240 : treeBlock 240 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block248 : treeBlock 248 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block256 : treeBlock 256 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block264 : treeBlock 264 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block272 : treeBlock 272 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block280 : treeBlock 280 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block288 : treeBlock 288 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block296 : treeBlock 296 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block304 : treeBlock 304 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block312 : treeBlock 312 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block320 : treeBlock 320 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block328 : treeBlock 328 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block336 : treeBlock 336 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block344 : treeBlock 344 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block352 : treeBlock 352 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block360 : treeBlock 360 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block368 : treeBlock 368 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block376 : treeBlock 376 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block384 : treeBlock 384 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block392 : treeBlock 392 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block400 : treeBlock 400 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block408 : treeBlock 408 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block416 : treeBlock 416 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block424 : treeBlock 424 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block432 : treeBlock 432 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block440 : treeBlock 440 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block448 : treeBlock 448 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block456 : treeBlock 456 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block464 : treeBlock 464 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block472 : treeBlock 472 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block480 : treeBlock 480 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block488 : treeBlock 488 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block496 : treeBlock 496 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block504 : treeBlock 504 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block512 : treeBlock 512 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block520 : treeBlock 520 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block528 : treeBlock 528 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block536 : treeBlock 536 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block544 : treeBlock 544 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block552 : treeBlock 552 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block560 : treeBlock 560 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block568 : treeBlock 568 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block576 : treeBlock 576 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block584 : treeBlock 584 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block592 : treeBlock 592 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block600 : treeBlock 600 8 c111Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c111Block608 : treeBlock 608 7 c111Check = true := by decide +kernel

private theorem c111Checked : treeBlock 0 615 c111Check = true :=
  (@treeBlock_merge 0 304 311 c111Check
    (@treeBlock_merge 0 152 152 c111Check
    (@treeBlock_merge 0 72 80 c111Check
    (@treeBlock_merge 0 32 40 c111Check
    (@treeBlock_merge 0 16 16 c111Check
    (@treeBlock_merge 0 8 8 c111Check
    c111Block0
    c111Block8)
    (@treeBlock_merge 16 8 8 c111Check
    c111Block16
    c111Block24))
    (@treeBlock_merge 32 16 24 c111Check
    (@treeBlock_merge 32 8 8 c111Check
    c111Block32
    c111Block40)
    (@treeBlock_merge 48 8 16 c111Check
    c111Block48
    (@treeBlock_merge 56 8 8 c111Check
    c111Block56
    c111Block64))))
    (@treeBlock_merge 72 40 40 c111Check
    (@treeBlock_merge 72 16 24 c111Check
    (@treeBlock_merge 72 8 8 c111Check
    c111Block72
    c111Block80)
    (@treeBlock_merge 88 8 16 c111Check
    c111Block88
    (@treeBlock_merge 96 8 8 c111Check
    c111Block96
    c111Block104)))
    (@treeBlock_merge 112 16 24 c111Check
    (@treeBlock_merge 112 8 8 c111Check
    c111Block112
    c111Block120)
    (@treeBlock_merge 128 8 16 c111Check
    c111Block128
    (@treeBlock_merge 136 8 8 c111Check
    c111Block136
    c111Block144)))))
    (@treeBlock_merge 152 72 80 c111Check
    (@treeBlock_merge 152 32 40 c111Check
    (@treeBlock_merge 152 16 16 c111Check
    (@treeBlock_merge 152 8 8 c111Check
    c111Block152
    c111Block160)
    (@treeBlock_merge 168 8 8 c111Check
    c111Block168
    c111Block176))
    (@treeBlock_merge 184 16 24 c111Check
    (@treeBlock_merge 184 8 8 c111Check
    c111Block184
    c111Block192)
    (@treeBlock_merge 200 8 16 c111Check
    c111Block200
    (@treeBlock_merge 208 8 8 c111Check
    c111Block208
    c111Block216))))
    (@treeBlock_merge 224 40 40 c111Check
    (@treeBlock_merge 224 16 24 c111Check
    (@treeBlock_merge 224 8 8 c111Check
    c111Block224
    c111Block232)
    (@treeBlock_merge 240 8 16 c111Check
    c111Block240
    (@treeBlock_merge 248 8 8 c111Check
    c111Block248
    c111Block256)))
    (@treeBlock_merge 264 16 24 c111Check
    (@treeBlock_merge 264 8 8 c111Check
    c111Block264
    c111Block272)
    (@treeBlock_merge 280 8 16 c111Check
    c111Block280
    (@treeBlock_merge 288 8 8 c111Check
    c111Block288
    c111Block296))))))
    (@treeBlock_merge 304 152 159 c111Check
    (@treeBlock_merge 304 72 80 c111Check
    (@treeBlock_merge 304 32 40 c111Check
    (@treeBlock_merge 304 16 16 c111Check
    (@treeBlock_merge 304 8 8 c111Check
    c111Block304
    c111Block312)
    (@treeBlock_merge 320 8 8 c111Check
    c111Block320
    c111Block328))
    (@treeBlock_merge 336 16 24 c111Check
    (@treeBlock_merge 336 8 8 c111Check
    c111Block336
    c111Block344)
    (@treeBlock_merge 352 8 16 c111Check
    c111Block352
    (@treeBlock_merge 360 8 8 c111Check
    c111Block360
    c111Block368))))
    (@treeBlock_merge 376 40 40 c111Check
    (@treeBlock_merge 376 16 24 c111Check
    (@treeBlock_merge 376 8 8 c111Check
    c111Block376
    c111Block384)
    (@treeBlock_merge 392 8 16 c111Check
    c111Block392
    (@treeBlock_merge 400 8 8 c111Check
    c111Block400
    c111Block408)))
    (@treeBlock_merge 416 16 24 c111Check
    (@treeBlock_merge 416 8 8 c111Check
    c111Block416
    c111Block424)
    (@treeBlock_merge 432 8 16 c111Check
    c111Block432
    (@treeBlock_merge 440 8 8 c111Check
    c111Block440
    c111Block448)))))
    (@treeBlock_merge 456 80 79 c111Check
    (@treeBlock_merge 456 40 40 c111Check
    (@treeBlock_merge 456 16 24 c111Check
    (@treeBlock_merge 456 8 8 c111Check
    c111Block456
    c111Block464)
    (@treeBlock_merge 472 8 16 c111Check
    c111Block472
    (@treeBlock_merge 480 8 8 c111Check
    c111Block480
    c111Block488)))
    (@treeBlock_merge 496 16 24 c111Check
    (@treeBlock_merge 496 8 8 c111Check
    c111Block496
    c111Block504)
    (@treeBlock_merge 512 8 16 c111Check
    c111Block512
    (@treeBlock_merge 520 8 8 c111Check
    c111Block520
    c111Block528))))
    (@treeBlock_merge 536 40 39 c111Check
    (@treeBlock_merge 536 16 24 c111Check
    (@treeBlock_merge 536 8 8 c111Check
    c111Block536
    c111Block544)
    (@treeBlock_merge 552 8 16 c111Check
    c111Block552
    (@treeBlock_merge 560 8 8 c111Check
    c111Block560
    c111Block568)))
    (@treeBlock_merge 576 16 23 c111Check
    (@treeBlock_merge 576 8 8 c111Check
    c111Block576
    c111Block584)
    (@treeBlock_merge 592 8 15 c111Check
    c111Block592
    (@treeBlock_merge 600 8 7 c111Check
    c111Block600
    c111Block608)))))))

private theorem lower111 : Lower b111.1 stock111 b111.2.2.2 11 := by
  exact lowerDag (width := 128) (chart := none)
    (by unfold Masked; decide +kernel) (by unfold Masked; decide +kernel)
    (by unfold properWord; decide +kernel) (by simp) c111Autos
    (by unfold Masked; decide +kernel) (by decide +kernel) (by decide +kernel)
    (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower110) lower109) lower107) lower103) lower79) lower47) (by decide +kernel)
    c111Roots c111Checked

private def stock119 : List Word := [0xaa00aa00aa00aa00aa00aa00aa00aa, 0xcc00cc00cc00cc00cc00cc00cc00cc, 0xf000f000f000f000f000f000f000f0, 0xff000000ff000000ff000000ff0000, 0xff00ff0000000000ff00ff00000000, 0xff00ff00ff00ff0000000000000000]
private def b119 : Bound := (0xff00ff00ff00ff00ff00ff00ff00ff, stock119, 11, 0xff00ff00ff00fe00ff00fe00fe00a0)
private def cuts119 : List Bound := [b117, b55, b87, b103, b115, b118]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks119 : treeBlock 0 (2 ^ stock119.length) (fun token =>
    closes b119.1 b119.2.2.2 cuts119 10 (rootState stock119 10 token)) = true := by
  decide +kernel
private theorem lower119 : Lower b119.1 stock119 b119.2.2.2 11 := by
  exact deriveLower b119.1 b119.2.2.2 stock119 cuts119 10
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower118) lower115) lower103) lower87) lower55) lower117)
    (by unfold cuts119; decide +kernel) checks119

private def stock123 : List Word := [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 0xf000f000f000f000f000f000f000f00, 0xf0f00000f0f00000f0f00000f0f0000, 0xf0f0f0f000000000f0f0f0f00000000, 0xf0f0f0f0f0f0f0f0000000000000000]
private def b123 : Bound := (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, stock123, 10, 0xf0f0f0f0f0f0f0e0f0f0f0e0e0e0c00)
private def cuts123 : List Bound := [b107, b115, b121, b122, b59, b91]
private def c123Index : Nat := 0x7396a44e1
private def c123Edges : Nat := 0x2c94524a04f4497a21b10c5870003f
private def c123Links : DagLinks :=
  dagLookupLinks c123Index c123Edges 5 2 13 3 1 3
private def c123Data : Forest := fun i => decodeNode 3 16 0x928c928462197a2261c101f8 i
private def c123Sample : DagSample := (0x2018040600c1801260019808050101403050049400650200c040300c0c01230018c08048101203048049200648200a040280c0a01228018a080421010830420490806422008840220c088122201888801210048301204848061220028400a0c028120a0182880411010430410490406412008440210c0841221018848011100443011048440611, 60)
private def c123Tags := dagTraceTags b123.1 60
  (dagTagBases stock123 0xffc1f07c0007c00f83e0f83e0003e007fe00001f0001f0001ff8000f80000000007ffff8000000000000007fff 0x842108421084210421084210842108210842108421084318c6318c6318c608421084210842118c6318c6318c63 60) 9 c123Data
private def c123States := dagTrace b123.1 stock123 9 c123Data
private def c123MoveCert : List (DagMoveRecord 128) := [
  ([([(0xffffffff0000000000000000ffffffff, 0), (0xffffffff00000000, 32)], [(0xffffffff0000000000000000, 32)])], rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c03e78e9c3668c982e58a9426488901e3868c16284880e182840608080, rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c03e78e9c3668c982e58a9426488901e3868c16284880e182840608080)]
private def c123Moves := dagMoves c123MoveCert

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Autos : DagMovesOK b123.1 b123.2.2.2 128 c123Moves :=
  dagMovesOfCheck (by decide +kernel)

private def c123Check := dagCheckNode b123.1 b123.2.2.2 none (dagKnownCloses b123.2.2.2 cuts123) 6
  c123States c123Moves c123Links c123Sample c123Tags

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Roots :
    dagCheckRoots b123.1 b123.2.2.2 none (dagKnownCloses b123.2.2.2 cuts123) []
      (dagRef 6 c123States c123Moves c123Links 0) stock123 9 = true := by
  decide +kernel

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block0 : treeBlock 0 3 c123Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c123Block3 : treeBlock 3 3 c123Check = true := by decide +kernel

private theorem c123Checked : treeBlock 0 6 c123Check = true :=
  (@treeBlock_merge 0 3 3 c123Check
    c123Block0
    c123Block3)

private theorem lower123 : Lower b123.1 stock123 b123.2.2.2 10 := by
  exact lowerDag (width := 128) (chart := none)
    (by unfold Masked; decide +kernel) (by unfold Masked; decide +kernel)
    (by unfold properWord; decide +kernel) (by simp) c123Autos
    (by unfold Masked; decide +kernel) (by decide +kernel) (by decide +kernel)
    (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower91) lower59) lower122) lower121) lower115) lower107) (by decide +kernel)
    c123Roots c123Checked

private def stock125 : List Word := [0x22222222222222222222222222222222, 0x30303030303030303030303030303030, 0x33003300330033003300330033003300, 0x33330000333300003333000033330000, 0x33333333000000003333333300000000, 0x33333333333333330000000000000000]
private def b125 : Bound := (0x33333333333333333333333333333333, stock125, 11, 0x33333333333333323333333232322020)
private def cuts125 : List Bound := [b117, b61, b93, b109, b121, b124]
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem checks125 : treeBlock 0 (2 ^ stock125.length) (fun token =>
    closes b125.1 b125.2.2.2 cuts125 10 (rootState stock125 10 token)) = true := by
  decide +kernel
private theorem lower125 : Lower b125.1 stock125 b125.2.2.2 11 := by
  exact deriveLower b125.1 b125.2.2.2 stock125 cuts125 10
    (by decide) (by unfold Masked; decide +kernel) (by unfold properWord; decide +kernel)
    (by unfold Masked; decide +kernel) (by decide +kernel) (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower124) lower121) lower109) lower93) lower61) lower117)
    (by unfold cuts125; decide +kernel) checks125

private def stock126 : List Word := [0x44444444444444444444444444444444, 0x50505050505050505050505050505050, 0x55005500550055005500550055005500, 0x55550000555500005555000055550000, 0x55555555000000005555555500000000, 0x55555555555555550000000000000000]
private def b126 : Bound := (0x55555555555555555555555555555555, stock126, 10, 0x55555555555555545555555454544400)
private def cuts126 : List Bound := [b110, b118, b122, b124, b62, b94]
private theorem lower126 : Lower b126.1 stock126 b126.2.2.2 10 :=
  lowerRelabelMasked (rowSelectPacked 0xffefef9fdebe78efcfaf1edcba70dfaf6e9ddab668cf8f2e1cd8b260bf6eed9bd6ae58af4ead1ad4aa509f2e6c99d2a6488f0e2c18d0a2407eedeb97ce9e386ecdab16cc9a305ead6a95ca96284e8d2a14c892203e6ce993c68e182e4ca912c48a101e2c6891c286080e0c2810c08200) lower123
    (by decide +kernel) (by decide +kernel) (suppliesOfCheck (by decide +kernel))

private def stock127 : List Word := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000]
private def b127 : Bound := (0xffffffffffffffffffffffffffffffff, stock127, 13, 0xfffffffffffffffefffffffefefeeca0)
private def cuts127 : List Bound := [b111, b119, b125, b63, b95, b123, b126]
private def c127Index : Nat := 0x2c3076088af57d7a82bc495e20aec2d70aeb8415bc3ade056e86b6c55ac5ace456702b34359a0ac9256482b08f5840ac10d6006af47562caa46d508ea6cd5287a94054a02a4475201a8e154496a2415101a86153f229f814e4ca7205380a9a4f4d20a6715320e96574b20a59052c8296414a09a5005268e93034942a4245210290434747a3a051b8e8dc14683a2c45148e8a034484a1c4506be824940a4a0505001680013f849fc04fe027dcb3d8b9e824f40279473ba89dc0cee0275113a809d11ce692715138819c404e1866ed137609b914dc066dc336649b20cd7126a8933cc9992cca16648531299880cbfa65f832ea996964b406588d2bc495c14ab9655832a449475ca1924f4d27629372499924bc92526927149192451f21e590d14858a420720088fe147e0a3e851ea58f40c788e3bc51d078e70c730638c71c418df1c6e8a360b1ac28d31c6792330719238c80c6386310717e58b64c5a862d0316238a754520e28c3144189b3c4c8a260312e18922c459e22c111608881c3e321f010f4287a043d021e430f20879043c061adb0d038651c310e17c70b26859042c0615c30ac18550c2892134908898430c1e9a0e4906e28332419060b8905c082a241502098903e781c1c0d8606c102e48160c098e04c102228100c07860307018080a1401220080ffa57f923fc05fccafe417f10bf789fa0efce17e60bf209f8c2fc417e10bee15f6c2fb417d90beb89f3d0f9e07cd13e605f18cf8c07c603e301f180f8c07c603e111f080f8407bc33de01ee84f7217b523da05ec84f5e37ad13d589eac0f5607a913d291e750f3a079d03ce81e740f3a079d03cc91e640f32079333c42de1c2f0e078703c191e082f04078203bf11dec6eec577413b241d330e98074c03a601d300e9807491ba389d1c0e8e07441b9f95cf82e78273c039d85ce44e6287300b9785cbc0e5c172b1b9581ca82e5407290b9405c908e48071d3b8e05c6c2e341716238b01c504e20470c23848dc1c4e0a26ff337f81bf82df826fa137d01be42df206f80b7a8dbd40de626f3037981bc44dda46ed037589ba06dce16e41b7185b8c0dc606df236f05b6c6db416d8136b85b5c0dac16d50b6891b1d4d76c6b81b5b85ad82d6a16b1235691aac4d5226a7135099a7c4d326697134991a444d1a468d034605a246d0286800b3f099f42cf8167c033a219a18cd006651b30919650cb01658032b8593d0c9c164a232501910cc86163f231f818fc0c7e0639331b898d82c6826276b13058942c481620230f8586c8c36061b030c898602c2c261223080982cac1226080b028d8086bfe35f932fc057e00bec25f31af8897c40be205ee1af7017b04bd805eb0af5817ac0bd225e902f405784ebc205e102f0817786bb635db02ec0d7600ba465d10ae88173c4b9645c912e4817202b8e15c22ae1016fc6b7c15be02df016f80b7635bb02dc0d6e00b7005b802dc016d46b6a05b40ada016cc2b6605a382ca3d6218af6d5743aba015c46acac56502b2815902ac8056402b185559aaa2555102a70d5342a9625481aa4014fd2a7e05364a9b014b52a42c51d228aa14540a26250d32849140509eac4ef3273a139c09ce04e41a6cad36029a464cc326221310098804c11a5b2d29a094824a402520128c2932a499024b89258292a1495024a8124c492414847241851f4c8fa047d023e811e868f21479023a151d008e804721239011c808de346f0237051b808da146d0236051b008d804672a338119c08ca245d422d0d16808b4045a022b8d15448a62451122615128489404481224011184886344302208910408820441021f890fc08726439021b890b5482b84140a069d034081a040d02050d020481004051a001500007fe13fd11faa0fcc47e223ef11f514fa807d213e809f28cf7127b803db09ed04f6807b213d711ea0cf21878e13c701e380f10678423c201df10ef8077823bb09dd80ed0e76423b201d900ec0475a33a259d100e88074403a201d100e65272e239511c988e444716638911c198ded06ee437701bb80ddc06de836f01b780db066c0c36001af84d7c06bc135b19aa1cd5006a2335101a880d44069c334739a380d0c86860341119f0ccd9064ef327019380c94464a0325019280c9406481317698b80c4c86260313018790c3c061e030f018704c24a5fcb2fb197d04be425f012f4217810bb845d822e6317208b78c5b442d8116a10b5005a802d211678cb1d058c12c5096280af5057622b7215a88ad0256612ae29558caa8254e32a419508ca6cc5303297094b80a544524329109470ca380518228b094504a1c650e0285113f1c9f044f23278093c009e004f0027519390c98de4c4126109308097c44b6425b012d8096c04b03258012a8c944849e224d112588914c4862241111f888fc047e023f011f808f06478023c011e008d8c460622e1116848ac444c522509109087c4436421b010c88864043012151906a083024142209090388818240c01fe40fe087e843f211f520f90c7bc63d071e518f20479003c421de20ee8476863b211d808ea8c73cc39c11cb18e504724238e21c038df846f8237821bb08db906d8236821b308d9046c0435461a240d00867c2334519810cb846506326119110c788638231a118a18c2185ed22f4117810bb845d442e4316d28b5885a822d2116808b38458c82c6016300b18058062be115c18ae0056842b2115808ac0056002a8415210a90054042a0014e10a7005380298214728a304514228a014500a10c50802840141089d984ec0276013a089c084d8426c0136009b004cc626601330099804c82262112f1097804b4425a012c0896004b002561127208d3446422320115208a044500224211200888444022200110008708424a1fac0fd007e043f001f610fa087c083e001f000f7087b043cc61e410ed2876803b021d610eb0075043a421d200e808738438c81c220e100700438001bc20de006f0037801b820dc006b1835421a620c2886084304017c30be005e842f4017810b9185c802e0216460b10857882bc015c10ad085490266012c3096004a082484124009200478c23c01126089004404220010e108320418020c01060083003e981f400f62079103c801d860ec0076003b001c0c0e0006f0837801b820d4406a0035001a800d40064302bb412d807cd03e001f000e8807400333819040bc605c102e0017000b4205a002d0016800a48050102708120c08c2046002300100c074602c7016000a840540028101118059800540001
private def c127Edges : Nat := 0x8723705fc8d907f2358a1d25977f49599fd25344a432a21e819883a0645fc01607f004ca1e259e870965dfba5667ee94d80f24b087836721c0d957ee3591fb8d3449e32b00f0c5289802ba2580a8898013225804849a6365fa8d907ea35822480db7ec9599fb253603a92c2238cac49832adfa25667e894d80e24b17e83591fa0d3449032b00e0c5289002ba2300a88900132230049888058222013087a01022101637d464d9f499077d29589f4a53282c664df419627d064c21aa5977ce9599f3a535882059620016088204d220013087e02a21e8040876960df319627cc64c0b400a0488965df2a5667ca94d0fc8ca887402a21c804483a0100f1007282c028a1ae1a086b55c0f0807088786921f61a087955d21c557086e667121999486c65b21a19677c864d9f219060366200f0007889555d222d57286665ba0919677c664d9f19906034620219816c8240595f181347c60410ef807c03400880cb0e03bc63700c9880863250e17a53e03092c6178d3c3ba32b00c0c5082355d202557063e95b0dfa5645a494d80ba4b02dc32a206019085c04c216804085001016899042da01e168a53237a65816819302d80280b5807085004c16799042d801e186a56459c94d0b50ca885604d215013085202a213804484c01021661a484b868208494481f250212199c632665dc1996461c64f185193459a64180b18802d201e211016083e010566256059894c8dd199159665816599302d00280b3807183e05820f813159464d16519042d001e20a2595592959164a5342cc32a6108164816058210813581604c21000a883c01120e8041590959164253602a92c0b28ca983605920d813483402b20c80a8830011186016161804c20b004237402820ae1a082955c20e557482f55c209996c36e659563993458e64180a18802c801e206019060c965dc7a56458a94d0b18ca881c059205816080e02a20755907e726415b8d9159864d16219042c401e20649648172581f93d6073a665182193458664115b01602c201e181a5905849580b00ca02be01c204258159895816099302bc01c203d5987e32661cea59861265a8d7996058064c15a81982ba01c208e1a0821567207d5987e12661cca59c61095b181256457e94d809a4b05683660ae0ca881a067205019881202b20300a857cc5980930e02b66361ff0cd87dd2581caa59456435820000a880465b1ca196457664180898802b401e1cab1985749580ac8ca08000661ff55707db25a1fea56c72895a158816880955c1f6496872095b15ca53602092c1580d682b032a201816c80205a1ff80ac7f802a965199370465815781602ae0281f3196470464d0ab80787ca9651c0a56434e94d1570d602ac32a1fd00a87f20111fc004055a0581f7c9407009590d3253601e92c1560d602aa32a1fb00a87ea01119219345f86410aa00786489588d219305560580a9807058c965191a5645f694d1550d602a432a1f981647e40581f880a855265815381307df55c15ea56464494d80724b054c34c0a88ca87dc04d1f680a87d6f4814d013153404c14d013054a3581f501607d204c1f4004208401c1520d6027432896500a07cc0101f3e1a07cb55c151813026a01c1fbd5747e955c1f83d147d8f441f2196e58e65919099345f46430d0990601a620151013026801e1f0c9806fef58949190152405808080706fcf581f031307bc94c1ee0d3020001c1beb1301fe01c1f03d9371cf581c731906f8c5817c9902522634d7c819152205807f00706f6c4c1ef3d9371af581c6b1906f4c5817c1902520634d7c019152005807e80706f2c4c1ee3d93718f581c631906f0c5817b8d0251e334d7b819151e05807e00407c3570dc5d590716f701bbbd907bec4c1eea5305ec65894719007b634cd7b01c151c06407d807360e0541bb31907a294017999325126341e68d001f401c1eb25005e46341ea01001f201c17898a01f001c1baa5607ac94017818d251062807b80705de3281ba25607a89401770cd250e328dc53d6074af441b9b1607aec4e1eaa5385ea642176990250c63454581607a604e07b00706e495817618d250a62807a80706e2c641e8a5005d664c94218d079834007a00706e09589418ca0748f441b7b1625046341e781386dc9581750cd250232807980406da9581748cd250032807900406d8c641e6a5007986401740d324fe33407880406d695893f00a0746f441b531624fa3341e5013b7135641d155707b32501b4bd907b0c4e1e931307a094e1e725305e865a17399624f86401e58d3879234c54501901e001c1b2499078af581df316076e6580770ca06c72580768ca06c4f580760ca06c29581da8cd01d601c1e2bd106c0c581e2253877a9421de250076c3421da0d001d401c1ac3d601d23281abbd301d03281aaa5301ce01c1e13d14782f441aa313078094206f00706a6f581a9256076633406e80706a294c06e007077cf441a8316077a9421de25007643421d88d001b601c1a43d6068ef4c1dd3d14772f441a3313068af581a2256076663406d004068664c06c804068494c1da990b7603361d800d81b00101a099301ae0101a0256076663406b004067e94cdd78cd875e03606a804067c64c06a00d075c02819e99301a60341d680a067834019d8d0067464c1d70ca075a02819ca5607606341d78cd01a404c1d6010076ef4419c316076c9421da25007646421d8990375634e1d581381a20101983d6065ef4c1d4bd14750f44197313078f2511e3494065af581e1b13877ec4c1dda53877094c1d50d3874e34c0680070658f585460d6019e328195bd60654f58194c99074af581d231607466585468d9019c328d8e8160650c4c066807064ec4c193313064af581d0b13074094c1cf8d3019801c1cf49815992581923d6324e64c938190152a05806580703340581ce013073601018355c074556cdc7d59058d270191c9905c8958937a53024437054a0d901943281ce81c073406c1cc004030200cd83d57063a0081cbe1a057b26419149624dc94c0908d915263580648ca072c0661ca81947280641c981887240611c881814e43580640ca259804c1c431314f604c063807070ec4c53d013018c01c1c331314f204c062804070b2581c7310071a9401c60d014f00580620070714c40061807018401c0608040710c401c3a50070c340060007070af4817199035c604c05f807071f55c1c5bd54712f541c23d345c4642d73016b5ca05853b813017c01c05e80706cf254c90253024035805e0ca37040281c100406cd254c8fa53023e35805d8ca06fcf4803a80706fac401bda5006f234003b00700ee01c1beb1305c2634d70813017401c1bdb1305c0634d70013017201c1bcb1305be334d6f81301700101bf49606f8c401bd25005bc64c1bc0d035bc05805b80706e49341b70cd016c01c05a8070658c381baa5086e804205a007016601c1b924d06da3340590070656c381b8010816201005800406dc9341b698d015e01019530e06d6042194c9406ecc421b9b1006e29421b7a5006d83421b50d0015c01c1afbd3069ec4c19b993015a3281b401306bcf4c1a7313066c64c0560ca01563281b13d306a6c4c1a299301523281b281501503280538ca068632805300706c4c381b0a5086a49361a8a4d06883361a10cd014a01c0520ca01463281ab24d014001c04f807013a01004f0cd06b8934dad18d06b63341ad00d013801c04d8ca013432804b80706ac94204b00706bef451af3d106bac431acb0fc6b0c391abb0e06aa9360468070682328046007011601c1a9b0e06a49361a8a4d068033619f8cd011401c1a624d36946341a58cd06940341a7bd1469cf441a6b10c692c3f1a430e468ec381a098a01120100440040686636d9f0ca867c02a043804010c0101a098a010a010d9e8ca867a02a042004010602819e007010402819d807067831c19d807067c62819e8ca010204019d00d068ac381a224d86849341a018d867e634d9c8d08672042040004066893419998d366433419900d066ef4519b3d1066ac43198b0fc660c39197b0e06cf2511b349406c8f451b1bd106c0c421aa31006a09421a325006703421970d000fe01c03f0ca0658f4c195b13065464c03e8ca00f801c194310064e9401930d000f601c192bd2323c64003d007065325416ea53023435803c8ca064805808c8d300f03281c0d57470155cd91c9476452501bfbd3c6eef4bdb4bd286d2f49196bd20646f451913d105b8642c8c19035b804e08c01300b401cdcce1a77218681f1499f63326618cc99436f2641ed498f7912621e4498474d260dc1c96558f2581ccc9447212501c1bd9a58ef64190bd605a864ec8b99324aa640d6a019822e06452a816009001c18e816063804c18d8040635868183494063004c18480a062e0101864960602f641803d605420641500160624010180bd6853e05a18901305fef5a150816861756617f499853c36618a819862804d189813062201118800405cc6648de80a0618058186e1a0617250172996061202818381805faf58182c9805f8f58c93999053a05818355985f7266172259853836618201986060298d780a053604c14d013053404c14c8d6060206418001605fe01017ebd2323c64c16ea56053035817e016234802817f49405f6f4416e196052e058170a5305b605853301305c094c53281305be94c53201305bcc5817ca5005f064017b8d005b406453181605ea94017618d05d433417898d05de03417898d05de63417925085e064217701085d86341748cd05d46341748cd05e6942176a5005d66421740d085c6c4ed6c81385baf585338d6324e0640e201005c6c4c16c81614c404c16c01005c293417018d05be33416b813323c04c16f31285bac3816b01385b064016ba5305b66340e225005b062816ba4f05b4c54d6cb1305b295816b25305ecf6217a3d845cef601733d645caf581723d105c4c6616e31605aa066530816063f86818f559c63356618b557461f55c187499c615266184494460525017d3d985a866614b019a57d55c15f494008e32881a007008c01c023007008a32816881605a0028167804059d868162bd124ee65802200734e264c02180724e264c02100724ec64c02100724ea9580208ca0588058166013059602816500424e89580200ca059355d164557258cf4595ebd124e664c01f80704da35801f0ca24e495801e8ca058805816080a24e264c01e0070588f5893819904d805801d80724e264c160bd6a4e065a135816858d566162c99a4de9661350d98074328161819858402916000a00726341348d3007032801b98d006c01c15f557057b25a15e49424dc95a1340d6806a32815d8168574029169557259b25b963c96a57f25195cc94059af5b163bd6857ef4515cbd124aa65a12a816804201c54a8d3453a3411360cd4556f5854a996124a34c1358d00554f58091199552865914e19344d464115b816456c05815a8078551258153bd3056755c1533d3024265954999344d0641806188056404d15880784ec358152196424064d490190455e01e554c940552f4408f993523e641805988055a01e48e8d004da65908d193453064115580785532501543d104d264d08c9906014620153807853404c54d01004ec01c152d57054925015749445592505553d1554cf4415530e454cc381518d3c4e634d54b8d0c23034114b8cdd2303358048c50534c4c14db130536c4c14cbd60542064150016053e040c188d30530f58533996053a058492807053605814d013123a01c14cbd10530c3814f4940538f4414bb1614c23588188d614b234c146c9814db25813399914b065814a81314d325852b99604c034c13db1304cc35852f8d304f4c4c1328d614bc34c13cb1304c805852e81304f1258148a5005206401318d914b83581478100518c4c14649414b6340146d57051694052d0d3050a63414080d051064292d8d3050e34214298d05000341418d085026341400cd04fc042144a50850c940142190850464092d0d604fe04213e81004f694013d19004f204013c3d284e4f441310d384e204c53881004ec01c13ac9444e9250536bd154d2f44136b0e44d2c3813881304e2f4c92c8d304e525881719924b0658138019205a65892b99304b234c12c8d304db25801719904b065813601604d601c134bd3005a65812b993206204013318d04ca33413200d04cf250131b1244c4c4112f98a04bc32812e80a04b662812c81634b1251d2bc9414b0f4552bbd104c0c4352e30fd4b4c3e92d30f64b0c3992bb0e04c094f12e252f4b494a12d25244b092d12ba4b052955d149d570524f5b1473d5c514f5613e3d544eef4d139bd304def451373d104d4c3913430e04c235a0160d604ac34c55a557556155c15a3d14560f44151313152c35b08b8d654aa34d14b0d0d22e34112a8cd6010314217d57084725b209496880b2511fdc9407c6f5a190196c5a664f0d0193457064180398804a805a01000783169608b419932ae6588ab99302d00644ab81602ae04c0cd01914a20581288130488c7011d31b134ec640d3b1623f2970cab25922ac9580fc8dc12ac3640ab0d604a403412800c032892c0ce002134cc640d33160300c38caaa5922aa9584aa8d902aa35812700d849a03512600d049603212500c449203012125832a06588a819312a00580a80130338064523016048c04c0b9018048b868122557048294011fa4d047a328120a5913a09580e825323e8664ca7996229e64c0fa019129e0580a7813047e9644e7a56039e94c8f9999329c6588a719303e60644a7016029c04c11e999139c6580e719323e4364ca68d6229a34c0f9019129a0580a68130484c704e6b19039ac58120253047c9408f899c32986648a619604783280f881c12980640a60160470c4c11831004506340be00d04649348f819932966588a599304563280f801912960580a581323de64c0f7813046ec4c11aa4d23dc658ca519303dc0584a501323da64cca499003da04c4a4810146a94c11aa5023d8658ca419322906400f6016129004c0a4010047155c51b313446cc4111a24da3f065a8f5996328e64c8a399003f005a0f5816128e04c0a381023d4658ca3193228c6400f5016128c04c0a301004649408f4999328a6588a299304543280f4819128a0580a2813045e94cca2193128804c118557145c94d11725063ee65a8f4196328664c8a199003ee05a0f4016128604c0a181003280608f38d6328434c8a10d003ce0584a101302840408f30d6328234c8a08d003cc0584a0813028204011599004546348f28d932803588a00d303ca0644a0016028004c113993327e34c49f813045155c513193444c6418fb0d6a3c8358c9f0d3227c3400fb01683c805849f013027c04011d61a0472941119a500462935116a4d045892c8fa999a3c6664c9e996227a64c1148ca844a3280fa81983c606449e816027a04c10f25004343281108cd0444c424e6256039894c0cfa4b327865889e193244064249e016027804c110010843c94c10c8ca033c92c0b900c043464c10c990033a6204e5b190396c580cdb0e044694d10fa53043a94110e250043692cc9d999227665810c0ca842e32849d81902760581020ca042ac42107a4d441c934104a4b040a32a1018ca0426c3910930e04229361010ca041e941107250041092c1008ca840032810624b441692c104b130410c400ff98d040463410224d8404640102990440664010098d44006340ff98803fa6210fe1880428941108250041a93510524d040e92d10324b03fc32a0fd8ca327465889d19302d00280fc18d03ee6280fb007327234c89c8d0327034c89c0d0326e04c89b81003e86400f998d326c35889b0d303e401c0f518a03ce01c0f7a5003da6284f699003da6344f725043dc9350f618a83d46340f300703ce3340f30ca03e06350f598d03d26290f418a03ca01e0f200713943410e50cd43f355c0fa99583e26550f1995139264d0e499043c435a0f08d6326a34c89a8d0049f86912461a048e967121a5983b09650dba590476963112258842c9610fd25813909594d0a56039094d0d0a53032e92d0bd24b23c06668b2199326865889a19303c00660b2019126805809a01302f2f440ef55713b8c5b4dfb16832cc390bc30e32dc95a4b70d682f80348ed00a03b40100ece1a032692c0c381623ae0280eb804137c958c99999326465849981912640580ea00a326065a499816838ac66c97a59925e3660ea819a3a60298e900a03a60110e9004325c64c497013325a64c496813325834c49601303a09400e7a4d32566580e70ca12560580e625003883400e19930394358c950d3039a9620e5a58038e9590e1256032492c8e4999b2526580e481992520580e3c99137c0580e20d3238665a0e1816938b8680e2c940384f580ee61a03b75670ec55983ad55d0e8d5703912660e3259c3829660caa4b432292cc9419992500660d6d57037c04c8de80a037a0100de61a036d2500da816136a04c8dd00a03740100dcd57437155c0da816036b2580c33d9034af58c93999324c658493819124c0588d900a03640100d901303620280d23d6b24a65a493816836d5660d1c99b2489664920d983680660d9813430a04c8d800a635e0280d8004435e0100d6d57034525ac91a56924635a0d6016c35605a0d501363520290d480472409584900d6323e95848f8d6323c64c48f013323a64c48f013323895848e0d6030c0640d281623480280d2004323694c48d8d3034f55d0d35570346f450d13d1323064c48c013037f55c0ddc96c36f25a0d749443512500d0bd6b22e65a48b816b22a95888aa53122a35808a8d3033ec4c0cf310322896488a256033a63448a0d902283580ce00d03340348cc80a03320100c9b1c0336c6c4c93190324c5888b25c3226964889a56022c3704898d902263580c501c033006c0c38160328060c8925612243580c301903275660c9499b2229664888d993100660c8013430a04c0c8316221c9580870d6031c9400c6a4d03183280c5a58130c9580c3253321a658886993121a05808681303132604c34962216640085810321864c486013030cf5ac88196922005a0c555983109660c3a53430a94cc87999a21464c487819821404c4cb61a032f5670cb557132ac674c8b19832ac5b0c8b16b212966884a5692123660848d6931e0674c2019831e05b0c201683040100c080302f80080c061a220e964c82a56220a94c0838d9120a3580828d302fe0660bb81942e20640bf01882fa0610bd81802f355cc84316921065a4ba0d682ef566881a53020634c0bb01982e555c0ba55702e725b0b8c96b20865a48201692f155c0bd496c2f1250c81256a20494e4810d6820434e4ba816d2e005a0ba813c2e004e0add57021092c02399320683400230d0206834002299302da04c0b600a02d601c0b561a02c7250c5f0d600883404210d300843404218d30086340420996008264c0b101612c404c0b400a02ce01c420196008064c0b355742cb55c08b188420e62041f8d3007e340c64196007a64c0b101602bc01c4218d300783400b149602a8f580658d900763400af8d5108634c0af49682a6f5a0658d682c75660a94998244966065199807464c0b081982c001d0ae807007295801b0d002b755c0a8c96824295a08324b019265a01a99302b405a0ac807608435805e8d3024095809d19901786580ab80a023e95805d99600f434c03d0d3023495801f19900f26580aa01602a601c08ca53007065803c19300ea34c09719302723580378d3025a64c09c0d600d834c0960d3026e05803481302569580a7990029c63409b0d900d03580a6807028c6280338d3028401c0a498a02926400330d002949410a418a80ca3400320d0028c6340318d3028201c0a219040c434003081000c00400a10cd028232802f813027e34102f01002966350a398d028a6290a198a00ba34c0a0007827c01c08a98800b834c08a24b027864002d8d6208401c09c8cd027032809b804027525009b0d242543410ab55742ab55c0a93d142a2f440a8196c29865709e9958276655094993423064c089988420a62009a8d6a07e35802d0d3006834081a0d0026234881a0d0006664c099816026404c098007025c63409698a025801c09599582246200950d6825f868094bd602226200190d0023cc4c0188cd0218c4c8188cd023ac4c8188cd0238f580181900220058093813024c0400928070236f580179900234f580171900232f4c016990021805808f010023a01c090494423f25008e3d14236f4408d30e4232c38092557424755c0913d14242f4408c3130058334415996005664c02a193022a94002999602289600892562056664029196021a0640860160224f5801519002200580858100218c4c0148cd021af6408819630a03580140d0021864c0288d30218c4c086bd6821665a0280d6822d566089c998222966027999804e64c087819821c04d085013004c94c412993004a640012253204a6580251930046334084557020f25a083494020af5a024996804464008201682060410803d500eac4c03b31301fe94003ba5001fec58c63b13018e95805d253318cc4c063256017294cc62b13018a95805c2530201264c624960188c6405bb1601fc94007e99001f804005b25601ea63407980d01f063405a99301f0634067b0e016894c07ca5081ee642059993016495807a98d01e4034058993016064c057a5601e66340790cd019d25005731601f494207b25001e86420788108154c4c054bd601d8c4c0778060150f4c053b13014c64c06c80a01d8c38052a5301d664206e98d81b863406d00d81b003404db130134c4004b19001ca32504aa530128940c720d001c8328070804012663404925001c8634048a500120634047a5001c263404731301ca940c718d301c63340710ca01c0010074b0e41d0c38046a5001ce6360730cdc1be33302c8c5409c31404619301ae028045990011494c06e98d81b863406b00d81aa03404499301ae3280440d0010e64006c8cd81a802a0430d0010a64c06b8ca010864006980a81063400410d0010264c06a0ca01a602804025301b463606c18d01ac33606a8cd01a40420773d141daf4403fb1301d494206f25001b664202b8c5409a31406881080fcc4c03ebd6019ec4c03e25000f6c4c066a500198f54421bd300f4c4c067498319125801f3d900f2f580658190070f5803c3d32086040061a500184940060a500180f4c063a4d018c63406280d018693406118d018203406030f0191250062312417ec41056bd2017a01c0563d200ee94003b3d3017493405c98d017003405998a016202803f24b016a63605998a016002805898a016032803ebd1016c93605a24d016463605780d8148c40051b10014ec400558120154018044007014e92c05318d811862a04598a011202a04380a013231c04c18a014401004b98a014233c04f98a013c32804e80a013201004c0cc012e63604a0c64126334048004012662804818a01289340490d001223280478040148c39051b0e014093704e24cc13692d04d24b012c62a03b8cdc0e833304a8cac11c32702b0c54098314043007011862a04598a010a02a04200a010c31c0440ca810601e0430c7010401e0418c7010401c04498a810e6280428ca810832804080d815af450563d10152c3905430e014a936046a4d011463603b0d0c0e433f02a8c5409631404000d80fcc4003e24d00f6c3c03ebd200f404c03ba4d00ecc3c0388cd00dc32803580400e293403a31000e63400380cd00da32803500400e293403830f00dc934036b0f00d693403530f00e4f480378cd00d832803480400c831c03080400cc31e0320ca00c001003080a00c001c0338ca40ca3280318c740c431c02f80480bc01002a0c500a662002e0cd017925105dc9430f2f45c3c3d100eac4305bb0ff15cc3e05730f40fec3c03cb0e40f0c3803a8d3c0d034b02e8d280b63490290c5409431402b31300aaf5802cb1300b004c02b31000a863402abd200a665402881600a2c4c02bc981057258815bd900a4f58c2801600a00400262500096c4c0272500098934025b0f009af54412bd3204ac58025313319555dc64d570202f5b07dbd5f1e0f560783d541a0f54c5f3d3507ef4c0653d14192f4405f316a07ec5802d313009e3150248c5207325001cbd1004c62081a013008c01c022d57007ac3801e01300860400210070083251020494207cc3981c30e00563150128c5007804c01e313007d25a01ebd6805c65a01d816807325001c3d3806ef44016993804862001b013a06804c01a010006755c0150c5005204c8188100062034018494405f25081730e605ac3801724b405a92c014813005234c815c968056f5a015196805005a013494204af4e8123d1004ac4e01230e004604e023c942088f4f81fbd3a074f4581abd10088c4f01fb138074c3901ab0e006434f0160d3804e3150110c502dd55c0b4c96c2c925a0ae49442b125009a3d6825065b08b9968212621081188009035a0108d013bb55c0efc96c3bb2504e0256d34095a0e0253c34094e0c1a4b42de92cc10196a04064e410016804004e407a56401e94d00324b003a02a00f557403955c00d996c028659406993401a6410029880008c3800cc94102e94f001a4b002555c00ad57002555c007496801895a0088168016958005253001f55c0073d1001264c0053d300172504053d10014c384065570018f44004b13002f55c00b496c02925a009c944021250006bd6801065a0035570009250401c94000af4f001bd1103125000d3d3c030f44403993c00e64300118818612502193d3c860f44d29993e4a664380098814a604f129810c03e01f000802000007f
private def c127Links : DagLinks :=
  dagLookupLinks c127Index c127Edges 17 5 13 11 2 6
private def c127Data : Forest := fun i => decodeNode 11 24 0x9c4b00944baaec3301b449009c46195c47009446aae433026444c34c3402c442026c3f02643f01543fc3443400843daaec344b043b015439008c39aae434333c3432dc34aae43532cc3402dc337a78019284317a2001aae25402642d00842dc34c24026c26026426015426026428008c26008426c34424333c2492da5402c422026c1d01541d02641f008c1d00841daaec13026c18015c18015418008c18aae413008416c34414aae41432dc1392d254c34406ab3c06ab3406ab240e033c0692cc0b92c40b033406015c064b0408ab3407015406928a54aae3fc02dbfc32dc0202d3fc033400015bfcaae3fd4adbfd0153fc9282540153f8008bf80083f8aaebe40153f5008bf5aae3e402cbf102c3f10153f17a2be4aae3ed026bed0153ed7a23e47a43eb02c3e80263e80083e8c343e50083e6aae3e532dbe47ad254933b21ab83db7b23e06263db7b23de4a63db7b23dc1a63db931b219283c96273c96273d34a03d64a73d34a03d40273d36263c94a03d14a73c90273cf4a63c94a03cc3203cc1a73c90273ca1a63c9930b21928ba79283a77a23c44a73c46273a77a2bc07a23c04a13c06263a77a23bc4a13bc4a03bc4a73a77a2bb97a23b94a63a77a23ab4a13ab3213b54a03ab31a3b33213ab3203ab31a3ac19a3ac1943ad0143ad0203ac0273ab1a73a77a2ba87a23a81a63a79303217ac3a362c3a332c3a3ab639a62639f4a639f1a639f93039e03839a02639b00839b03639a928b21008398c34391033391032b91032391031391030b91030391928321aae38462038c4a038c1a038c7aab8462038a7aa3846203864a03861a03867a43857a6b847b3321008382aaeb22aae3227a7b2292c37862637d62037862637b4a03786263791a03787a5b2262136a4a137402137462036a49a3724a136a0213704a036a49a36d31a36d1a136a02136b1a036a7a4b22026368928b2e92832e02a3657a2b2e7a232e61c3614a136162132e7a2b557a2355621b5549a35a19a35a01a35a61fb5561cb5561c3554a135649b35562032e61c35149b35149a3514a132e7a2b477a2347621b4749a34a19a34a01a34a61fb4761cb4761c3474a032e61c33949b33931b34349a33931434131b33931a33931433a19433a18e33b00e33b01a33a0213391a132e7a2b2f7a232f621b2f49a33231a33201a33261fb2f61cb2f61c32f1a032e7a43227a632a62632a32632a92a3246203264a03261a03267a432502c3247a2b227a23227ac32132da54c342d4ab3ad402c31b02631b00831bc3431aab32d4026317008317aaead4033310026b10026310026312008b10008310aae2d4933ad4c3430b02c30c92830b9332d4014309928ad4030307ab3303930305033303014b039282d40322ff02c2ff0082ff9282fb7a42fd02c2fc7a22fb7b32d44a02f73202f71a02f77b12d54a02f57b0ad54a12e84a12ee31a2f13212ee31a2ef0212ee4a02e831a2ec3212e831a2e919a2e91a12e87b02d57acad57ac2d57a22d56262e36332d549a2df31a2df19a2df6252dd61c2dd62c2d531a2db62a2d64ac2d63142d849e2d74a62d60332d53332d4327a54aae2b902c2cf0142cf0082cfc342ce7adab90262ca0142ca0082caaaeac8aae2c87ad2b9ab32c09332c07ac2c40332c0014ac07ad2c10142c07a2ab9aae2ba92d2ba9282ba02d2ba014aba7a22b9320a5402cab502c2b500f2b57a2a55aae2b1026ab100f2b17a225500f2af928aa300f2ad9282a300f2ab61caa39282a77a22a700f2a761c2a3aae2a49282a41a7aa362625503229f02c29f02029f92829702c29d7a229702c29a02629a7a229861c29862c2971a1a55026295aaea56aae2567ada564a028f32028f02028f7aba56aae28b92828c4a028b7ab2564a127d3212871a12874a027d31a28532127d1a128332027d31a28019a28002127d02127e02027d7aaa564a02793202790202797a52787a6a5600e276928a749282747a625692c2707a62710322707a2a567a225692c26b02c26b00e26b61ca567a626961c25692826231a26419a26401a264624a62620a621ad2564a7a5731425d19425d01425d4a5a5731425b4a4a5702c259496a574962571a625619aa5502d25402180101a250026251018250c349e001b24901aa4901a249019249018a49018249c341e04b39e0026246c34244aae2444b31e063823c4b22414a623c4b223f4a023c33223d19423c4b19e0c342254a0a25aae234626237620a344a023549b2344a02254a023249aa25aae22e4a622f4a0a2e49a22549622532022a31a22a195225aae226326227320a261942254b11e04a6a1762122019a2210212204a62174a621e4a0a174a02174962173262193202191952171942174b09e06212154a09fb61ca1161c21149b2114a01fb4a0a0e4a020e49a9fb496a0b49620b49a1fb6262086202084969fb4961fb3209ff49b2043201ff32020231a9ff31a1ff3101ff1951fb3109fc3101fc1941fb4b01e0aae1e131a1f63141f600e1f632b1e13201f231a1f200e1f232a9e131a9e44a01ef49a9ec31a1ed3151ec31a1e431a1ea3149e43141e419a1e61941e600f1e400e1e432a1e11ad1e11ac1e10331e092d820aae1de928020c341c1ab39c10081dac341d9ab31c10081d7aae9c10331d20141d40089d20081d2aae1c14a01ce49a1ce1941ce4b11c94a01cc4b01c91ac1ca0331c99331c19321c74b39c19281c21a61c402d1c37ac1c24b31c14a7820aae1a10261bd0081bdc341bc92d9a10081baaae9b8aae1b892d1a1ab31af92c1b50331af0269af0261b10141b10089af0081af9289a1aae1a902d9a902d1a90269a90089a99281a1aae9a2aae1a202c1a40081a47a29a27a21a27ad1a14a702062619c62019c31a19c01a19c63619801a199008199036198ab3984aae18462d984030194ab319293319262d18462c19002d9844a018c49a18c19418c4b018bab31859301894b31854a69857ad1864a618502d184496820008181006181c3417b03317b03117b03097b00417c03017b92d970aae179928170ab3176033176027970aae17192d971aae17292d171027170496020aae02102616b01416b00e16bc3416a92d82101416700e167aae965aae16592d021ab315d92c16203315d00e95d1aa15f92d15e00e15d928821aae15902d15900e959928021014157aae935aae13502c15300e1537a29357a213532d93532014d31a14d00e14d32b93531a93e4a094832014931514831a13e31a14631493e32094431413e19a14119414100f13e1a093f00e13e32b13532013c32a93592813619a1371941370081371a49361ad1357ad02102c1300261301a413100e130c3412931a12c31412c00e12c32b12a1ad12a7ac12932d82102612502012500e125aae918aae1187a29187a211892891992811902011d00e11d7a29197a211961c91961c11962611832d021ab310a4a01154b011493310a7ac1124b310a32c11003310a02690a7ad10b62610c32d10b02610a310821aae10392d1039281037ad10302d1030209033100217ad8499320fc62c0ff4a00fc3200fc0200fc7ab8494a10f14a10f731a0f83210f74a00f131a0f53210f131a0f219a0f20210f17aa84900c0ef7a28d17a20d161c0eb3210eb4a10d161c8df61c0df31b0df19b8df4a00e031a0e419a0e01940e031a0e10080e01998df4a00d131b0dc31a0dc3210d131b0d219b0d931a0d21940d719b0d219a0d21940d30140d30210d20210d17aa0496260cf9300cb4a00cd7aa0cc0320cb7a28497a20499280bf49a0c531a0c501a0c56248bf49a0c131a0c101a0c161e0c06208bf62d04900e0bd92885b92805b49a0b831a0b801a0b861f85b49b0af31b0b549a0af3140b331b0af3140b01940b001b0af61e85b7a28807a20800240aa00c0aa61c88061c0804960a631b0a649b08061c88e61c08e0080a219e0a149b88e31409d19409d01409d49988e49688e49608e00809919809831b09731508e19588e49a08f3140931a008f19408f31409000808f19388e49a08031508b31408b31b08031508119508831408118e08619508119408118e08200e08201b08101b08061e05b62007e7a407a49a07c61e07b02607a61c85b61c05b49a07761e0761a785b6200731a00737a406949a07161e07019a06949a06e61e06d19406949a06b61e06a0080691a585b19485e18f06619405e19406418e85e18e05e01406000e06000905e00805e1a505b19a05c1a485b6260496260580260589300506200567a405331a05432a0537ac05062605102005018a8494a004e7aa04a49a04c61e04b62604a18a0491ad02192802200e046aae04562782202004200e04292884092804062702292d03b7ad03b62603c02d03b61c8229280367a70367a203602703661c022020034aae0331a782201a03192882d92802d49682d49602d1a70227ad02832d0281a602902d02818a82292802362702361c02302702318a0221a002102702000f801aae81b01501daae01b32d81b7a78029280197a2002aae00892d808aae01592d008928808aae01102d011928008aae00e7a200e7ad0087a200992800a61c00a62600932d008321802aae0067a78039280047a200331000200400103f800 i
private def c127Sample : DagSample := (0x2018040600c1801860049800c60019808050101403050061401250031400650200c040300c0c01830048c00c30018c08048101203048061201248031200648200a040280c0a01828048a00c28018a080441011030440611012440311006442009040240c0901824048900c240189080141005030140605012140305006142010840420c1081842049080c420190880221008830220608812220308806222004840120c0481812048480c1201848800a10028300a06028120a03028060a2010440410c1041841049040c410190480211008430210608412210308406212004440110c0441811048440c11018448005100143005060141205030140605, 112)
private def c127Tags := dagTraceTags b127.1 112
  (dagTagBases stock127 0xfffc07f01fc000fe00000fe00000fe03f80fe03f8001fc00001fc00001fff80000007f0003f800003f80000007ffe00000000007f0000000000000001fffff0000000000007f00000000000000fffffff0000000000000000000000000000fffffff 0x8102040810204081020408102040408102040810204081020408102020408102040810204081020408103870e1c3870e1c3870e1c3870e1c142850a142850a142850a142850a060c183060c183060c183060c1830a142850a142850a142850a14285 112) 12 c127Data
private def c127States := dagTrace b127.1 stock127 12 c127Data
private def c127MoveCert : List (DagMoveRecord 128) := [
  ([([(0xffffffff0000000000000000ffffffff, 0), (0xffffffff00000000, 32)], [(0xffffffff0000000000000000, 32)])], rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c03e78e9c3668c982e58a9426488901e3868c16284880e182840608080, rowSelectPacked 0xfffbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c03e78e9c3668c982e58a9426488901e3868c16284880e182840608080),
  ([([(0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0x50505050505050505050505050505050, 3)])], rowSelectPacked 0xffefef9fdebe78efcfaf1edcba70dfaf6e9ddab668cf8f2e1cd8b260bf6eed9bd6ae58af4ead1ad4aa509f2e6c99d2a6488f0e2c18d0a2407eedeb97ce9e386ecdab16cc9a305ead6a95ca96284e8d2a14c892203e6ce993c68e182e4ca912c48a101e2c6891c286080e0c2810c08200, rowSelectPacked 0xffefef9fdebe78efcfaf1edcba70dfaf6e9ddab668cf8f2e1cd8b260bf6eed9bd6ae58af4ead1ad4aa509f2e6c99d2a6488f0e2c18d0a2407eedeb97ce9e386ecdab16cc9a305ead6a95ca96284e8d2a14c892203e6ce993c68e182e4ca912c48a101e2c6891c286080e0c2810c08200),
  ([([(0xa5a5a5a50000000000000000a5a5a5a5, 0), (0xa0a0a0a00000000000000000a0a0a0a, 3), (0x5050505000000000, 29), (0xa5a5a5a500000000, 32), (0xa0a0a0a00000000, 35)], [(0x505050500000000000000000, 35), (0xa5a5a5a50000000000000000, 32), (0xa0a0a0a0000000000000000, 29), (0x50505050000000000000000050505050, 3)])], rowSelectPacked 0xffefef9fdebe78efcfaf1edcba70dfaf6e9ddab668cf8f2e1cd8b2607eedeb97ce9e386ecdab16cc9a305ead6a95ca96284e8d2a14c89220bf6eed9bd6ae58af4ead1ad4aa509f2e6c99d2a6488f0e2c18d0a2403e6ce993c68e182e4ca912c48a101e2c6891c286080e0c2810c08200, rowSelectPacked 0xffefef9fdebe78efcfaf1edcba70dfaf6e9ddab668cf8f2e1cd8b2607eedeb97ce9e386ecdab16cc9a305ead6a95ca96284e8d2a14c89220bf6eed9bd6ae58af4ead1ad4aa509f2e6c99d2a6488f0e2c18d0a2403e6ce993c68e182e4ca912c48a101e2c6891c286080e0c2810c08200)]
private def c127Moves := dagMoves c127MoveCert

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Autos : DagMovesOK b127.1 b127.2.2.2 128 c127Moves :=
  dagMovesOfCheck (by decide +kernel)

private def c127Check := dagCheckNode b127.1 b127.2.2.2 none (dagKnownCloses b127.2.2.2 cuts127) 1101
  c127States c127Moves c127Links c127Sample c127Tags

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Roots :
    dagCheckRoots b127.1 b127.2.2.2 none (dagKnownCloses b127.2.2.2 cuts127) []
      (dagRef 1101 c127States c127Moves c127Links 0) stock127 12 = true := by
  decide +kernel

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block0 : treeBlock 0 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block8 : treeBlock 8 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block16 : treeBlock 16 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block24 : treeBlock 24 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block32 : treeBlock 32 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block40 : treeBlock 40 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block48 : treeBlock 48 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block56 : treeBlock 56 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block64 : treeBlock 64 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block72 : treeBlock 72 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block80 : treeBlock 80 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block88 : treeBlock 88 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block96 : treeBlock 96 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block104 : treeBlock 104 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block112 : treeBlock 112 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block120 : treeBlock 120 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block128 : treeBlock 128 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block136 : treeBlock 136 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block144 : treeBlock 144 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block152 : treeBlock 152 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block160 : treeBlock 160 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block168 : treeBlock 168 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block176 : treeBlock 176 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block184 : treeBlock 184 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block192 : treeBlock 192 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block200 : treeBlock 200 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block208 : treeBlock 208 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block216 : treeBlock 216 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block224 : treeBlock 224 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block232 : treeBlock 232 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block240 : treeBlock 240 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block248 : treeBlock 248 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block256 : treeBlock 256 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block264 : treeBlock 264 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block272 : treeBlock 272 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block280 : treeBlock 280 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block288 : treeBlock 288 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block296 : treeBlock 296 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block304 : treeBlock 304 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block312 : treeBlock 312 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block320 : treeBlock 320 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block328 : treeBlock 328 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block336 : treeBlock 336 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block344 : treeBlock 344 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block352 : treeBlock 352 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block360 : treeBlock 360 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block368 : treeBlock 368 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block376 : treeBlock 376 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block384 : treeBlock 384 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block392 : treeBlock 392 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block400 : treeBlock 400 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block408 : treeBlock 408 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block416 : treeBlock 416 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block424 : treeBlock 424 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block432 : treeBlock 432 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block440 : treeBlock 440 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block448 : treeBlock 448 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block456 : treeBlock 456 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block464 : treeBlock 464 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block472 : treeBlock 472 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block480 : treeBlock 480 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block488 : treeBlock 488 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block496 : treeBlock 496 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block504 : treeBlock 504 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block512 : treeBlock 512 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block520 : treeBlock 520 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block528 : treeBlock 528 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block536 : treeBlock 536 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block544 : treeBlock 544 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block552 : treeBlock 552 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block560 : treeBlock 560 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block568 : treeBlock 568 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block576 : treeBlock 576 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block584 : treeBlock 584 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block592 : treeBlock 592 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block600 : treeBlock 600 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block608 : treeBlock 608 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block616 : treeBlock 616 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block624 : treeBlock 624 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block632 : treeBlock 632 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block640 : treeBlock 640 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block648 : treeBlock 648 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block656 : treeBlock 656 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block664 : treeBlock 664 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block672 : treeBlock 672 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block680 : treeBlock 680 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block688 : treeBlock 688 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block696 : treeBlock 696 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block704 : treeBlock 704 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block712 : treeBlock 712 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block720 : treeBlock 720 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block728 : treeBlock 728 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block736 : treeBlock 736 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block744 : treeBlock 744 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block752 : treeBlock 752 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block760 : treeBlock 760 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block768 : treeBlock 768 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block776 : treeBlock 776 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block784 : treeBlock 784 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block792 : treeBlock 792 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block800 : treeBlock 800 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block808 : treeBlock 808 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block816 : treeBlock 816 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block824 : treeBlock 824 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block832 : treeBlock 832 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block840 : treeBlock 840 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block848 : treeBlock 848 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block856 : treeBlock 856 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block864 : treeBlock 864 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block872 : treeBlock 872 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block880 : treeBlock 880 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block888 : treeBlock 888 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block896 : treeBlock 896 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block904 : treeBlock 904 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block912 : treeBlock 912 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block920 : treeBlock 920 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block928 : treeBlock 928 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block936 : treeBlock 936 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block944 : treeBlock 944 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block952 : treeBlock 952 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block960 : treeBlock 960 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block968 : treeBlock 968 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block976 : treeBlock 976 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block984 : treeBlock 984 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block992 : treeBlock 992 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block1000 : treeBlock 1000 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block1008 : treeBlock 1008 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block1016 : treeBlock 1016 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block1024 : treeBlock 1024 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block1032 : treeBlock 1032 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block1040 : treeBlock 1040 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block1048 : treeBlock 1048 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block1056 : treeBlock 1056 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block1064 : treeBlock 1064 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block1072 : treeBlock 1072 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block1080 : treeBlock 1080 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block1088 : treeBlock 1088 8 c127Check = true := by decide +kernel
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
private theorem c127Block1096 : treeBlock 1096 5 c127Check = true := by decide +kernel

private theorem c127Checked : treeBlock 0 1101 c127Check = true :=
  (@treeBlock_merge 0 552 549 c127Check
    (@treeBlock_merge 0 272 280 c127Check
    (@treeBlock_merge 0 136 136 c127Check
    (@treeBlock_merge 0 64 72 c127Check
    (@treeBlock_merge 0 32 32 c127Check
    (@treeBlock_merge 0 16 16 c127Check
    (@treeBlock_merge 0 8 8 c127Check
    c127Block0
    c127Block8)
    (@treeBlock_merge 16 8 8 c127Check
    c127Block16
    c127Block24))
    (@treeBlock_merge 32 16 16 c127Check
    (@treeBlock_merge 32 8 8 c127Check
    c127Block32
    c127Block40)
    (@treeBlock_merge 48 8 8 c127Check
    c127Block48
    c127Block56)))
    (@treeBlock_merge 64 32 40 c127Check
    (@treeBlock_merge 64 16 16 c127Check
    (@treeBlock_merge 64 8 8 c127Check
    c127Block64
    c127Block72)
    (@treeBlock_merge 80 8 8 c127Check
    c127Block80
    c127Block88))
    (@treeBlock_merge 96 16 24 c127Check
    (@treeBlock_merge 96 8 8 c127Check
    c127Block96
    c127Block104)
    (@treeBlock_merge 112 8 16 c127Check
    c127Block112
    (@treeBlock_merge 120 8 8 c127Check
    c127Block120
    c127Block128)))))
    (@treeBlock_merge 136 64 72 c127Check
    (@treeBlock_merge 136 32 32 c127Check
    (@treeBlock_merge 136 16 16 c127Check
    (@treeBlock_merge 136 8 8 c127Check
    c127Block136
    c127Block144)
    (@treeBlock_merge 152 8 8 c127Check
    c127Block152
    c127Block160))
    (@treeBlock_merge 168 16 16 c127Check
    (@treeBlock_merge 168 8 8 c127Check
    c127Block168
    c127Block176)
    (@treeBlock_merge 184 8 8 c127Check
    c127Block184
    c127Block192)))
    (@treeBlock_merge 200 32 40 c127Check
    (@treeBlock_merge 200 16 16 c127Check
    (@treeBlock_merge 200 8 8 c127Check
    c127Block200
    c127Block208)
    (@treeBlock_merge 216 8 8 c127Check
    c127Block216
    c127Block224))
    (@treeBlock_merge 232 16 24 c127Check
    (@treeBlock_merge 232 8 8 c127Check
    c127Block232
    c127Block240)
    (@treeBlock_merge 248 8 16 c127Check
    c127Block248
    (@treeBlock_merge 256 8 8 c127Check
    c127Block256
    c127Block264))))))
    (@treeBlock_merge 272 136 144 c127Check
    (@treeBlock_merge 272 64 72 c127Check
    (@treeBlock_merge 272 32 32 c127Check
    (@treeBlock_merge 272 16 16 c127Check
    (@treeBlock_merge 272 8 8 c127Check
    c127Block272
    c127Block280)
    (@treeBlock_merge 288 8 8 c127Check
    c127Block288
    c127Block296))
    (@treeBlock_merge 304 16 16 c127Check
    (@treeBlock_merge 304 8 8 c127Check
    c127Block304
    c127Block312)
    (@treeBlock_merge 320 8 8 c127Check
    c127Block320
    c127Block328)))
    (@treeBlock_merge 336 32 40 c127Check
    (@treeBlock_merge 336 16 16 c127Check
    (@treeBlock_merge 336 8 8 c127Check
    c127Block336
    c127Block344)
    (@treeBlock_merge 352 8 8 c127Check
    c127Block352
    c127Block360))
    (@treeBlock_merge 368 16 24 c127Check
    (@treeBlock_merge 368 8 8 c127Check
    c127Block368
    c127Block376)
    (@treeBlock_merge 384 8 16 c127Check
    c127Block384
    (@treeBlock_merge 392 8 8 c127Check
    c127Block392
    c127Block400)))))
    (@treeBlock_merge 408 72 72 c127Check
    (@treeBlock_merge 408 32 40 c127Check
    (@treeBlock_merge 408 16 16 c127Check
    (@treeBlock_merge 408 8 8 c127Check
    c127Block408
    c127Block416)
    (@treeBlock_merge 424 8 8 c127Check
    c127Block424
    c127Block432))
    (@treeBlock_merge 440 16 24 c127Check
    (@treeBlock_merge 440 8 8 c127Check
    c127Block440
    c127Block448)
    (@treeBlock_merge 456 8 16 c127Check
    c127Block456
    (@treeBlock_merge 464 8 8 c127Check
    c127Block464
    c127Block472))))
    (@treeBlock_merge 480 32 40 c127Check
    (@treeBlock_merge 480 16 16 c127Check
    (@treeBlock_merge 480 8 8 c127Check
    c127Block480
    c127Block488)
    (@treeBlock_merge 496 8 8 c127Check
    c127Block496
    c127Block504))
    (@treeBlock_merge 512 16 24 c127Check
    (@treeBlock_merge 512 8 8 c127Check
    c127Block512
    c127Block520)
    (@treeBlock_merge 528 8 16 c127Check
    c127Block528
    (@treeBlock_merge 536 8 8 c127Check
    c127Block536
    c127Block544)))))))
    (@treeBlock_merge 552 272 277 c127Check
    (@treeBlock_merge 552 136 136 c127Check
    (@treeBlock_merge 552 64 72 c127Check
    (@treeBlock_merge 552 32 32 c127Check
    (@treeBlock_merge 552 16 16 c127Check
    (@treeBlock_merge 552 8 8 c127Check
    c127Block552
    c127Block560)
    (@treeBlock_merge 568 8 8 c127Check
    c127Block568
    c127Block576))
    (@treeBlock_merge 584 16 16 c127Check
    (@treeBlock_merge 584 8 8 c127Check
    c127Block584
    c127Block592)
    (@treeBlock_merge 600 8 8 c127Check
    c127Block600
    c127Block608)))
    (@treeBlock_merge 616 32 40 c127Check
    (@treeBlock_merge 616 16 16 c127Check
    (@treeBlock_merge 616 8 8 c127Check
    c127Block616
    c127Block624)
    (@treeBlock_merge 632 8 8 c127Check
    c127Block632
    c127Block640))
    (@treeBlock_merge 648 16 24 c127Check
    (@treeBlock_merge 648 8 8 c127Check
    c127Block648
    c127Block656)
    (@treeBlock_merge 664 8 16 c127Check
    c127Block664
    (@treeBlock_merge 672 8 8 c127Check
    c127Block672
    c127Block680)))))
    (@treeBlock_merge 688 64 72 c127Check
    (@treeBlock_merge 688 32 32 c127Check
    (@treeBlock_merge 688 16 16 c127Check
    (@treeBlock_merge 688 8 8 c127Check
    c127Block688
    c127Block696)
    (@treeBlock_merge 704 8 8 c127Check
    c127Block704
    c127Block712))
    (@treeBlock_merge 720 16 16 c127Check
    (@treeBlock_merge 720 8 8 c127Check
    c127Block720
    c127Block728)
    (@treeBlock_merge 736 8 8 c127Check
    c127Block736
    c127Block744)))
    (@treeBlock_merge 752 32 40 c127Check
    (@treeBlock_merge 752 16 16 c127Check
    (@treeBlock_merge 752 8 8 c127Check
    c127Block752
    c127Block760)
    (@treeBlock_merge 768 8 8 c127Check
    c127Block768
    c127Block776))
    (@treeBlock_merge 784 16 24 c127Check
    (@treeBlock_merge 784 8 8 c127Check
    c127Block784
    c127Block792)
    (@treeBlock_merge 800 8 16 c127Check
    c127Block800
    (@treeBlock_merge 808 8 8 c127Check
    c127Block808
    c127Block816))))))
    (@treeBlock_merge 824 136 141 c127Check
    (@treeBlock_merge 824 64 72 c127Check
    (@treeBlock_merge 824 32 32 c127Check
    (@treeBlock_merge 824 16 16 c127Check
    (@treeBlock_merge 824 8 8 c127Check
    c127Block824
    c127Block832)
    (@treeBlock_merge 840 8 8 c127Check
    c127Block840
    c127Block848))
    (@treeBlock_merge 856 16 16 c127Check
    (@treeBlock_merge 856 8 8 c127Check
    c127Block856
    c127Block864)
    (@treeBlock_merge 872 8 8 c127Check
    c127Block872
    c127Block880)))
    (@treeBlock_merge 888 32 40 c127Check
    (@treeBlock_merge 888 16 16 c127Check
    (@treeBlock_merge 888 8 8 c127Check
    c127Block888
    c127Block896)
    (@treeBlock_merge 904 8 8 c127Check
    c127Block904
    c127Block912))
    (@treeBlock_merge 920 16 24 c127Check
    (@treeBlock_merge 920 8 8 c127Check
    c127Block920
    c127Block928)
    (@treeBlock_merge 936 8 16 c127Check
    c127Block936
    (@treeBlock_merge 944 8 8 c127Check
    c127Block944
    c127Block952)))))
    (@treeBlock_merge 960 72 69 c127Check
    (@treeBlock_merge 960 32 40 c127Check
    (@treeBlock_merge 960 16 16 c127Check
    (@treeBlock_merge 960 8 8 c127Check
    c127Block960
    c127Block968)
    (@treeBlock_merge 976 8 8 c127Check
    c127Block976
    c127Block984))
    (@treeBlock_merge 992 16 24 c127Check
    (@treeBlock_merge 992 8 8 c127Check
    c127Block992
    c127Block1000)
    (@treeBlock_merge 1008 8 16 c127Check
    c127Block1008
    (@treeBlock_merge 1016 8 8 c127Check
    c127Block1016
    c127Block1024))))
    (@treeBlock_merge 1032 32 37 c127Check
    (@treeBlock_merge 1032 16 16 c127Check
    (@treeBlock_merge 1032 8 8 c127Check
    c127Block1032
    c127Block1040)
    (@treeBlock_merge 1048 8 8 c127Check
    c127Block1048
    c127Block1056))
    (@treeBlock_merge 1064 16 21 c127Check
    (@treeBlock_merge 1064 8 8 c127Check
    c127Block1064
    c127Block1072)
    (@treeBlock_merge 1080 8 13 c127Check
    c127Block1080
    (@treeBlock_merge 1088 8 5 c127Check
    c127Block1088
    c127Block1096))))))))

private theorem lower127 : Lower b127.1 stock127 b127.2.2.2 13 := by
  exact lowerDag (width := 128) (chart := none)
    (by unfold Masked; decide +kernel) (by unfold Masked; decide +kernel)
    (by unfold properWord; decide +kernel) (by simp) c127Autos
    (by unfold Masked; decide +kernel) (by decide +kernel) (by decide +kernel)
    (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) lower126) lower123) lower95) lower63) lower125) lower119) lower111) (by decide +kernel)
    c127Roots c127Checked


open PEqualNP.CircuitLowerBounds

def endpoints : List ℕ := [0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6]

def graph (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < endpoints.length / 2, (List.ofFn x).getD (endpoints.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (endpoints.getD (2 * i + 1) 0) false = true)

def upper : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 2]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [7, 2]⟩,
    ⟨.or, [3, 9]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [5, 6]⟩,
    ⟨.or, [1, 14]⟩, ⟨.or, [9, 14]⟩, ⟨.and, [11, 15]⟩, ⟨.and, [13, 16]⟩,
    ⟨.or, [17, 18]⟩], 19⟩

theorem upper_legal :
    ∀ g ∈ upper.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g h
  simp only [upper, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_correct : ∀ x, upper.eval (List.ofFn x) = graph x := by
  decide +kernel

private theorem lowerAll (s : ℕ) (h : PEqualNP.MetaComplexity.HasCircuitSize 7 graph s) : 13 ≤ s := by
  let raw : List (BitVec 128) :=
    [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc,
      0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00,
      0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000,
      0xffffffffffffffff0000000000000000]
  let target : BitVec 128 := 0xfffffffffffffffefffffffefefeeca0
  have bounded : Lower (fullMask 128) (raw.map BitVec.toNat) target.toNat 13 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) lower127
  exact hcsLower (n := 7) raw target 13 graph (by decide +kernel) (by decide +kernel) bounded s h

end PEqualNP.Outside.L_meta_10576_aux

open PEqualNP.Outside.L_meta_10576_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_10576 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates out legal _ computes
  have fan : PEqualNP.MetaComplexity.FanInTwo ⟨gates, out⟩ := by
    intro g hg
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using legal g hg
  have h : PEqualNP.MetaComplexity.HasCircuitSize 7 graph gates.length :=
    ⟨⟨gates, out⟩, fan, le_rfl, computes⟩
  exact ⟨upper.gates, upper.output, upper_legal,
    le_trans (show upper.gates.length ≤ 13 by decide) (lowerAll _ h), upper_correct⟩
