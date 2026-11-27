import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12056_aux

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

def fa000a000a000a00Mask : Word := 0xa000a000a000a00
def fa000a000a000a00Goal : Word := 0xa00080008000000
def fa000a000a000a00Stock : List Word := [0x800080008000800, 0xa0000000a000000, 0xa000a0000000000]
def fa000a000a000a00Cuts : List Bound := []
def fa000a000a000a00Fact : Bound := (fa000a000a000a00Mask, fa000a000a000a00Stock, 4, fa000a000a000a00Goal)
def fa000a000a000a00Witness : List Witness := [(0x800080008000800, 27, 25), (0xa0000000a000000, 27, 11), (0xa000a0000000000, 43, 11)]
def fa000a000a000a00Forest : Forest := fun i => decodeNode 1 4 0xe i
def fa000a000a000a00States := dagTrace fa000a000a000a00Mask fa000a000a000a00Stock 3 fa000a000a000a00Forest
def fa000a000a000a00Links : DagLinks := dagLookupLinks 0x9 0x7 2 1 3 1 0 2
def fa000a000a000a00Moves := dagMoves ([] : List (DagMoveRecord 64))
def fa000a000a000a00Check := dagCheckNode fa000a000a000a00Mask fa000a000a000a00Goal none (dagKnownCloses fa000a000a000a00Goal fa000a000a000a00Cuts) 1 fa000a000a000a00States fa000a000a000a00Moves fa000a000a000a00Links (0,0) (fun _ => [])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fa000a000a000a00Roots : dagCheckRoots fa000a000a000a00Mask fa000a000a000a00Goal none (dagKnownCloses fa000a000a000a00Goal fa000a000a000a00Cuts) fa000a000a000a00Witness
    (dagRef 1 fa000a000a000a00States fa000a000a000a00Moves fa000a000a000a00Links 0) fa000a000a000a00Stock 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fa000a000a000a00B0 : treeBlock 0 1 fa000a000a000a00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fa000a000a000a00All : treeBlock 0 1 fa000a000a000a00Check = true := fa000a000a000a00B0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fa000a000a000a00Known : Known fa000a000a000a00Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fa000a000a000a00Lower : Lower fa000a000a000a00Mask fa000a000a000a00Stock fa000a000a000a00Goal 4 := by
  have autos : DagMovesOK fa000a000a000a00Mask fa000a000a000a00Goal 64 fa000a000a000a00Moves := dagMovesOfCheck (by decide +kernel)
  apply lowerDag _ _ _ _ autos _ _ _ fa000a000a000a00Known _ fa000a000a000a00Roots fa000a000a000a00All
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · intro c hc; cases hc
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp [fa000a000a000a00Cuts]

def fc000c000c000c00Mask : Word := 0xc000c000c000c00
def fc000c000c000c00Goal : Word := 0xc00080008000000
def fc000c000c000c00Stock : List Word := [0x800080008000800, 0xc0000000c000000, 0xc000c0000000000]
def fc000c000c000c00Fact : Bound := (fc000c000c000c00Mask, fc000c000c000c00Stock, 4, fc000c000c000c00Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fc000c000c000c00Lower : Lower fc000c000c000c00Mask fc000c000c000c00Stock fc000c000c000c00Goal 4 :=
  dagShiftLower (width := 64) [([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])] fa000a000a000a00Lower (by decide +kernel)
def ff0000000f000000Mask : Word := 0xf0000000f000000
def ff0000000f000000Goal : Word := 0xe00000008000000
def ff0000000f000000Stock : List Word := [0xa0000000a000000, 0xc0000000c000000, 0xf00000000000000]
def ff0000000f000000Cuts : List Bound := []
def ff0000000f000000Fact : Bound := (ff0000000f000000Mask, ff0000000f000000Stock, 4, ff0000000f000000Goal)
def ff0000000f000000Witness : List Witness := [(0xa0000000a000000, 27, 26), (0xc0000000c000000, 27, 25), (0xf00000000000000, 57, 25)]
def ff0000000f000000Forest : Forest := fun i => decodeNode 1 4 0xe i
def ff0000000f000000States := dagTrace ff0000000f000000Mask ff0000000f000000Stock 3 ff0000000f000000Forest
def ff0000000f000000Links : DagLinks := dagLookupLinks 0x9 0x7 2 1 3 1 0 2
def ff0000000f000000Moves := dagMoves ([] : List (DagMoveRecord 64))
def ff0000000f000000Check := dagCheckNode ff0000000f000000Mask ff0000000f000000Goal none (dagKnownCloses ff0000000f000000Goal ff0000000f000000Cuts) 1 ff0000000f000000States ff0000000f000000Moves ff0000000f000000Links (0,0) (fun _ => [])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff0000000f000000Roots : dagCheckRoots ff0000000f000000Mask ff0000000f000000Goal none (dagKnownCloses ff0000000f000000Goal ff0000000f000000Cuts) ff0000000f000000Witness
    (dagRef 1 ff0000000f000000States ff0000000f000000Moves ff0000000f000000Links 0) ff0000000f000000Stock 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff0000000f000000B0 : treeBlock 0 1 ff0000000f000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff0000000f000000All : treeBlock 0 1 ff0000000f000000Check = true := ff0000000f000000B0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff0000000f000000Known : Known ff0000000f000000Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff0000000f000000Lower : Lower ff0000000f000000Mask ff0000000f000000Stock ff0000000f000000Goal 4 := by
  have autos : DagMovesOK ff0000000f000000Mask ff0000000f000000Goal 64 ff0000000f000000Moves := dagMovesOfCheck (by decide +kernel)
  apply lowerDag _ _ _ _ autos _ _ _ ff0000000f000000Known _ ff0000000f000000Roots ff0000000f000000All
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · intro c hc; cases hc
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp [ff0000000f000000Cuts]

def ff000f0000000000Mask : Word := 0xf000f0000000000
def ff000f0000000000Goal : Word := 0xe00080000000000
def ff000f0000000000Stock : List Word := [0xa000a0000000000, 0xc000c0000000000, 0xf00000000000000]
def ff000f0000000000Fact : Bound := (ff000f0000000000Mask, ff000f0000000000Stock, 4, ff000f0000000000Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff000f0000000000Lower : Lower ff000f0000000000Mask ff000f0000000000Stock ff000f0000000000Goal 4 :=
  dagShiftLower (width := 64) [([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])] ff0000000f000000Lower (by decide +kernel)
def ff000f000f000f00Mask : Word := 0xf000f000f000f00
def ff000f000f000f00Goal : Word := 0xe00080008000000
def ff000f000f000f00Stock : List Word := [0xa000a000a000a00, 0xc000c000c000c00, 0xf0000000f000000, 0xf000f0000000000]
def ff000f000f000f00Cuts : List Bound := [fa000a000a000a00Fact, fc000c000c000c00Fact, ff0000000f000000Fact, ff000f0000000000Fact]
def ff000f000f000f00Fact : Bound := (ff000f000f000f00Mask, ff000f000f000f00Stock, 7, ff000f000f000f00Goal)
def ff000f000f000f00Witness : List Witness := [(0xa000a000a000a00, 27, 26), (0xc000c000c000c00, 27, 25), (0xf0000000f000000, 27, 11), (0xf000f0000000000, 43, 11)]
def ff000f000f000f00Forest : Forest := fun i => decodeNode 6 18 0x24b01620a589c192c9d880193190c524327064c9e930858c9e33278c51e31b064b1b6206cc5019315d8c570085c09c19324189509304ccc9003240021001b058c86626198c0c33219890a326180c8602618020600f064b0262008c5020080403c0 i
def ff000f000f000f00States := dagTrace ff000f000f000f00Mask ff000f000f000f00Stock 6 ff000f000f000f00Forest
def ff000f000f000f00Links : DagLinks := dagLookupLinks 0x9472821bc30806fc5f83876e2dc1b0b606c0bdd782f0586ac550aa046e88508a10402801001973025c4b81612c0544a81502a039c700e01c02cc0d001 0x2792c718804314a5882533188c95f319640c5502544066792c6d8803314858c2593181899f32690c51803138064800d858c219308a4ca06327ccc9e31450094d0191c035c92c6d88023144ccc0c324664c5863148c98b31a44098801a5c021333028c913930564c9462548cc8931a440c8701a40020c33028c90c63029890e63235898b33224c9880321c0986008124b0362008c52a92ca189e66208cc9dd31b68c5160273c06c500f04020000f 11 4 12 6 0 5
def ff000f000f000f00Moves := dagMoves ([] : List (DagMoveRecord 64))
def ff000f000f000f00Check := dagCheckNode ff000f000f000f00Mask ff000f000f000f00Goal none (dagKnownCloses ff000f000f000f00Goal ff000f000f000f00Cuts) 43 ff000f000f000f00States ff000f000f000f00Moves ff000f000f000f00Links (0x302b050e4123a040ec501b0c8ac34391c0ac342b058e8103a1506c1639040e45439148e8323a1486c101b140ec123b0c0ec143b040ac701b0506c143a0d0ec323b0c06c12390486c122b058ec142b0c0e4503a0c0e8543b140e4523b1c0ec502b150e8703a148e4162b0586c32390d06c542b1c0e4321b148ac343a, 55) (dagTraceTags ff000f000f000f00Mask 55 (dagTagBases ff000f000f000f00Stock 0xf7ef9f3afffeb6f4fffdfebfbbb6f7c7fff7bbedbefcf3feff9f3fe 0x91350800bfc350f0109382891b50b6809c1884d89224e405e043c6 55) 6 ff000f000f000f00Forest)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff000f000f000f00Roots : dagCheckRoots ff000f000f000f00Mask ff000f000f000f00Goal none (dagKnownCloses ff000f000f000f00Goal ff000f000f000f00Cuts) ff000f000f000f00Witness
    (dagRef 43 ff000f000f000f00States ff000f000f000f00Moves ff000f000f000f00Links 0) ff000f000f000f00Stock 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff000f000f000f00B0 : treeBlock 0 4 ff000f000f000f00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff000f000f000f00B4 : treeBlock 4 4 ff000f000f000f00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff000f000f000f00B8 : treeBlock 8 4 ff000f000f000f00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff000f000f000f00B12 : treeBlock 12 4 ff000f000f000f00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff000f000f000f00B16 : treeBlock 16 4 ff000f000f000f00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff000f000f000f00B20 : treeBlock 20 4 ff000f000f000f00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff000f000f000f00B24 : treeBlock 24 4 ff000f000f000f00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff000f000f000f00B28 : treeBlock 28 4 ff000f000f000f00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff000f000f000f00B32 : treeBlock 32 4 ff000f000f000f00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff000f000f000f00B36 : treeBlock 36 4 ff000f000f000f00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff000f000f000f00B40 : treeBlock 40 3 ff000f000f000f00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff000f000f000f00All : treeBlock 0 43 ff000f000f000f00Check = true := (@treeBlock_merge 0 20 23 ff000f000f000f00Check (@treeBlock_merge 0 8 12 ff000f000f000f00Check (@treeBlock_merge 0 4 4 ff000f000f000f00Check ff000f000f000f00B0 ff000f000f000f00B4) (@treeBlock_merge 8 4 8 ff000f000f000f00Check ff000f000f000f00B8 (@treeBlock_merge 12 4 4 ff000f000f000f00Check ff000f000f000f00B12 ff000f000f000f00B16))) (@treeBlock_merge 20 12 11 ff000f000f000f00Check (@treeBlock_merge 20 4 8 ff000f000f000f00Check ff000f000f000f00B20 (@treeBlock_merge 24 4 4 ff000f000f000f00Check ff000f000f000f00B24 ff000f000f000f00B28)) (@treeBlock_merge 32 4 7 ff000f000f000f00Check ff000f000f000f00B32 (@treeBlock_merge 36 4 3 ff000f000f000f00Check ff000f000f000f00B36 ff000f000f000f00B40))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff000f000f000f00Known : Known ff000f000f000f00Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) ff000f0000000000Lower) ff0000000f000000Lower) fc000c000c000c00Lower) fa000a000a000a00Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff000f000f000f00Lower : Lower ff000f000f000f00Mask ff000f000f000f00Stock ff000f000f000f00Goal 7 := by
  have autos : DagMovesOK ff000f000f000f00Mask ff000f000f000f00Goal 64 ff000f000f000f00Moves := dagMovesOfCheck (by decide +kernel)
  apply lowerDag _ _ _ _ autos _ _ _ ff000f000f000f00Known _ ff000f000f000f00Roots ff000f000f000f00All
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · intro c hc; cases hc
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [ff000f000f000f00Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b hb
    rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def f2200220022002200Mask : Word := 0x2200220022002200
def f2200220022002200Goal : Word := 0x2200200020000000
def f2200220022002200Stock : List Word := [0x2000200020002000, 0x2200000022000000, 0x2200220000000000]
def f2200220022002200Fact : Bound := (f2200220022002200Mask, f2200220022002200Stock, 4, f2200220022002200Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f2200220022002200Lower : Lower f2200220022002200Mask f2200220022002200Stock f2200220022002200Goal 4 :=
  dagShiftLower (width := 64) [([(0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)])] fa000a000a000a00Lower (by decide +kernel)
def f3000300030003000Mask : Word := 0x3000300030003000
def f3000300030003000Goal : Word := 0x3000200020000000
def f3000300030003000Stock : List Word := [0x2000200020002000, 0x3000000030000000, 0x3000300000000000]
def f3000300030003000Fact : Bound := (f3000300030003000Mask, f3000300030003000Stock, 4, f3000300030003000Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f3000300030003000Lower : Lower f3000300030003000Mask f3000300030003000Stock f3000300030003000Goal 4 :=
  dagShiftLower (width := 64) [([(0x8181818181818181, 0), (0x202020202020202, 1), (0x404040404040404, 2), (0x808080808080808, 3)], [(0x1010101010101010, 3), (0x2020202020202020, 2), (0x4040404040404040, 1)])] fa000a000a000a00Lower (by decide +kernel)
def f3300000033000000Mask : Word := 0x3300000033000000
def f3300000033000000Goal : Word := 0x3200000020000000
def f3300000033000000Stock : List Word := [0x2200000022000000, 0x3000000030000000, 0x3300000000000000]
def f3300000033000000Fact : Bound := (f3300000033000000Mask, f3300000033000000Stock, 4, f3300000033000000Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f3300000033000000Lower : Lower f3300000033000000Mask f3300000033000000Stock f3300000033000000Goal 4 :=
  dagShiftLower (width := 64) [([(0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)])] ff0000000f000000Lower (by decide +kernel)
def f3300330000000000Mask : Word := 0x3300330000000000
def f3300330000000000Goal : Word := 0x3200200000000000
def f3300330000000000Stock : List Word := [0x2200220000000000, 0x3000300000000000, 0x3300000000000000]
def f3300330000000000Fact : Bound := (f3300330000000000Mask, f3300330000000000Stock, 4, f3300330000000000Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f3300330000000000Lower : Lower f3300330000000000Mask f3300330000000000Stock f3300330000000000Goal 4 :=
  dagShiftLower (width := 64) [([(0xc3c300000000c3c3, 0), (0xc0c000000000c0c, 2), (0x30300000, 14), (0xc3c30000, 16), (0xc0c0000, 18)], [(0x303000000000, 18), (0xc3c300000000, 16), (0xc0c00000000, 14), (0x3030000000003030, 2)])] ff0000000f000000Lower (by decide +kernel)
def f3300330033003300Mask : Word := 0x3300330033003300
def f3300330033003300Goal : Word := 0x3200200020000000
def f3300330033003300Stock : List Word := [0x2200220022002200, 0x3000300030003000, 0x3300000033000000, 0x3300330000000000]
def f3300330033003300Fact : Bound := (f3300330033003300Mask, f3300330033003300Stock, 7, f3300330033003300Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f3300330033003300Lower : Lower f3300330033003300Mask f3300330033003300Stock f3300330033003300Goal 7 :=
  dagShiftLower (width := 64) [([(0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)])] ff000f000f000f00Lower (by decide +kernel)
def f4400440044004400Mask : Word := 0x4400440044004400
def f4400440044004400Goal : Word := 0x4400400040000000
def f4400440044004400Stock : List Word := [0x4000400040004000, 0x4400000044000000, 0x4400440000000000]
def f4400440044004400Fact : Bound := (f4400440044004400Mask, f4400440044004400Stock, 4, f4400440044004400Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f4400440044004400Lower : Lower f4400440044004400Mask f4400440044004400Stock f4400440044004400Goal 4 :=
  dagShiftLower (width := 64) [([(0x8181818181818181, 0), (0x2020202020202020, 1), (0x808080808080808, 2), (0x202020202020202, 3)], [(0x4040404040404040, 3), (0x1010101010101010, 2), (0x404040404040404, 1)])] fa000a000a000a00Lower (by decide +kernel)
def f5000500050005000Mask : Word := 0x5000500050005000
def f5000500050005000Goal : Word := 0x5000400040000000
def f5000500050005000Stock : List Word := [0x4000400040004000, 0x5000000050000000, 0x5000500000000000]
def f5000500050005000Fact : Bound := (f5000500050005000Mask, f5000500050005000Stock, 4, f5000500050005000Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f5000500050005000Lower : Lower f5000500050005000Mask f5000500050005000Stock f5000500050005000Goal 4 :=
  dagShiftLower (width := 64) [([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])] fa000a000a000a00Lower (by decide +kernel)
def f5500000055000000Mask : Word := 0x5500000055000000
def f5500000055000000Goal : Word := 0x5400000040000000
def f5500000055000000Stock : List Word := [0x4400000044000000, 0x5000000050000000, 0x5500000000000000]
def f5500000055000000Fact : Bound := (f5500000055000000Mask, f5500000055000000Stock, 4, f5500000055000000Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f5500000055000000Lower : Lower f5500000055000000Mask f5500000055000000Stock f5500000055000000Goal 4 :=
  dagShiftLower (width := 64) [([(0x8181818181818181, 0), (0x2020202020202020, 1), (0x808080808080808, 2), (0x202020202020202, 3)], [(0x4040404040404040, 3), (0x1010101010101010, 2), (0x404040404040404, 1)])] ff0000000f000000Lower (by decide +kernel)
def f5500550000000000Mask : Word := 0x5500550000000000
def f5500550000000000Goal : Word := 0x5400400000000000
def f5500550000000000Stock : List Word := [0x4400440000000000, 0x5000500000000000, 0x5500000000000000]
def f5500550000000000Fact : Bound := (f5500550000000000Mask, f5500550000000000Stock, 4, f5500550000000000Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f5500550000000000Lower : Lower f5500550000000000Mask f5500550000000000Stock f5500550000000000Goal 4 :=
  dagShiftLower (width := 64) [([(0x8181000000008181, 0), (0x2020000000002020, 1), (0x808000000000808, 2), (0x202000000000202, 3), (0x40400000, 13), (0x10100000, 14), (0x4040000, 15), (0x81810000, 16), (0x20200000, 17), (0x8080000, 18), (0x2020000, 19)], [(0x404000000000, 19), (0x101000000000, 18), (0x40400000000, 17), (0x818100000000, 16), (0x202000000000, 15), (0x80800000000, 14), (0x20200000000, 13), (0x4040000000004040, 3), (0x1010000000001010, 2), (0x404000000000404, 1)])] ff0000000f000000Lower (by decide +kernel)
def f5500550055005500Mask : Word := 0x5500550055005500
def f5500550055005500Goal : Word := 0x5400400040000000
def f5500550055005500Stock : List Word := [0x4400440044004400, 0x5000500050005000, 0x5500000055000000, 0x5500550000000000]
def f5500550055005500Fact : Bound := (f5500550055005500Mask, f5500550055005500Stock, 7, f5500550055005500Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f5500550055005500Lower : Lower f5500550055005500Mask f5500550055005500Stock f5500550055005500Goal 7 :=
  dagShiftLower (width := 64) [([(0x8181818181818181, 0), (0x2020202020202020, 1), (0x808080808080808, 2), (0x202020202020202, 3)], [(0x4040404040404040, 3), (0x1010101010101010, 2), (0x404040404040404, 1)])] ff000f000f000f00Lower (by decide +kernel)
def fff000000Mask : Word := 0xff000000
def fff000000Goal : Word := 0xe8000000
def fff000000Stock : List Word := [0xaa000000, 0xcc000000, 0xf0000000]
def fff000000Cuts : List Bound := []
def fff000000Fact : Bound := (fff000000Mask, fff000000Stock, 4, fff000000Goal)
def fff000000Witness : List Witness := [(0xaa000000, 27, 26), (0xcc000000, 27, 25), (0xf0000000, 29, 25)]
def fff000000Forest : Forest := fun i => decodeNode 1 4 0xe i
def fff000000States := dagTrace fff000000Mask fff000000Stock 3 fff000000Forest
def fff000000Links : DagLinks := dagLookupLinks 0x9 0x7 2 1 3 1 0 2
def fff000000Moves := dagMoves ([] : List (DagMoveRecord 64))
def fff000000Check := dagCheckNode fff000000Mask fff000000Goal none (dagKnownCloses fff000000Goal fff000000Cuts) 1 fff000000States fff000000Moves fff000000Links (0,0) (fun _ => [])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff000000Roots : dagCheckRoots fff000000Mask fff000000Goal none (dagKnownCloses fff000000Goal fff000000Cuts) fff000000Witness
    (dagRef 1 fff000000States fff000000Moves fff000000Links 0) fff000000Stock 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff000000B0 : treeBlock 0 1 fff000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff000000All : treeBlock 0 1 fff000000Check = true := fff000000B0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff000000Known : Known fff000000Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff000000Lower : Lower fff000000Mask fff000000Stock fff000000Goal 4 := by
  have autos : DagMovesOK fff000000Mask fff000000Goal 64 fff000000Moves := dagMovesOfCheck (by decide +kernel)
  apply lowerDag _ _ _ _ autos _ _ _ fff000000Known _ fff000000Roots fff000000All
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · intro c hc; cases hc
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp [fff000000Cuts]

def fff000000ff000000Mask : Word := 0xff000000ff000000
def fff000000ff000000Goal : Word := 0xfe000000e8000000
def fff000000ff000000Stock : List Word := [0xaa000000aa000000, 0xcc000000cc000000, 0xf0000000f0000000, 0xff00000000000000]
def fff000000ff000000Cuts : List Bound := [fff000000Fact, ff0000000f000000Fact, f3300000033000000Fact, f5500000055000000Fact]
def fff000000ff000000Fact : Bound := (fff000000ff000000Mask, fff000000ff000000Stock, 7, fff000000ff000000Goal)
def fff000000ff000000Witness : List Witness := [(0xaa000000aa000000, 27, 26), (0xcc000000cc000000, 27, 25), (0xf0000000f0000000, 29, 25), (0xff00000000000000, 57, 25)]
def fff000000ff000000Forest : Forest := fun i => decodeNode 6 18 0x24b01c38a58ac192c9d8801c38918a6432b064d9e92c798d9e3287ccd9e31f064b1b6206cc501c385d8a573295c0ac1936424b1063640c750328440d9001f058d8662a19880633618ca86028240d8601c1c0a86013064b0262008c5020080403c0 i
def fff000000ff000000States := dagTrace fff000000ff000000Mask fff000000ff000000Stock 6 fff000000ff000000Forest
def fff000000ff000000Links : DagLinks := dagLookupLinks 0x9472821bc30807001f8b87700e01b8b706c2bdd782f0586b0158aa146e8c11822142284100997320640c81812e25c0b09602a239c700e01c02cc0d001 0x2792c718804314a70e2233590ca6031d540d580294c076792c6d88033147cc725c38898d6462978c78e0355c0a4b0117cca1f3288a4da192c818d9e336340a5201d28045c92c6d8802314440709010670e15635618a4e3355cca5001e2004910281c0411328564d9492c4d8d8d32948c7500361804890281c07090281c070e636358a8c6202ccd8a32a200d8602a124b0362008c52a92ca18ae66208ccadd31f68c51602b3c07c501304020000f 11 4 12 6 0 5
def fff000000ff000000Moves := dagMoves ([] : List (DagMoveRecord 64))
def fff000000ff000000Check := dagCheckNode fff000000ff000000Mask fff000000ff000000Goal none (dagKnownCloses fff000000ff000000Goal fff000000ff000000Cuts) 43 fff000000ff000000States fff000000ff000000Moves fff000000ff000000Links (0x343d1c07c383b0c8f8303f0e0e8383f0c878343f0c0ec323f1c07434390d074303d0c0f8381b0d0f0323a1c078701b0c07c323c1c0fc38390d0f8703e0c074383e0c87c343b1c0f4341f0c06c703b0c0f0301e0c8ec303a0c8f430390e07c383d1c0f0381e0c874383c0d0e8321b1c0e4341b1c0e8341e0e0743239, 55) (dagTraceTags fff000000ff000000Mask 55 (dagTagBases fff000000ff000000Stock 0xbeeb63eb37b353b76eaefb32fc19ff86f5bbb926e757f46cbf2f273 0x401019212010504c01011000d40a0231010a0004a08901102028241 55) 6 fff000000ff000000Forest)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff000000ff000000Roots : dagCheckRoots fff000000ff000000Mask fff000000ff000000Goal none (dagKnownCloses fff000000ff000000Goal fff000000ff000000Cuts) fff000000ff000000Witness
    (dagRef 43 fff000000ff000000States fff000000ff000000Moves fff000000ff000000Links 0) fff000000ff000000Stock 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff000000ff000000B0 : treeBlock 0 4 fff000000ff000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff000000ff000000B4 : treeBlock 4 4 fff000000ff000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff000000ff000000B8 : treeBlock 8 4 fff000000ff000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff000000ff000000B12 : treeBlock 12 4 fff000000ff000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff000000ff000000B16 : treeBlock 16 4 fff000000ff000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff000000ff000000B20 : treeBlock 20 4 fff000000ff000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff000000ff000000B24 : treeBlock 24 4 fff000000ff000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff000000ff000000B28 : treeBlock 28 4 fff000000ff000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff000000ff000000B32 : treeBlock 32 4 fff000000ff000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff000000ff000000B36 : treeBlock 36 4 fff000000ff000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff000000ff000000B40 : treeBlock 40 3 fff000000ff000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff000000ff000000All : treeBlock 0 43 fff000000ff000000Check = true := (@treeBlock_merge 0 20 23 fff000000ff000000Check (@treeBlock_merge 0 8 12 fff000000ff000000Check (@treeBlock_merge 0 4 4 fff000000ff000000Check fff000000ff000000B0 fff000000ff000000B4) (@treeBlock_merge 8 4 8 fff000000ff000000Check fff000000ff000000B8 (@treeBlock_merge 12 4 4 fff000000ff000000Check fff000000ff000000B12 fff000000ff000000B16))) (@treeBlock_merge 20 12 11 fff000000ff000000Check (@treeBlock_merge 20 4 8 fff000000ff000000Check fff000000ff000000B20 (@treeBlock_merge 24 4 4 fff000000ff000000Check fff000000ff000000B24 fff000000ff000000B28)) (@treeBlock_merge 32 4 7 fff000000ff000000Check fff000000ff000000B32 (@treeBlock_merge 36 4 3 fff000000ff000000Check fff000000ff000000B36 fff000000ff000000B40))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff000000ff000000Known : Known fff000000ff000000Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) f5500000055000000Lower) f3300000033000000Lower) ff0000000f000000Lower) fff000000Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff000000ff000000Lower : Lower fff000000ff000000Mask fff000000ff000000Stock fff000000ff000000Goal 7 := by
  have autos : DagMovesOK fff000000ff000000Mask fff000000ff000000Goal 64 fff000000ff000000Moves := dagMovesOfCheck (by decide +kernel)
  apply lowerDag _ _ _ _ autos _ _ _ fff000000ff000000Known _ fff000000ff000000Roots fff000000ff000000All
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · intro c hc; cases hc
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [fff000000ff000000Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b hb
    rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def fff0000000000Mask : Word := 0xff0000000000
def fff0000000000Goal : Word := 0xe80000000000
def fff0000000000Stock : List Word := [0xaa0000000000, 0xcc0000000000, 0xf00000000000]
def fff0000000000Fact : Bound := (fff0000000000Mask, fff0000000000Stock, 4, fff0000000000Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff0000000000Lower : Lower fff0000000000Mask fff0000000000Stock fff0000000000Goal 4 :=
  dagShiftLower (width := 64) [([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])] fff000000Lower (by decide +kernel)
def fff00ff0000000000Mask : Word := 0xff00ff0000000000
def fff00ff0000000000Goal : Word := 0xfe00e80000000000
def fff00ff0000000000Stock : List Word := [0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000]
def fff00ff0000000000Fact : Bound := (fff00ff0000000000Mask, fff00ff0000000000Stock, 7, fff00ff0000000000Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff0000000000Lower : Lower fff00ff0000000000Mask fff00ff0000000000Stock fff00ff0000000000Goal 7 :=
  dagShiftLower (width := 64) [([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])] fff000000ff000000Lower (by decide +kernel)
def fff00ff00Mask : Word := 0xff00ff00
def fff00ff00Goal : Word := 0xe8000000
def fff00ff00Stock : List Word := [0xaa00aa00, 0xcc00cc00, 0xf000f000, 0xff000000]
def fff00ff00Cuts : List Bound := [fff000000Fact]
def fff00ff00Fact : Bound := (fff00ff00Mask, fff00ff00Stock, 5, fff00ff00Goal)
def fff00ff00Witness : List Witness := [(0xaa00aa00, 27, 26), (0xcc00cc00, 27, 25), (0xf000f000, 29, 25), (0xff000000, 27, 11)]
def fff00ff00Forest : Forest := fun i => decodeNode 1 2 0x0 i
def fff00ff00States := dagTrace fff00ff00Mask fff00ff00Stock 4 fff00ff00Forest
def fff00ff00Links : DagLinks := dagLookupLinks 0x0 0x0 2 1 1 1 0 2
def fff00ff00Moves := dagMoves ([] : List (DagMoveRecord 64))
def fff00ff00Check := dagCheckNode fff00ff00Mask fff00ff00Goal none (dagKnownCloses fff00ff00Goal fff00ff00Cuts) 0 fff00ff00States fff00ff00Moves fff00ff00Links (0,0) (fun _ => [])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00Roots : dagCheckRoots fff00ff00Mask fff00ff00Goal none (dagKnownCloses fff00ff00Goal fff00ff00Cuts) fff00ff00Witness
    (dagRef 0 fff00ff00States fff00ff00Moves fff00ff00Links 0) fff00ff00Stock 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00All : treeBlock 0 0 fff00ff00Check = true := rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00Known : Known fff00ff00Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) fff000000Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00Lower : Lower fff00ff00Mask fff00ff00Stock fff00ff00Goal 5 := by
  have autos : DagMovesOK fff00ff00Mask fff00ff00Goal 64 fff00ff00Moves := dagMovesOfCheck (by decide +kernel)
  apply lowerDag _ _ _ _ autos _ _ _ fff00ff00Known _ fff00ff00Roots fff00ff00All
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · intro c hc; cases hc
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [fff00ff00Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b hb
    rcases hb with rfl <;> decide +kernel

def fff000000ff00Mask : Word := 0xff000000ff00
def fff000000ff00Goal : Word := 0xe80000000000
def fff000000ff00Stock : List Word := [0xaa000000aa00, 0xcc000000cc00, 0xf0000000f000, 0xff0000000000]
def fff000000ff00Fact : Bound := (fff000000ff00Mask, fff000000ff00Stock, 5, fff000000ff00Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff000000ff00Lower : Lower fff000000ff00Mask fff000000ff00Stock fff000000ff00Goal 5 :=
  dagShiftLower (width := 64) [([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])] fff00ff00Lower (by decide +kernel)
def faa00aa00aa00aa00Mask : Word := 0xaa00aa00aa00aa00
def faa00aa00aa00aa00Goal : Word := 0xaa00a800a8000000
def faa00aa00aa00aa00Stock : List Word := [0x8800880088008800, 0xa000a000a000a000, 0xaa000000aa000000, 0xaa00aa0000000000]
def faa00aa00aa00aa00Cuts : List Bound := [fa000a000a000a00Fact]
def faa00aa00aa00aa00Fact : Bound := (faa00aa00aa00aa00Mask, faa00aa00aa00aa00Stock, 5, faa00aa00aa00aa00Goal)
def faa00aa00aa00aa00Witness : List Witness := [(0x8800880088008800, 27, 25), (0xa000a000a000a000, 29, 25), (0xaa000000aa000000, 27, 11), (0xaa00aa0000000000, 43, 11)]
def faa00aa00aa00aa00Forest : Forest := fun i => decodeNode 1 2 0x0 i
def faa00aa00aa00aa00States := dagTrace faa00aa00aa00aa00Mask faa00aa00aa00aa00Stock 4 faa00aa00aa00aa00Forest
def faa00aa00aa00aa00Links : DagLinks := dagLookupLinks 0x0 0x0 2 1 1 1 0 2
def faa00aa00aa00aa00Moves := dagMoves ([] : List (DagMoveRecord 64))
def faa00aa00aa00aa00Check := dagCheckNode faa00aa00aa00aa00Mask faa00aa00aa00aa00Goal none (dagKnownCloses faa00aa00aa00aa00Goal faa00aa00aa00aa00Cuts) 0 faa00aa00aa00aa00States faa00aa00aa00aa00Moves faa00aa00aa00aa00Links (0,0) (fun _ => [])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faa00aa00aa00aa00Roots : dagCheckRoots faa00aa00aa00aa00Mask faa00aa00aa00aa00Goal none (dagKnownCloses faa00aa00aa00aa00Goal faa00aa00aa00aa00Cuts) faa00aa00aa00aa00Witness
    (dagRef 0 faa00aa00aa00aa00States faa00aa00aa00aa00Moves faa00aa00aa00aa00Links 0) faa00aa00aa00aa00Stock 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faa00aa00aa00aa00All : treeBlock 0 0 faa00aa00aa00aa00Check = true := rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faa00aa00aa00aa00Known : Known faa00aa00aa00aa00Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) fa000a000a000a00Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faa00aa00aa00aa00Lower : Lower faa00aa00aa00aa00Mask faa00aa00aa00aa00Stock faa00aa00aa00aa00Goal 5 := by
  have autos : DagMovesOK faa00aa00aa00aa00Mask faa00aa00aa00aa00Goal 64 faa00aa00aa00aa00Moves := dagMovesOfCheck (by decide +kernel)
  apply lowerDag _ _ _ _ autos _ _ _ faa00aa00aa00aa00Known _ faa00aa00aa00aa00Roots faa00aa00aa00aa00All
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · intro c hc; cases hc
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [faa00aa00aa00aa00Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b hb
    rcases hb with rfl <;> decide +kernel

def fcc00cc00cc00cc00Mask : Word := 0xcc00cc00cc00cc00
def fcc00cc00cc00cc00Goal : Word := 0xcc00c800c8000000
def fcc00cc00cc00cc00Stock : List Word := [0x8800880088008800, 0xc000c000c000c000, 0xcc000000cc000000, 0xcc00cc0000000000]
def fcc00cc00cc00cc00Fact : Bound := (fcc00cc00cc00cc00Mask, fcc00cc00cc00cc00Stock, 5, fcc00cc00cc00cc00Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fcc00cc00cc00cc00Lower : Lower fcc00cc00cc00cc00Mask fcc00cc00cc00cc00Stock fcc00cc00cc00cc00Goal 5 :=
  dagShiftLower (width := 64) [([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])] faa00aa00aa00aa00Lower (by decide +kernel)
def ff000f000f000f000Mask : Word := 0xf000f000f000f000
def ff000f000f000f000Goal : Word := 0xf000e000e0000000
def ff000f000f000f000Stock : List Word := [0xa000a000a000a000, 0xc000c000c000c000, 0xf0000000f0000000, 0xf000f00000000000]
def ff000f000f000f000Fact : Bound := (ff000f000f000f000Mask, ff000f000f000f000Stock, 5, ff000f000f000f000Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff000f000f000f000Lower : Lower ff000f000f000f000Mask ff000f000f000f000Stock ff000f000f000f000Goal 5 :=
  dagShiftLower (width := 64) [([(0x8181818181818181, 0), (0x202020202020202, 1), (0x404040404040404, 2), (0x808080808080808, 3)], [(0x1010101010101010, 3), (0x2020202020202020, 2), (0x4040404040404040, 1)])] faa00aa00aa00aa00Lower (by decide +kernel)
def fff00ff00ff00ff00Mask : Word := 0xff00ff00ff00ff00
def fff00ff00ff00ff00Goal : Word := 0xfe00e800e8000000
def fff00ff00ff00ff00Stock : List Word := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]
def fff00ff00ff00ff00Cuts : List Bound := [ff000f000f000f00Fact, f3300330033003300Fact, f5500550055005500Fact, fff000000ff000000Fact, fff00ff0000000000Fact, fff00ff00Fact, fff000000ff00Fact, faa00aa00aa00aa00Fact, fcc00cc00cc00cc00Fact, ff000f000f000f000Fact]
def fff00ff00ff00ff00Fact : Bound := (fff00ff00ff00ff00Mask, fff00ff00ff00ff00Stock, 10, fff00ff00ff00ff00Goal)
def fff00ff00ff00ff00Witness : List Witness := [(0xaa00aa00aa00aa00, 27, 26), (0xcc00cc00cc00cc00, 27, 25), (0xf000f000f000f000, 29, 25), (0xff000000ff000000, 27, 11), (0xff00ff0000000000, 43, 11)]
def fff00ff00ff00ff00Forest : Forest := fun i => decodeNode 8 20 0xc380192cbef44c962bbe629bef44c5629c532bbe329bef44c0629c0329c002bbe029be93301c38bc92c01c38b492cb7629b7329b7933b4c38b592cb462001f4492030b1c38aa936aa636aa328ad336aa93cab035aac3f92f44a8c3892f49a492ca4029a493f92c38a293e92f4a9af489fc4a9a0289d94a9a92c9a0299a93392f449893292f449303495c3f93c389392c9231f01c388592c8d6298d3298d93385c388b92c85c388693386c388792c866208531401f445903082c387b9367b6367b93c7e3357b3287c0367bc3f59f4479c3859f497592c753297593f59c387393e59f4a6bf4870c4a6b3286e94a6b92c6b3296b93359f446993259f446403466c3f64c386492c59f4460c3f60c386031d59f445ac385a93e5a9325a92c5a3145901f01f441d02456c384f63c549354f6364f3364f028500364fc3f1df444dc381df444ac384a92c1df4946636466204663f1dc384392c4363e1df4a3bf484094a3b6343e64a3b6363b6203b6331df443892c386321df4430c3f30c3830c383393c30c38319303062a1df442a0342dc3f2ac382a92c2a6201df4426c3f26c382632a1df441ec3f1ec381ec381f9331f92c1f01c1e02a1d01301c380292c18629183291893302c381692c02c381193311c381292c1162002f440bc380b93e0b9320b92c0b31f02c380393303c380792c03c380492c0462003314020080101f00 i
def fff00ff00ff00ff00States := dagTrace fff00ff00ff00ff00Mask fff00ff00ff00ff00Stock 9 fff00ff00ff00ff00Forest
def fff00ff00ff00ff00Links : DagLinks := dagLookupLinks 0x1977c8b644314f873c386186fef7c3be05ec6f43737b81d8f6bad567a925482a41520a6ad2ca8e94169d3ce827233909c0ce026e33709b0cab2541237910c8824411d58e846ca3431a08c8c6423031808c044d626111288844422031008624031f88fc07e03f01eeaf5278a3bc9de0ef07693a51c6cdc76e036c5b60da16d03645b20d8166633018aec4162031017eabf05e92f05780bb15d82e85740ba05aaad41664b305982c85640ae4568ab05562a7453829c14e0a7053828952d88f747823851c08d146823051808b13fe1fc0f0e7803c01cd4e427203901b54da06d03591a84d406913481a04d0068031a98c0c606123009800be25f02f09780ba25852c01600ae25702b814d0a4251128093109624a1248924092049023190906d83241900c806402d515909d04a425012808c83e81f00f807c03e01f00d286083001800b105802c01420820298032001 0xbcc38ba92cb262b906208332b5731f1b314b992cb062b8f6208132b5531f1a314c9f44af341c5329ae31d80041c10297f01d8e3145301319008ad31cc6f44af641c5629ac31e52041c002951011b86207d01f180087c01c50010c2f4480641c162952341c03297b01e4f012b7620aa31f8d314ca92cc862bc7629b6620c432bc3329a931f8c314bf02bbe0297a01f4e01317008b5c38a89378b92c796374d62b16620bcc38b492ca762b8a6207832b4c31f15314b5c388992c4b62b14620b992cb862988620b73291331487c381292cb5c388692c4a62b11620bac38b6933b492c856204931f10314a8f4498c3e96c3836335623292831d0f314b1030ad328ad328ab93cb0c38a6949a093daf9369c9319492cae636ac336aa035350296101d27011a8f44a2c3e93c3834335603292631d0e3149fc48a6f499ec3e9c93ea592ca4029a2c380d0089fc489ff489d028a0f4a9ec4a9c94a9b92c9a02998f440c0089503496f4494c3f93c380b314b2f44a9c3fa7c38a393fa193e99933979329292c2f0295f01d250110a0088bc388992c5e62b096208f92c8e629886208d3290831487c380792c8bc388692c5d62b0662087c380592c87c380492c89c38889338692c0362090c388c9338a92c856205931f0231479f4469c3e67c3836635626295e6202431e820307c0287e93c7c32881c38779497193d809366d9316592c7f6367d335353296131d7b0362301279f4473c3e64c3834635606295d6202231e70c4877f496fc3e6d93e7692c7532973c385c31470c4870f486e32871f4a6fc4a6d94a6c92c6b32969f445b3146603467f4465c3f64c385a6202131c200101f31c62f4461c3f60c381e0105ef445dc385c93e5b9325a92c83f447ac3f78c387493f7293e6a933689326392c2f3295f31d593141d0124df444bc383993e369362e92c2863624336560245463c500285002855c3853935486494163d526363d6313562a2c620513362732a4f0362302a4df444ac384493e349362b92c26636223364bf444ac384393e389322a92c4094848f493f93e3d63e476364662044c384392c4094840f483e63441f4a3f94a3d64a3c6363b62039f443892c31c3c33c3c33c3831c3836f4435c3f34c383293c309302d0342ef442cc3f2bc382a92c213282001c1f32828f4427c3f26c381e01c213282001c1f32821c38209331f92c24f4423c3f22c381e01c57f444ec3f4cc384992c4563f4263e3a633376322f62a296202532a1d02a16c381492c0f62b096201a92c1962913620183290831412c380792c16c381192c0e62b0662012c380592c12c380492c14c38139331192c036200ff440ec380d93e0c9320b92c07c380592c07c380492c05c380492c09c38089330692c036201bc38179331592c106200a31f02314cbc38bd933bb92cb36209131f843145801f1c013010080001f 13 4 12 8 0 5
def fff00ff00ff00ff00Moves := dagMoves ([] : List (DagMoveRecord 64))
def fff00ff00ff00ff00Check := dagCheckNode fff00ff00ff00ff00Mask fff00ff00ff00ff00Goal none (dagKnownCloses fff00ff00ff00ff00Goal fff00ff00ff00ff00Cuts) 204 fff00ff00ff00ff00States fff00ff00ff00ff00Moves fff00ff00ff00ff00Links (0x50ac1a1f148ec502d0d07c323d150ec301d078ac1e2e06078321f078781e2d0506c301e070f85039160f8123906074383e048ac143a0c0e4183c0e07c343b050b8703e140e8122d048741e3f068bc321b0d0e8341b058ac542b160b83239148b4543a160f0522b0c874161b068b47039078bc341e0e0f01c2e148e4703a1c0f0381d068741e1f160b4381e07078542e, 64) (dagTraceTags fff00ff00ff00ff00Mask 64 (dagTagBases fff00ff00ff00ff00Stock 0xb6c4f7df6bfcef896f3bfdf6dc5b5bf65d7dac6de0aabcffeafba73e7f953517ff965ab1f767e278 0x3200600601bc43890d1104b41c4259c440ecac606088ac7e8ace81184f11341364dc1201f267a230 64) 9 fff00ff00ff00ff00Forest)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00Roots : dagCheckRoots fff00ff00ff00ff00Mask fff00ff00ff00ff00Goal none (dagKnownCloses fff00ff00ff00ff00Goal fff00ff00ff00ff00Cuts) fff00ff00ff00ff00Witness
    (dagRef 204 fff00ff00ff00ff00States fff00ff00ff00ff00Moves fff00ff00ff00ff00Links 0) fff00ff00ff00ff00Stock 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B0 : treeBlock 0 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B4 : treeBlock 4 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B8 : treeBlock 8 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B12 : treeBlock 12 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B16 : treeBlock 16 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B20 : treeBlock 20 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B24 : treeBlock 24 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B28 : treeBlock 28 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B32 : treeBlock 32 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B36 : treeBlock 36 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B40 : treeBlock 40 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B44 : treeBlock 44 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B48 : treeBlock 48 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B52 : treeBlock 52 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B56 : treeBlock 56 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B60 : treeBlock 60 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B64 : treeBlock 64 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B68 : treeBlock 68 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B72 : treeBlock 72 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B76 : treeBlock 76 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B80 : treeBlock 80 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B84 : treeBlock 84 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B88 : treeBlock 88 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B92 : treeBlock 92 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B96 : treeBlock 96 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B100 : treeBlock 100 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B104 : treeBlock 104 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B108 : treeBlock 108 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B112 : treeBlock 112 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B116 : treeBlock 116 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B120 : treeBlock 120 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B124 : treeBlock 124 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B128 : treeBlock 128 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B132 : treeBlock 132 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B136 : treeBlock 136 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B140 : treeBlock 140 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B144 : treeBlock 144 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B148 : treeBlock 148 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B152 : treeBlock 152 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B156 : treeBlock 156 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B160 : treeBlock 160 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B164 : treeBlock 164 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B168 : treeBlock 168 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B172 : treeBlock 172 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B176 : treeBlock 176 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B180 : treeBlock 180 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B184 : treeBlock 184 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B188 : treeBlock 188 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B192 : treeBlock 192 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B196 : treeBlock 196 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00B200 : treeBlock 200 4 fff00ff00ff00ff00Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00All : treeBlock 0 204 fff00ff00ff00ff00Check = true := (@treeBlock_merge 0 100 104 fff00ff00ff00ff00Check (@treeBlock_merge 0 48 52 fff00ff00ff00ff00Check (@treeBlock_merge 0 24 24 fff00ff00ff00ff00Check (@treeBlock_merge 0 12 12 fff00ff00ff00ff00Check (@treeBlock_merge 0 4 8 fff00ff00ff00ff00Check fff00ff00ff00ff00B0 (@treeBlock_merge 4 4 4 fff00ff00ff00ff00Check fff00ff00ff00ff00B4 fff00ff00ff00ff00B8)) (@treeBlock_merge 12 4 8 fff00ff00ff00ff00Check fff00ff00ff00ff00B12 (@treeBlock_merge 16 4 4 fff00ff00ff00ff00Check fff00ff00ff00ff00B16 fff00ff00ff00ff00B20))) (@treeBlock_merge 24 12 12 fff00ff00ff00ff00Check (@treeBlock_merge 24 4 8 fff00ff00ff00ff00Check fff00ff00ff00ff00B24 (@treeBlock_merge 28 4 4 fff00ff00ff00ff00Check fff00ff00ff00ff00B28 fff00ff00ff00ff00B32)) (@treeBlock_merge 36 4 8 fff00ff00ff00ff00Check fff00ff00ff00ff00B36 (@treeBlock_merge 40 4 4 fff00ff00ff00ff00Check fff00ff00ff00ff00B40 fff00ff00ff00ff00B44)))) (@treeBlock_merge 48 24 28 fff00ff00ff00ff00Check (@treeBlock_merge 48 12 12 fff00ff00ff00ff00Check (@treeBlock_merge 48 4 8 fff00ff00ff00ff00Check fff00ff00ff00ff00B48 (@treeBlock_merge 52 4 4 fff00ff00ff00ff00Check fff00ff00ff00ff00B52 fff00ff00ff00ff00B56)) (@treeBlock_merge 60 4 8 fff00ff00ff00ff00Check fff00ff00ff00ff00B60 (@treeBlock_merge 64 4 4 fff00ff00ff00ff00Check fff00ff00ff00ff00B64 fff00ff00ff00ff00B68))) (@treeBlock_merge 72 12 16 fff00ff00ff00ff00Check (@treeBlock_merge 72 4 8 fff00ff00ff00ff00Check fff00ff00ff00ff00B72 (@treeBlock_merge 76 4 4 fff00ff00ff00ff00Check fff00ff00ff00ff00B76 fff00ff00ff00ff00B80)) (@treeBlock_merge 84 8 8 fff00ff00ff00ff00Check (@treeBlock_merge 84 4 4 fff00ff00ff00ff00Check fff00ff00ff00ff00B84 fff00ff00ff00ff00B88) (@treeBlock_merge 92 4 4 fff00ff00ff00ff00Check fff00ff00ff00ff00B92 fff00ff00ff00ff00B96))))) (@treeBlock_merge 100 52 52 fff00ff00ff00ff00Check (@treeBlock_merge 100 24 28 fff00ff00ff00ff00Check (@treeBlock_merge 100 12 12 fff00ff00ff00ff00Check (@treeBlock_merge 100 4 8 fff00ff00ff00ff00Check fff00ff00ff00ff00B100 (@treeBlock_merge 104 4 4 fff00ff00ff00ff00Check fff00ff00ff00ff00B104 fff00ff00ff00ff00B108)) (@treeBlock_merge 112 4 8 fff00ff00ff00ff00Check fff00ff00ff00ff00B112 (@treeBlock_merge 116 4 4 fff00ff00ff00ff00Check fff00ff00ff00ff00B116 fff00ff00ff00ff00B120))) (@treeBlock_merge 124 12 16 fff00ff00ff00ff00Check (@treeBlock_merge 124 4 8 fff00ff00ff00ff00Check fff00ff00ff00ff00B124 (@treeBlock_merge 128 4 4 fff00ff00ff00ff00Check fff00ff00ff00ff00B128 fff00ff00ff00ff00B132)) (@treeBlock_merge 136 8 8 fff00ff00ff00ff00Check (@treeBlock_merge 136 4 4 fff00ff00ff00ff00Check fff00ff00ff00ff00B136 fff00ff00ff00ff00B140) (@treeBlock_merge 144 4 4 fff00ff00ff00ff00Check fff00ff00ff00ff00B144 fff00ff00ff00ff00B148)))) (@treeBlock_merge 152 24 28 fff00ff00ff00ff00Check (@treeBlock_merge 152 12 12 fff00ff00ff00ff00Check (@treeBlock_merge 152 4 8 fff00ff00ff00ff00Check fff00ff00ff00ff00B152 (@treeBlock_merge 156 4 4 fff00ff00ff00ff00Check fff00ff00ff00ff00B156 fff00ff00ff00ff00B160)) (@treeBlock_merge 164 4 8 fff00ff00ff00ff00Check fff00ff00ff00ff00B164 (@treeBlock_merge 168 4 4 fff00ff00ff00ff00Check fff00ff00ff00ff00B168 fff00ff00ff00ff00B172))) (@treeBlock_merge 176 12 16 fff00ff00ff00ff00Check (@treeBlock_merge 176 4 8 fff00ff00ff00ff00Check fff00ff00ff00ff00B176 (@treeBlock_merge 180 4 4 fff00ff00ff00ff00Check fff00ff00ff00ff00B180 fff00ff00ff00ff00B184)) (@treeBlock_merge 188 8 8 fff00ff00ff00ff00Check (@treeBlock_merge 188 4 4 fff00ff00ff00ff00Check fff00ff00ff00ff00B188 fff00ff00ff00ff00B192) (@treeBlock_merge 196 4 4 fff00ff00ff00ff00Check fff00ff00ff00ff00B196 fff00ff00ff00ff00B200))))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00Known : Known fff00ff00ff00ff00Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) ff000f000f000f000Lower) fcc00cc00cc00cc00Lower) faa00aa00aa00aa00Lower) fff000000ff00Lower) fff00ff00Lower) fff00ff0000000000Lower) fff000000ff000000Lower) f5500550055005500Lower) f3300330033003300Lower) ff000f000f000f00Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fff00ff00ff00ff00Lower : Lower fff00ff00ff00ff00Mask fff00ff00ff00ff00Stock fff00ff00ff00ff00Goal 10 := by
  have autos : DagMovesOK fff00ff00ff00ff00Mask fff00ff00ff00ff00Goal 64 fff00ff00ff00ff00Moves := dagMovesOfCheck (by decide +kernel)
  apply lowerDag _ _ _ _ autos _ _ _ fff00ff00ff00ff00Known _ fff00ff00ff00ff00Roots fff00ff00ff00ff00All
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · intro c hc; cases hc
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [fff00ff00ff00ff00Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def faaaa0000aaaa0000Mask : Word := 0xaaaa0000aaaa0000
def faaaa0000aaaa0000Goal : Word := 0xaa800000a8000000
def faaaa0000aaaa0000Stock : List Word := [0x8888000088880000, 0xa0a00000a0a00000, 0xaa000000aa000000, 0xaaaa000000000000]
def faaaa0000aaaa0000Cuts : List Bound := []
def faaaa0000aaaa0000Fact : Bound := (faaaa0000aaaa0000Mask, faaaa0000aaaa0000Stock, 6, faaaa0000aaaa0000Goal)
def faaaa0000aaaa0000Witness : List Witness := [(0x8888000088880000, 27, 25), (0xa0a00000a0a00000, 29, 25), (0xaa000000aa000000, 27, 19), (0xaaaa000000000000, 55, 23)]
def faaaa0000aaaa0000Forest : Forest := fun i => decodeNode 6 18 0x24b4192c04cc21030858ac131c78071e62705884162004cac163464c9c193058091631f04cd130104cc6c131504c50102b04cd0e027064c0b3242c07c103420070801b0404c131c1403c10090402020080403c0 i
def faaaa0000aaaa0000States := dagTrace faaaa0000aaaa0000Mask faaaa0000aaaa0000Stock 5 faaaa0000aaaa0000Forest
def faaaa0000aaaa0000Links : DagLinks := dagLookupLinks 0x2b0541a8150281500a0130a604a190320230c608c108a104207c4f81e0ba1740e05c0380684d01a03025c2b8160ac0580a841a001 0x200888cc210307cc71e01c080219324658d179305809143344c040200838090e334324c0b324240d0801c14030531c08022492d8e4b2062b7589dc6216d881a32b60c9d531f48c6d131540c50f02b3409ca01f1c06c60131003c300904020000f 11 5 12 6 0 6
def faaaa0000aaaa0000Moves := dagMoves ([] : List (DagMoveRecord 64))
def faaaa0000aaaa0000Check := dagCheckNode faaaa0000aaaa0000Mask faaaa0000aaaa0000Goal none (dagKnownCloses faaaa0000aaaa0000Goal faaaa0000aaaa0000Cuts) 37 faaaa0000aaaa0000States faaaa0000aaaa0000Moves faaaa0000aaaa0000Links (0x1a86c661d098f4621f0a8ec2e390c8dc223f1a87c22370a8fc6a3b1886c2e3d188fc663d0c8fc263f088ec221f18874661f088f426390a8e42a1b098742e3b198fc6a3f088746237088e42e3f0987c2a370b86c323d098dc263b198e4221b0a8f42a1f1a874661b1a8e4323b0b874623d188ec321f1a8dc261b188e42e37198ec2a1d198dc32391a8f42e1f0c86c321d, 64) (dagTraceTags faaaa0000aaaa0000Mask 64 (dagTagBases faaaa0000aaaa0000Stock 0x2f77e39dd7a36bb8fdbffffeedfff6df73e7de2f7638d96d9bfaf45d7b553da6 0xd09b0c0d008e6aa802008000040110138cb400d4583a894c640545386b8485a4 64) 5 faaaa0000aaaa0000Forest)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaa0000aaaa0000Roots : dagCheckRoots faaaa0000aaaa0000Mask faaaa0000aaaa0000Goal none (dagKnownCloses faaaa0000aaaa0000Goal faaaa0000aaaa0000Cuts) faaaa0000aaaa0000Witness
    (dagRef 37 faaaa0000aaaa0000States faaaa0000aaaa0000Moves faaaa0000aaaa0000Links 0) faaaa0000aaaa0000Stock 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaa0000aaaa0000B0 : treeBlock 0 4 faaaa0000aaaa0000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaa0000aaaa0000B4 : treeBlock 4 4 faaaa0000aaaa0000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaa0000aaaa0000B8 : treeBlock 8 4 faaaa0000aaaa0000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaa0000aaaa0000B12 : treeBlock 12 4 faaaa0000aaaa0000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaa0000aaaa0000B16 : treeBlock 16 4 faaaa0000aaaa0000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaa0000aaaa0000B20 : treeBlock 20 4 faaaa0000aaaa0000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaa0000aaaa0000B24 : treeBlock 24 4 faaaa0000aaaa0000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaa0000aaaa0000B28 : treeBlock 28 4 faaaa0000aaaa0000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaa0000aaaa0000B32 : treeBlock 32 4 faaaa0000aaaa0000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaa0000aaaa0000B36 : treeBlock 36 1 faaaa0000aaaa0000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaa0000aaaa0000All : treeBlock 0 37 faaaa0000aaaa0000Check = true := (@treeBlock_merge 0 20 17 faaaa0000aaaa0000Check (@treeBlock_merge 0 8 12 faaaa0000aaaa0000Check (@treeBlock_merge 0 4 4 faaaa0000aaaa0000Check faaaa0000aaaa0000B0 faaaa0000aaaa0000B4) (@treeBlock_merge 8 4 8 faaaa0000aaaa0000Check faaaa0000aaaa0000B8 (@treeBlock_merge 12 4 4 faaaa0000aaaa0000Check faaaa0000aaaa0000B12 faaaa0000aaaa0000B16))) (@treeBlock_merge 20 8 9 faaaa0000aaaa0000Check (@treeBlock_merge 20 4 4 faaaa0000aaaa0000Check faaaa0000aaaa0000B20 faaaa0000aaaa0000B24) (@treeBlock_merge 28 4 5 faaaa0000aaaa0000Check faaaa0000aaaa0000B28 (@treeBlock_merge 32 4 1 faaaa0000aaaa0000Check faaaa0000aaaa0000B32 faaaa0000aaaa0000B36))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaa0000aaaa0000Known : Known faaaa0000aaaa0000Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaa0000aaaa0000Lower : Lower faaaa0000aaaa0000Mask faaaa0000aaaa0000Stock faaaa0000aaaa0000Goal 6 := by
  have autos : DagMovesOK faaaa0000aaaa0000Mask faaaa0000aaaa0000Goal 64 faaaa0000aaaa0000Moves := dagMovesOfCheck (by decide +kernel)
  apply lowerDag _ _ _ _ autos _ _ _ faaaa0000aaaa0000Known _ faaaa0000aaaa0000Roots faaaa0000aaaa0000All
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · intro c hc; cases hc
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp [faaaa0000aaaa0000Cuts]

def faaaaaaaa00000000Mask : Word := 0xaaaaaaaa00000000
def faaaaaaaa00000000Goal : Word := 0xaa80a80000000000
def faaaaaaaa00000000Stock : List Word := [0x8888888800000000, 0xa0a0a0a000000000, 0xaa00aa0000000000, 0xaaaa000000000000]
def faaaaaaaa00000000Fact : Bound := (faaaaaaaa00000000Mask, faaaaaaaa00000000Stock, 6, faaaaaaaa00000000Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaa00000000Lower : Lower faaaaaaaa00000000Mask faaaaaaaa00000000Stock faaaaaaaa00000000Goal 6 :=
  dagShiftLower (width := 64) [([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])] faaaa0000aaaa0000Lower (by decide +kernel)
def fa0a0a0a0a0a0a0aMask : Word := 0xa0a0a0a0a0a0a0a
def fa0a0a0a0a0a0a0aGoal : Word := 0xa00080008000000
def fa0a0a0a0a0a0a0aStock : List Word := [0x808080808080808, 0xa000a000a000a00, 0xa0a00000a0a0000, 0xa0a0a0a00000000]
def fa0a0a0a0a0a0a0aCuts : List Bound := [fa000a000a000a00Fact]
def fa0a0a0a0a0a0a0aFact : Bound := (fa0a0a0a0a0a0a0aMask, fa0a0a0a0a0a0a0aStock, 5, fa0a0a0a0a0a0a0aGoal)
def fa0a0a0a0a0a0a0aWitness : List Witness := [(0x808080808080808, 27, 25), (0xa000a000a000a00, 27, 19), (0xa0a00000a0a0000, 27, 11), (0xa0a0a0a00000000, 43, 11)]
def fa0a0a0a0a0a0a0aForest : Forest := fun i => decodeNode 1 2 0x0 i
def fa0a0a0a0a0a0a0aStates := dagTrace fa0a0a0a0a0a0a0aMask fa0a0a0a0a0a0a0aStock 4 fa0a0a0a0a0a0a0aForest
def fa0a0a0a0a0a0a0aLinks : DagLinks := dagLookupLinks 0x0 0x0 2 1 1 1 0 2
def fa0a0a0a0a0a0a0aMoves := dagMoves ([] : List (DagMoveRecord 64))
def fa0a0a0a0a0a0a0aCheck := dagCheckNode fa0a0a0a0a0a0a0aMask fa0a0a0a0a0a0a0aGoal none (dagKnownCloses fa0a0a0a0a0a0a0aGoal fa0a0a0a0a0a0a0aCuts) 0 fa0a0a0a0a0a0a0aStates fa0a0a0a0a0a0a0aMoves fa0a0a0a0a0a0a0aLinks (0,0) (fun _ => [])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fa0a0a0a0a0a0a0aRoots : dagCheckRoots fa0a0a0a0a0a0a0aMask fa0a0a0a0a0a0a0aGoal none (dagKnownCloses fa0a0a0a0a0a0a0aGoal fa0a0a0a0a0a0a0aCuts) fa0a0a0a0a0a0a0aWitness
    (dagRef 0 fa0a0a0a0a0a0a0aStates fa0a0a0a0a0a0a0aMoves fa0a0a0a0a0a0a0aLinks 0) fa0a0a0a0a0a0a0aStock 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fa0a0a0a0a0a0a0aAll : treeBlock 0 0 fa0a0a0a0a0a0a0aCheck = true := rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fa0a0a0a0a0a0a0aKnown : Known fa0a0a0a0a0a0a0aCuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) fa000a000a000a00Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fa0a0a0a0a0a0a0aLower : Lower fa0a0a0a0a0a0a0aMask fa0a0a0a0a0a0a0aStock fa0a0a0a0a0a0a0aGoal 5 := by
  have autos : DagMovesOK fa0a0a0a0a0a0a0aMask fa0a0a0a0a0a0a0aGoal 64 fa0a0a0a0a0a0a0aMoves := dagMovesOfCheck (by decide +kernel)
  apply lowerDag _ _ _ _ autos _ _ _ fa0a0a0a0a0a0a0aKnown _ fa0a0a0a0a0a0a0aRoots fa0a0a0a0a0a0a0aAll
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · intro c hc; cases hc
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [fa0a0a0a0a0a0a0aCuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b hb
    rcases hb with rfl <;> decide +kernel

def f2222222222222222Mask : Word := 0x2222222222222222
def f2222222222222222Goal : Word := 0x2200200020000000
def f2222222222222222Stock : List Word := [0x2020202020202020, 0x2200220022002200, 0x2222000022220000, 0x2222222200000000]
def f2222222222222222Fact : Bound := (f2222222222222222Mask, f2222222222222222Stock, 5, f2222222222222222Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f2222222222222222Lower : Lower f2222222222222222Mask f2222222222222222Stock f2222222222222222Goal 5 :=
  dagShiftLower (width := 64) [([(0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)])] fa0a0a0a0a0a0a0aLower (by decide +kernel)
def f8080808080808080Mask : Word := 0x8080808080808080
def f8080808080808080Goal : Word := 0x8080800080000000
def f8080808080808080Stock : List Word := [0x8000800080008000, 0x8080000080800000, 0x8080808000000000]
def f8080808080808080Cuts : List Bound := []
def f8080808080808080Fact : Bound := (f8080808080808080Mask, f8080808080808080Stock, 4, f8080808080808080Goal)
def f8080808080808080Witness : List Witness := [(0x8000800080008000, 31, 23), (0x8080000080800000, 31, 15), (0x8080808000000000, 47, 15)]
def f8080808080808080Forest : Forest := fun i => decodeNode 1 4 0xe i
def f8080808080808080States := dagTrace f8080808080808080Mask f8080808080808080Stock 3 f8080808080808080Forest
def f8080808080808080Links : DagLinks := dagLookupLinks 0x9 0x7 2 1 3 1 0 2
def f8080808080808080Moves := dagMoves ([] : List (DagMoveRecord 64))
def f8080808080808080Check := dagCheckNode f8080808080808080Mask f8080808080808080Goal none (dagKnownCloses f8080808080808080Goal f8080808080808080Cuts) 1 f8080808080808080States f8080808080808080Moves f8080808080808080Links (0,0) (fun _ => [])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f8080808080808080Roots : dagCheckRoots f8080808080808080Mask f8080808080808080Goal none (dagKnownCloses f8080808080808080Goal f8080808080808080Cuts) f8080808080808080Witness
    (dagRef 1 f8080808080808080States f8080808080808080Moves f8080808080808080Links 0) f8080808080808080Stock 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f8080808080808080B0 : treeBlock 0 1 f8080808080808080Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f8080808080808080All : treeBlock 0 1 f8080808080808080Check = true := f8080808080808080B0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f8080808080808080Known : Known f8080808080808080Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f8080808080808080Lower : Lower f8080808080808080Mask f8080808080808080Stock f8080808080808080Goal 4 := by
  have autos : DagMovesOK f8080808080808080Mask f8080808080808080Goal 64 f8080808080808080Moves := dagMovesOfCheck (by decide +kernel)
  apply lowerDag _ _ _ _ autos _ _ _ f8080808080808080Known _ f8080808080808080Roots f8080808080808080All
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · intro c hc; cases hc
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp [f8080808080808080Cuts]

def f8888888888888888Mask : Word := 0x8888888888888888
def f8888888888888888Goal : Word := 0x8880880088000000
def f8888888888888888Stock : List Word := [0x8080808080808080, 0x8800880088008800, 0x8888000088880000, 0x8888888800000000]
def f8888888888888888Cuts : List Bound := [f8080808080808080Fact]
def f8888888888888888Fact : Bound := (f8888888888888888Mask, f8888888888888888Stock, 5, f8888888888888888Goal)
def f8888888888888888Witness : List Witness := [(0x8080808080808080, 55, 51), (0x8800880088008800, 27, 19), (0x8888000088880000, 27, 11), (0x8888888800000000, 43, 11)]
def f8888888888888888Forest : Forest := fun i => decodeNode 1 2 0x0 i
def f8888888888888888States := dagTrace f8888888888888888Mask f8888888888888888Stock 4 f8888888888888888Forest
def f8888888888888888Links : DagLinks := dagLookupLinks 0x0 0x0 2 1 1 1 0 2
def f8888888888888888Moves := dagMoves ([] : List (DagMoveRecord 64))
def f8888888888888888Check := dagCheckNode f8888888888888888Mask f8888888888888888Goal none (dagKnownCloses f8888888888888888Goal f8888888888888888Cuts) 0 f8888888888888888States f8888888888888888Moves f8888888888888888Links (0,0) (fun _ => [])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f8888888888888888Roots : dagCheckRoots f8888888888888888Mask f8888888888888888Goal none (dagKnownCloses f8888888888888888Goal f8888888888888888Cuts) f8888888888888888Witness
    (dagRef 0 f8888888888888888States f8888888888888888Moves f8888888888888888Links 0) f8888888888888888Stock 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f8888888888888888All : treeBlock 0 0 f8888888888888888Check = true := rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f8888888888888888Known : Known f8888888888888888Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) f8080808080808080Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f8888888888888888Lower : Lower f8888888888888888Mask f8888888888888888Stock f8888888888888888Goal 5 := by
  have autos : DagMovesOK f8888888888888888Mask f8888888888888888Goal 64 f8888888888888888Moves := dagMovesOfCheck (by decide +kernel)
  apply lowerDag _ _ _ _ autos _ _ _ f8888888888888888Known _ f8888888888888888Roots f8888888888888888All
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · intro c hc; cases hc
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [f8888888888888888Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b hb
    rcases hb with rfl <;> decide +kernel

def fa0a0a0a0a0a0a0a0Mask : Word := 0xa0a0a0a0a0a0a0a0
def fa0a0a0a0a0a0a0a0Goal : Word := 0xa080a000a0000000
def fa0a0a0a0a0a0a0a0Stock : List Word := [0x8080808080808080, 0xa000a000a000a000, 0xa0a00000a0a00000, 0xa0a0a0a000000000]
def fa0a0a0a0a0a0a0a0Fact : Bound := (fa0a0a0a0a0a0a0a0Mask, fa0a0a0a0a0a0a0a0Stock, 5, fa0a0a0a0a0a0a0a0Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fa0a0a0a0a0a0a0a0Lower : Lower fa0a0a0a0a0a0a0a0Mask fa0a0a0a0a0a0a0a0Stock fa0a0a0a0a0a0a0a0Goal 5 :=
  dagShiftLower (width := 64) [([(0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)])] f8888888888888888Lower (by decide +kernel)
def faaaaaaaaaaaaaaaaMask : Word := 0xaaaaaaaaaaaaaaaa
def faaaaaaaaaaaaaaaaGoal : Word := 0xaa80a800a8000000
def faaaaaaaaaaaaaaaaStock : List Word := [0x8888888888888888, 0xa0a0a0a0a0a0a0a0, 0xaa00aa00aa00aa00, 0xaaaa0000aaaa0000, 0xaaaaaaaa00000000]
def faaaaaaaaaaaaaaaaCuts : List Bound := [faaaa0000aaaa0000Fact, faaaaaaaa00000000Fact, fa0a0a0a0a0a0a0aFact, f2222222222222222Fact, f8888888888888888Fact, fa0a0a0a0a0a0a0a0Fact, faa00aa00aa00aa00Fact]
def faaaaaaaaaaaaaaaaFact : Bound := (faaaaaaaaaaaaaaaaMask, faaaaaaaaaaaaaaaaStock, 9, faaaaaaaaaaaaaaaaGoal)
def faaaaaaaaaaaaaaaaWitness : List Witness := [(0x8888888888888888, 27, 25), (0xa0a0a0a0a0a0a0a0, 29, 25), (0xaa00aa00aa00aa00, 27, 19), (0xaaaa0000aaaa0000, 27, 11), (0xaaaaaaaa00000000, 43, 11)]
def faaaaaaaaaaaaaaaaForest : Forest := fun i => decodeNode 9 21 0x18700192db68135ea4b2da6797703cbbb15db4c72e803974627b6995db58d2e264f6d02bb699a5b809edb26601c38b5c960070f6b18715831cb300e5998ceb0c4358032b1b10560c7eb0c515e01caf808578c6eb003f58328ac80e568072b20375863300fa24f30fa79e915493f9e61e54a4fa786394f01ca7b1fcf18829463d4a010a580f5298fa78c433c03ea3b104f0c7e78c514201ca1808508c6e7803f3c3289e80e4f80727a0373c62700fa24d40d27387f35c389ac9f4d64ca6ac4201c3897499cbb0e2632592e01f97009cb9880038712462a95c9ec9312250651289339200e49a4b6492592433300fa2468ca24327f1ac3e8f31547a4c6340391c92d8d496468c9c03e88fdc3f7ee1c3f70f6292591493e7ee1c4364ce1b25b0d92c86815c3409e1b278fdc3e84c9f4264b213264fdc3881499c0a4b6052590202b81013c0a4c1fb870fe9337f4963f8091fa63e01f447719a3eb0fddd870ee93f77499bba4b1dd870ef93377c963bd8cddec4eef620778083b8c6c03e88e6c3f7361c39a4fdcd266e692d73496398c5403870db9336de1c38a4b1b6c66db6276db10b6f0e1b9258dc6206d98a0070e190654d893d646243540a1ab266c801069c96b224b190038d0633646243370f19ac56c801c65b13b2188590c40c803300fa22d40a18b27eb5c3e6119530a4c56a020c092d5ac962d40717ac7eb5c485d61e2e98ad6a038b86275ab10ad58816a04e01f444661fa330e11987aaf92c57c9f2330e151266a892d544962a0cad5064ea893c4661f2924f949258a49324661c2764cd3b25a9d92c4e995a74c9d3b2608cc484d61e268cfd1989097c3c4b999a330e1272669392c4999223312121878903154649e2364c11a6288c01f00fa21d80d11387e76c383b49f9da4cced2587601c41b1f9d807102c66766273b3109d9880ed870779333bc961dd8cceec4e776203b80e1d806c03e8845c3f22e1c1164fc8b2664592d22c961170f4d727a6b62035b1f1170f8cd2626663e333101998c88b27c609323031f1818c8c0c406062622c9e9698c8b52785b31c2db13168cf88b2625463e2a498154c70aac4c5433222c9e9358c89b2784f01c27b13134cc89a07c459312331f11a4c090038486262319f1180c88a02601f441401a10b0fc51870280281fc9f8a00a07b266280101dc968a24b0518702993314c960a40706ac662901c19b138a588452c402901c17b190a80705ac4c2a012150080a8c68526382800f00fa20630fc318701893f0c4998624b4312581863f0c319863120398781c62b0c31386188430c401800900e1c00a4cc058701492c0131980989c04c4202c380749603988004666023270149e0264c01263e0231b0118a80b0e007258036200198a0080200203e00 i
def faaaaaaaaaaaaaaaaStates := dagTrace faaaaaaaaaaaaaaaaMask faaaaaaaaaaaaaaaaStock 8 faaaaaaaaaaaaaaaaForest
def faaaaaaaaaaaaaaaaLinks : DagLinks := dagLookupLinks 0x28e851c0a38146868d051a0a2c545828b05122a2034402870d0c1a18142866ebcd6396e12c8a5904b2096412b8a5704ae095832a0a530ca609483280a4e149a1934126064a146398c41178a2f045c18b811496290452089c51382260c4c08943110e220444088430f8a1e0c3c087430d8a191430186010b861513f997f00fe01fb0bf607ec0fd81ea8bce379c0f381e41bc807900eabdd503aa07486e901d203a027400e785cf0388b7100e201c2138407080df8dbf037c16f80d9adb1135a46ac4d581ab034e469c0d381a7034e069c0d3819e4b3c06780cf019a233406680cd019a033406680c8a591032206440c70d82630216040bf897e0afa15f02bd857b02f605ec0bd817b02f605d4cb4b16902d205a40b4816902d205a40ae35591ab205640ab0d5602ac05580ab015602a63519aa301460286350c0a18141128205002a00140027c24f809f013c127804ec29d813b0260b4c0098012e125c04b80958d2b025414a80950128125004a00930926024a1494092811a5a302450889091202240438887010e021c0438087010e020a941408281050202440408081010202040408080f849f003e007b08f601ec03d047a00f401e803c467880f101de23bc07780ed11c2c38027000de11ba137026d84da09b4036426c80d809b0036006c00d801b0036006c00d801b00348c6330c50982430025d18b4316612c825900b2016402ace5580ab015602ac0521ca1193c327804f009e0128a24c249809301260244446908c09180230046008a110c42142428085010a020c441807f20fc11f803f007e00f821f003c106978d011a0033086508c81188430845f10be017442e045c00b8017002d845910b0115842b005600ac015422a805408a801500281048408081000200040008001000200040008001000200040007c20f801f003e0062d0b8617002e005630ac015802b005600ac0140c28005000a00140026104c00980130026004c008c60b3401a8001 0x2d7871569339d496cce4b244c671862b7db13bb1885c8c40c633359995a28c9ce863e4331b1318a858c52f404d7833cbb81e5d4c72e803971324b8b1a5b8092dc6697b92dbcc965a58f6aac637662bb9b13d2589670c4332620b9195dc0c9e2e63ef931b7598ab8cc52de0576d0275900fa2006ce60264100f1280485402263870e292c0a3105af0e2d12673792d984964b18ce2cc56f862775310b85881b2666b132b439939c8c7c80636243150998a5524f6a52796731cb300e58c0ca5669160318af80857c072c0c515e0106c02456c062b40215a01cad994564072d387b68c38a9c99d464ca6d25965633a4b19591886c4c412a33d90199bdcc9ec263f5d31b7498ab80c51ae07ac403343013d7007eb0036710131f00788c024240115493da949e553d22a58792933d8f998b580f5860635031ca780e52c042960214d620a618f52807a8e07d1e33ca218c50c0428603944628a10083080f27e0313e0109f00e4fcca27a03956f44aae1f54e4fea327d3592ca731fd258fa90c43466209399fc74cc5ec64f4531fa098dba0c55be628d403f60818a1409e8003f3c01b380098f003c44012110089c81a4ebd127187f37c389b49f4d64ca4ac7f1b6337ab12b9d885bcc40d233f5f999a10c94de63e3a31b1098a840c5263870dd92c07b104c70e1b92580e62099e1c4ca4ce61259246338d313b99885b6c40d13335f1939b8c7c72636203150698a4bc07e5c02729c3e95b1517807653891283289300e4b30e25527b2793392c96c924b1780669902b410139640743e0120c0088fe1e484ca23f87d1e62a2c00ec7007245e892093f8ec98c6e4b635258cf03f4b015a0009ca603a1e0090580441f0f2006611594885c9e42a4c1fe04912c3c7f1984570f6152651492c6701ec4b0e2232671092d87c962ec0ce1c0570d0270e8048280221787d0a93e84c962e80c60f8710693382c96c124b19a0670302b810138700241201100c387fc99bfa4b231e8917c3f8b61c44e4fa192790893280c983300fd72066fd0240d804820021e8638fa334798083c8c71e2020f00107798e3d30e1e7266f292c78b19bc189ddec40fbf447ce1fbe30e1ef27ef69337ac963280fd6e0667f027770080680240e010ecf4475e1fbab0e1d327ee893373c96b9a4b19267eb6333479959f8c9c3262a063147161c3764b00ac40e2c386e496011881bb870dc92c01b103930e1c7266e192c70319b7d89dbcc42db62064199ad4c9d1863e7d31b0c18a808c51ad87cd832a2918f35b121aa050d3010269943400719d890cdc3c6580e3670e1af27ad493369496b464b19ec66cc62b65313b2588590c404c31e61e1e3140a18787cc232a2598f3000408c650bd01c5de242eb0f170038c6f446249fb064c57f25abe92c5e31fae58ad6ec4eb66215ab10114c794587895630584a429a4f14b2609432456e1e24d8c16187aa593257c9626ccf55b870ac93355c96aaa4b130666a932b54193a44c551c628a6c3e52c9f2924b12e662a2c3850c99a824b53f2589a3334f195a74c9d2062a8d3144de2426b0f13189097c3c4ae1c2524cd2725891c484861e23a4f11b260b3f445961fac70e15d27ca793c51c992724c13267e963334919223cc55186287c3284481a1ec070f46507901c3c00e1dcca1060388101c3e61c1ee4ccf5258796333c3139dd88115e8888c3f43e1c21a4fd0b2668492c4131fa018ccfec4e7e6213eb101d8070706306d64834b1e19d8c06e01836318363241918c0c4c485e348290240d0030d0c786363030b12160cf0960783200c1898c0c0c60db87a6c93d33b19189898d6c4057332250191a70f8d12626763e30b13199880ba67c5103e2e19e1400f05c01856330248180b0030c927c639323131f1858c8c0c405a33e2a1991380f88e0642900c2e3181724f0b66385e93d2eb191698988c064566302b498154c70b12625763e2a3131340f8a0c605093c2780e14a4f4a2c644e626269991258c0932604801c25c989298f88ec4c4633e3a7a21cf0fce58707193f384999be4b4dd2586a63e32b1917d898b267c533322601f1140c850018386281b98e1080d06cc50350101a18e0fc0a0660203231c1e8140c58a07602030628178060b8c906a0382d00c161920cc0705e0382d01c173190b1898560242a0101c61c0de4cc6d25834633193138c588460c402931a21fa21070fc818703e93f1e4998ea4b4732582831c0ee240730f04de8825c3f1261c08e4fc452662192d1049607d8fc3cc661b62b0d31386588430c4014c3807c96015880298700e92c0231003f0e01d258036200549e0264c00b8700492c01b1005b0e02b2661392c0931984589c20c420d6200619982cc9c1063e0731b0318a808c52f98716c933b549655d8ce76c4f3462196b1048ccce3264efc31f7698db94c55b4628c70335a013a2c07cea036440131380785c024020100001f 15 5 12 9 0 6
def faaaaaaaaaaaaaaaaMoves := dagMoves ([] : List (DagMoveRecord 64))
def faaaaaaaaaaaaaaaaCheck := dagCheckNode faaaaaaaaaaaaaaaaMask faaaaaaaaaaaaaaaaGoal none (dagKnownCloses faaaaaaaaaaaaaaaaGoal faaaaaaaaaaaaaaaaCuts) 381 faaaaaaaaaaaaaaaaStates faaaaaaaaaaaaaaaaMoves faaaaaaaaaaaaaaaaLinks (0x486c0e1f038bc4637058bc2e1d118ec523b118bc4e2b078b4422d048b44239148bc0a2d0b8fc2e1b198fc321f048e40e37128dc662b0a8dc1e2b148f41a2f138b42239138fc6a39188f4422b1a874323d048741e1d0887452390c8e44e2f188e41a1d1a8dc4e37058ac1e2f0c8742e370787c321b0b87c1a2d0a874161b1a8f46637148b4522b128b4462b0986c663b, 64) (dagTraceTags faaaaaaaaaaaaaaaaMask 64 (dagTagBases faaaaaaaaaaaaaaaaStock 0x3bffafffd1ef44fdd704fea7bfbcfbc3effff97ffff3bfbf7cbbb6babe5deee8fbc2f7d2404f7957 0x13d6232be16c00fd0400f185b2a8dac3892a18701d93b5306461c6db245d6e887ee0e54a04476947 64) 8 faaaaaaaaaaaaaaaaForest)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaRoots : dagCheckRoots faaaaaaaaaaaaaaaaMask faaaaaaaaaaaaaaaaGoal none (dagKnownCloses faaaaaaaaaaaaaaaaGoal faaaaaaaaaaaaaaaaCuts) faaaaaaaaaaaaaaaaWitness
    (dagRef 381 faaaaaaaaaaaaaaaaStates faaaaaaaaaaaaaaaaMoves faaaaaaaaaaaaaaaaLinks 0) faaaaaaaaaaaaaaaaStock 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB0 : treeBlock 0 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB4 : treeBlock 4 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB8 : treeBlock 8 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB12 : treeBlock 12 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB16 : treeBlock 16 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB20 : treeBlock 20 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB24 : treeBlock 24 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB28 : treeBlock 28 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB32 : treeBlock 32 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB36 : treeBlock 36 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB40 : treeBlock 40 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB44 : treeBlock 44 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB48 : treeBlock 48 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB52 : treeBlock 52 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB56 : treeBlock 56 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB60 : treeBlock 60 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB64 : treeBlock 64 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB68 : treeBlock 68 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB72 : treeBlock 72 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB76 : treeBlock 76 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB80 : treeBlock 80 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB84 : treeBlock 84 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB88 : treeBlock 88 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB92 : treeBlock 92 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB96 : treeBlock 96 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB100 : treeBlock 100 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB104 : treeBlock 104 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB108 : treeBlock 108 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB112 : treeBlock 112 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB116 : treeBlock 116 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB120 : treeBlock 120 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB124 : treeBlock 124 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB128 : treeBlock 128 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB132 : treeBlock 132 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB136 : treeBlock 136 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB140 : treeBlock 140 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB144 : treeBlock 144 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB148 : treeBlock 148 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB152 : treeBlock 152 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB156 : treeBlock 156 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB160 : treeBlock 160 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB164 : treeBlock 164 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB168 : treeBlock 168 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB172 : treeBlock 172 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB176 : treeBlock 176 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB180 : treeBlock 180 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB184 : treeBlock 184 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB188 : treeBlock 188 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB192 : treeBlock 192 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB196 : treeBlock 196 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB200 : treeBlock 200 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB204 : treeBlock 204 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB208 : treeBlock 208 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB212 : treeBlock 212 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB216 : treeBlock 216 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB220 : treeBlock 220 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB224 : treeBlock 224 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB228 : treeBlock 228 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB232 : treeBlock 232 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB236 : treeBlock 236 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB240 : treeBlock 240 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB244 : treeBlock 244 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB248 : treeBlock 248 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB252 : treeBlock 252 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB256 : treeBlock 256 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB260 : treeBlock 260 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB264 : treeBlock 264 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB268 : treeBlock 268 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB272 : treeBlock 272 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB276 : treeBlock 276 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB280 : treeBlock 280 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB284 : treeBlock 284 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB288 : treeBlock 288 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB292 : treeBlock 292 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB296 : treeBlock 296 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB300 : treeBlock 300 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB304 : treeBlock 304 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB308 : treeBlock 308 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB312 : treeBlock 312 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB316 : treeBlock 316 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB320 : treeBlock 320 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB324 : treeBlock 324 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB328 : treeBlock 328 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB332 : treeBlock 332 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB336 : treeBlock 336 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB340 : treeBlock 340 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB344 : treeBlock 344 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB348 : treeBlock 348 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB352 : treeBlock 352 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB356 : treeBlock 356 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB360 : treeBlock 360 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB364 : treeBlock 364 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB368 : treeBlock 368 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB372 : treeBlock 372 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB376 : treeBlock 376 4 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaB380 : treeBlock 380 1 faaaaaaaaaaaaaaaaCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaAll : treeBlock 0 381 faaaaaaaaaaaaaaaaCheck = true := (@treeBlock_merge 0 192 189 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 0 96 96 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 0 48 48 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 0 24 24 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 0 12 12 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 0 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB0 (@treeBlock_merge 4 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB4 faaaaaaaaaaaaaaaaB8)) (@treeBlock_merge 12 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB12 (@treeBlock_merge 16 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB16 faaaaaaaaaaaaaaaaB20))) (@treeBlock_merge 24 12 12 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 24 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB24 (@treeBlock_merge 28 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB28 faaaaaaaaaaaaaaaaB32)) (@treeBlock_merge 36 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB36 (@treeBlock_merge 40 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB40 faaaaaaaaaaaaaaaaB44)))) (@treeBlock_merge 48 24 24 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 48 12 12 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 48 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB48 (@treeBlock_merge 52 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB52 faaaaaaaaaaaaaaaaB56)) (@treeBlock_merge 60 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB60 (@treeBlock_merge 64 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB64 faaaaaaaaaaaaaaaaB68))) (@treeBlock_merge 72 12 12 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 72 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB72 (@treeBlock_merge 76 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB76 faaaaaaaaaaaaaaaaB80)) (@treeBlock_merge 84 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB84 (@treeBlock_merge 88 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB88 faaaaaaaaaaaaaaaaB92))))) (@treeBlock_merge 96 48 48 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 96 24 24 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 96 12 12 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 96 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB96 (@treeBlock_merge 100 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB100 faaaaaaaaaaaaaaaaB104)) (@treeBlock_merge 108 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB108 (@treeBlock_merge 112 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB112 faaaaaaaaaaaaaaaaB116))) (@treeBlock_merge 120 12 12 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 120 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB120 (@treeBlock_merge 124 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB124 faaaaaaaaaaaaaaaaB128)) (@treeBlock_merge 132 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB132 (@treeBlock_merge 136 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB136 faaaaaaaaaaaaaaaaB140)))) (@treeBlock_merge 144 24 24 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 144 12 12 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 144 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB144 (@treeBlock_merge 148 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB148 faaaaaaaaaaaaaaaaB152)) (@treeBlock_merge 156 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB156 (@treeBlock_merge 160 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB160 faaaaaaaaaaaaaaaaB164))) (@treeBlock_merge 168 12 12 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 168 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB168 (@treeBlock_merge 172 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB172 faaaaaaaaaaaaaaaaB176)) (@treeBlock_merge 180 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB180 (@treeBlock_merge 184 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB184 faaaaaaaaaaaaaaaaB188)))))) (@treeBlock_merge 192 96 93 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 192 48 48 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 192 24 24 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 192 12 12 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 192 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB192 (@treeBlock_merge 196 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB196 faaaaaaaaaaaaaaaaB200)) (@treeBlock_merge 204 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB204 (@treeBlock_merge 208 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB208 faaaaaaaaaaaaaaaaB212))) (@treeBlock_merge 216 12 12 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 216 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB216 (@treeBlock_merge 220 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB220 faaaaaaaaaaaaaaaaB224)) (@treeBlock_merge 228 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB228 (@treeBlock_merge 232 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB232 faaaaaaaaaaaaaaaaB236)))) (@treeBlock_merge 240 24 24 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 240 12 12 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 240 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB240 (@treeBlock_merge 244 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB244 faaaaaaaaaaaaaaaaB248)) (@treeBlock_merge 252 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB252 (@treeBlock_merge 256 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB256 faaaaaaaaaaaaaaaaB260))) (@treeBlock_merge 264 12 12 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 264 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB264 (@treeBlock_merge 268 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB268 faaaaaaaaaaaaaaaaB272)) (@treeBlock_merge 276 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB276 (@treeBlock_merge 280 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB280 faaaaaaaaaaaaaaaaB284))))) (@treeBlock_merge 288 48 45 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 288 24 24 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 288 12 12 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 288 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB288 (@treeBlock_merge 292 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB292 faaaaaaaaaaaaaaaaB296)) (@treeBlock_merge 300 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB300 (@treeBlock_merge 304 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB304 faaaaaaaaaaaaaaaaB308))) (@treeBlock_merge 312 12 12 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 312 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB312 (@treeBlock_merge 316 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB316 faaaaaaaaaaaaaaaaB320)) (@treeBlock_merge 324 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB324 (@treeBlock_merge 328 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB328 faaaaaaaaaaaaaaaaB332)))) (@treeBlock_merge 336 24 21 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 336 12 12 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 336 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB336 (@treeBlock_merge 340 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB340 faaaaaaaaaaaaaaaaB344)) (@treeBlock_merge 348 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB348 (@treeBlock_merge 352 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB352 faaaaaaaaaaaaaaaaB356))) (@treeBlock_merge 360 12 9 faaaaaaaaaaaaaaaaCheck (@treeBlock_merge 360 4 8 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB360 (@treeBlock_merge 364 4 4 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB364 faaaaaaaaaaaaaaaaB368)) (@treeBlock_merge 372 4 5 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB372 (@treeBlock_merge 376 4 1 faaaaaaaaaaaaaaaaCheck faaaaaaaaaaaaaaaaB376 faaaaaaaaaaaaaaaaB380)))))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaKnown : Known faaaaaaaaaaaaaaaaCuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) faa00aa00aa00aa00Lower) fa0a0a0a0a0a0a0a0Lower) f8888888888888888Lower) f2222222222222222Lower) fa0a0a0a0a0a0a0aLower) faaaaaaaa00000000Lower) faaaa0000aaaa0000Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem faaaaaaaaaaaaaaaaLower : Lower faaaaaaaaaaaaaaaaMask faaaaaaaaaaaaaaaaStock faaaaaaaaaaaaaaaaGoal 9 := by
  have autos : DagMovesOK faaaaaaaaaaaaaaaaMask faaaaaaaaaaaaaaaaGoal 64 faaaaaaaaaaaaaaaaMoves := dagMovesOfCheck (by decide +kernel)
  apply lowerDag _ _ _ _ autos _ _ _ faaaaaaaaaaaaaaaaKnown _ faaaaaaaaaaaaaaaaRoots faaaaaaaaaaaaaaaaAll
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · intro c hc; cases hc
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [faaaaaaaaaaaaaaaaCuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def fcccc0000cccc0000Mask : Word := 0xcccc0000cccc0000
def fcccc0000cccc0000Goal : Word := 0xcc800000c8000000
def fcccc0000cccc0000Stock : List Word := [0x8888000088880000, 0xc0c00000c0c00000, 0xcc000000cc000000, 0xcccc000000000000]
def fcccc0000cccc0000Fact : Bound := (fcccc0000cccc0000Mask, fcccc0000cccc0000Stock, 6, fcccc0000cccc0000Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fcccc0000cccc0000Lower : Lower fcccc0000cccc0000Mask fcccc0000cccc0000Stock fcccc0000cccc0000Goal 6 :=
  dagShiftLower (width := 64) [([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])] faaaa0000aaaa0000Lower (by decide +kernel)
def fcccccccc00000000Mask : Word := 0xcccccccc00000000
def fcccccccc00000000Goal : Word := 0xcc80c80000000000
def fcccccccc00000000Stock : List Word := [0x8888888800000000, 0xc0c0c0c000000000, 0xcc00cc0000000000, 0xcccc000000000000]
def fcccccccc00000000Fact : Bound := (fcccccccc00000000Mask, fcccccccc00000000Stock, 6, fcccccccc00000000Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fcccccccc00000000Lower : Lower fcccccccc00000000Mask fcccccccc00000000Stock fcccccccc00000000Goal 6 :=
  dagShiftLower (width := 64) [([(0x9999000000009999, 0), (0x2222000000002222, 1), (0x44440000, 15), (0x99990000, 16), (0x22220000, 17)], [(0x444400000000, 17), (0x999900000000, 16), (0x222200000000, 15), (0x4444000000004444, 1)])] faaaa0000aaaa0000Lower (by decide +kernel)
def fc0c0c0c0c0c0c0cMask : Word := 0xc0c0c0c0c0c0c0c
def fc0c0c0c0c0c0c0cGoal : Word := 0xc00080008000000
def fc0c0c0c0c0c0c0cStock : List Word := [0x808080808080808, 0xc000c000c000c00, 0xc0c00000c0c0000, 0xc0c0c0c00000000]
def fc0c0c0c0c0c0c0cFact : Bound := (fc0c0c0c0c0c0c0cMask, fc0c0c0c0c0c0c0cStock, 5, fc0c0c0c0c0c0c0cGoal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fc0c0c0c0c0c0c0cLower : Lower fc0c0c0c0c0c0c0cMask fc0c0c0c0c0c0c0cStock fc0c0c0c0c0c0c0cGoal 5 :=
  dagShiftLower (width := 64) [([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])] fa0a0a0a0a0a0a0aLower (by decide +kernel)
def f4444444444444444Mask : Word := 0x4444444444444444
def f4444444444444444Goal : Word := 0x4400400040000000
def f4444444444444444Stock : List Word := [0x4040404040404040, 0x4400440044004400, 0x4444000044440000, 0x4444444400000000]
def f4444444444444444Fact : Bound := (f4444444444444444Mask, f4444444444444444Stock, 5, f4444444444444444Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f4444444444444444Lower : Lower f4444444444444444Mask f4444444444444444Stock f4444444444444444Goal 5 :=
  dagShiftLower (width := 64) [([(0x8181818181818181, 0), (0x2020202020202020, 1), (0x808080808080808, 2), (0x202020202020202, 3)], [(0x4040404040404040, 3), (0x1010101010101010, 2), (0x404040404040404, 1)])] fa0a0a0a0a0a0a0aLower (by decide +kernel)
def fc0c0c0c0c0c0c0c0Mask : Word := 0xc0c0c0c0c0c0c0c0
def fc0c0c0c0c0c0c0c0Goal : Word := 0xc080c000c0000000
def fc0c0c0c0c0c0c0c0Stock : List Word := [0x8080808080808080, 0xc000c000c000c000, 0xc0c00000c0c00000, 0xc0c0c0c000000000]
def fc0c0c0c0c0c0c0c0Fact : Bound := (fc0c0c0c0c0c0c0c0Mask, fc0c0c0c0c0c0c0c0Stock, 5, fc0c0c0c0c0c0c0c0Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fc0c0c0c0c0c0c0c0Lower : Lower fc0c0c0c0c0c0c0c0Mask fc0c0c0c0c0c0c0c0Stock fc0c0c0c0c0c0c0c0Goal 5 :=
  dagShiftLower (width := 64) [([(0x8181818181818181, 0), (0x2020202020202020, 1), (0x808080808080808, 2), (0x202020202020202, 3)], [(0x4040404040404040, 3), (0x1010101010101010, 2), (0x404040404040404, 1)])] f8888888888888888Lower (by decide +kernel)
def fccccccccccccccccMask : Word := 0xcccccccccccccccc
def fccccccccccccccccGoal : Word := 0xcc80c800c8000000
def fccccccccccccccccStock : List Word := [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000]
def fccccccccccccccccFact : Bound := (fccccccccccccccccMask, fccccccccccccccccStock, 9, fccccccccccccccccGoal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fccccccccccccccccLower : Lower fccccccccccccccccMask fccccccccccccccccStock fccccccccccccccccGoal 9 :=
  dagShiftLower (width := 64) [([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])] faaaaaaaaaaaaaaaaLower (by decide +kernel)
def ff0f00000f0f00000Mask : Word := 0xf0f00000f0f00000
def ff0f00000f0f00000Goal : Word := 0xf0800000e0000000
def ff0f00000f0f00000Stock : List Word := [0xa0a00000a0a00000, 0xc0c00000c0c00000, 0xf0000000f0000000, 0xf0f0000000000000]
def ff0f00000f0f00000Fact : Bound := (ff0f00000f0f00000Mask, ff0f00000f0f00000Stock, 6, ff0f00000f0f00000Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff0f00000f0f00000Lower : Lower ff0f00000f0f00000Mask ff0f00000f0f00000Stock ff0f00000f0f00000Goal 6 :=
  dagShiftLower (width := 64) [([(0x8181818181818181, 0), (0x202020202020202, 1), (0x404040404040404, 2), (0x808080808080808, 3)], [(0x1010101010101010, 3), (0x2020202020202020, 2), (0x4040404040404040, 1)])] faaaa0000aaaa0000Lower (by decide +kernel)
def ff0f0f0f000000000Mask : Word := 0xf0f0f0f000000000
def ff0f0f0f000000000Goal : Word := 0xf080e00000000000
def ff0f0f0f000000000Stock : List Word := [0xa0a0a0a000000000, 0xc0c0c0c000000000, 0xf000f00000000000, 0xf0f0000000000000]
def ff0f0f0f000000000Fact : Bound := (ff0f0f0f000000000Mask, ff0f0f0f000000000Stock, 6, ff0f0f0f000000000Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff0f0f0f000000000Lower : Lower ff0f0f0f000000000Mask ff0f0f0f000000000Stock ff0f0f0f000000000Goal 6 :=
  dagShiftLower (width := 64) [([(0x8181000000008181, 0), (0x202000000000202, 1), (0x404000000000404, 2), (0x808000000000808, 3), (0x10100000, 13), (0x20200000, 14), (0x40400000, 15), (0x81810000, 16), (0x2020000, 17), (0x4040000, 18), (0x8080000, 19)], [(0x101000000000, 19), (0x202000000000, 18), (0x404000000000, 17), (0x818100000000, 16), (0x20200000000, 15), (0x40400000000, 14), (0x80800000000, 13), (0x1010000000001010, 3), (0x2020000000002020, 2), (0x4040000000004040, 1)])] faaaa0000aaaa0000Lower (by decide +kernel)
def f3030303030303030Mask : Word := 0x3030303030303030
def f3030303030303030Goal : Word := 0x3000200020000000
def f3030303030303030Stock : List Word := [0x2020202020202020, 0x3000300030003000, 0x3030000030300000, 0x3030303000000000]
def f3030303030303030Fact : Bound := (f3030303030303030Mask, f3030303030303030Stock, 5, f3030303030303030Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f3030303030303030Lower : Lower f3030303030303030Mask f3030303030303030Stock f3030303030303030Goal 5 :=
  dagShiftLower (width := 64) [([(0x8181818181818181, 0), (0x202020202020202, 1), (0x404040404040404, 2), (0x808080808080808, 3)], [(0x1010101010101010, 3), (0x2020202020202020, 2), (0x4040404040404040, 1)])] fa0a0a0a0a0a0a0aLower (by decide +kernel)
def f5050505050505050Mask : Word := 0x5050505050505050
def f5050505050505050Goal : Word := 0x5000400040000000
def f5050505050505050Stock : List Word := [0x4040404040404040, 0x5000500050005000, 0x5050000050500000, 0x5050505000000000]
def f5050505050505050Fact : Bound := (f5050505050505050Mask, f5050505050505050Stock, 5, f5050505050505050Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f5050505050505050Lower : Lower f5050505050505050Mask f5050505050505050Stock f5050505050505050Goal 5 :=
  dagShiftLower (width := 64) [([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])] fa0a0a0a0a0a0a0aLower (by decide +kernel)
def ff0f0f0f0f0f0f0f0Mask : Word := 0xf0f0f0f0f0f0f0f0
def ff0f0f0f0f0f0f0f0Goal : Word := 0xf080e000e0000000
def ff0f0f0f0f0f0f0f0Stock : List Word := [0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000]
def ff0f0f0f0f0f0f0f0Fact : Bound := (ff0f0f0f0f0f0f0f0Mask, ff0f0f0f0f0f0f0f0Stock, 9, ff0f0f0f0f0f0f0f0Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff0f0f0f0f0f0f0f0Lower : Lower ff0f0f0f0f0f0f0f0Mask ff0f0f0f0f0f0f0f0Stock ff0f0f0f0f0f0f0f0Goal 9 :=
  dagShiftLower (width := 64) [([(0x8181818181818181, 0), (0x202020202020202, 1), (0x404040404040404, 2), (0x808080808080808, 3)], [(0x1010101010101010, 3), (0x2020202020202020, 2), (0x4040404040404040, 1)])] faaaaaaaaaaaaaaaaLower (by decide +kernel)
def fffff000000000000Mask : Word := 0xffff000000000000
def fffff000000000000Goal : Word := 0xfe80000000000000
def fffff000000000000Stock : List Word := [0xaaaa000000000000, 0xcccc000000000000, 0xf0f0000000000000, 0xff00000000000000]
def fffff000000000000Cuts : List Bound := []
def fffff000000000000Fact : Bound := (fffff000000000000Mask, fffff000000000000Stock, 6, fffff000000000000Goal)
def fffff000000000000Witness : List Witness := [(0xaaaa000000000000, 55, 54), (0xcccc000000000000, 55, 53), (0xf0f0000000000000, 55, 51), (0xff00000000000000, 57, 49)]
def fffff000000000000Forest : Forest := fun i => decodeNode 6 18 0x24b4192c04cc21030858ac131c78071e627058841620058c1903064cac132858041632704c7c16284cc6c131504c50163038cc0e02b040a0b01c2c09c101f04ca0801b0404c131c1403c10090402020080403c0 i
def fffff000000000000States := dagTrace fffff000000000000Mask fffff000000000000Stock 5 fffff000000000000Forest
def fffff000000000000Links : DagLinks := dagLookupLinks 0x2b0541a8150281500a0130a604a1941282314608c108a00c007c2f81e0bc0780e09c0380684c85903015c2b8160ac0580a841a001 0x200888cc210307cc71e01c08021a630640c173285804133184d8a020083d8c0e330300a0b01c20060832814030531c08022492d8e4b2062b7589dc6216d881832b54c9d431f48c6d131540c50d02b2809c901f1c06c60131003c300904020000f 11 5 12 6 0 6
def fffff000000000000Moves := dagMoves ([] : List (DagMoveRecord 64))
def fffff000000000000Check := dagCheckNode fffff000000000000Mask fffff000000000000Goal none (dagKnownCloses fffff000000000000Goal fffff000000000000Cuts) 37 fffff000000000000States fffff000000000000Moves fffff000000000000Links (0x180fc6c39188f8683b190f46a3a198f070371a8ec663e180f4623a1c0fc6c3b190fc6439188fc603e180dc643c198f4683f1a8f8683a1a0e46c3d188f0603b188dc6a3f190f8623b180f0623d190ec603a198e46c3f1a8f0663f1b0f0703b1c0f460391a8e4663a1a0dc683e1b0e8683d1c0f864371a8dc683c1a8f46c3e190e86c371c0f07039198dc62391c0e8663b, 64) (dagTraceTags fffff000000000000Mask 64 (dagTagBases fffff000000000000Stock 0xfeffdff7fffde7b7ab6afe6ec7a37f68b5dee71f3547b9cbd9afacdd6d7a5a5d 0x108000000602032548407c4068bcf404a4718422d8491c926d08a2d4b0c0a0d 64) 5 fffff000000000000Forest)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff000000000000Roots : dagCheckRoots fffff000000000000Mask fffff000000000000Goal none (dagKnownCloses fffff000000000000Goal fffff000000000000Cuts) fffff000000000000Witness
    (dagRef 37 fffff000000000000States fffff000000000000Moves fffff000000000000Links 0) fffff000000000000Stock 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff000000000000B0 : treeBlock 0 4 fffff000000000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff000000000000B4 : treeBlock 4 4 fffff000000000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff000000000000B8 : treeBlock 8 4 fffff000000000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff000000000000B12 : treeBlock 12 4 fffff000000000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff000000000000B16 : treeBlock 16 4 fffff000000000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff000000000000B20 : treeBlock 20 4 fffff000000000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff000000000000B24 : treeBlock 24 4 fffff000000000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff000000000000B28 : treeBlock 28 4 fffff000000000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff000000000000B32 : treeBlock 32 4 fffff000000000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff000000000000B36 : treeBlock 36 1 fffff000000000000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff000000000000All : treeBlock 0 37 fffff000000000000Check = true := (@treeBlock_merge 0 20 17 fffff000000000000Check (@treeBlock_merge 0 8 12 fffff000000000000Check (@treeBlock_merge 0 4 4 fffff000000000000Check fffff000000000000B0 fffff000000000000B4) (@treeBlock_merge 8 4 8 fffff000000000000Check fffff000000000000B8 (@treeBlock_merge 12 4 4 fffff000000000000Check fffff000000000000B12 fffff000000000000B16))) (@treeBlock_merge 20 8 9 fffff000000000000Check (@treeBlock_merge 20 4 4 fffff000000000000Check fffff000000000000B20 fffff000000000000B24) (@treeBlock_merge 28 4 5 fffff000000000000Check fffff000000000000B28 (@treeBlock_merge 32 4 1 fffff000000000000Check fffff000000000000B32 fffff000000000000B36))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff000000000000Known : Known fffff000000000000Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff000000000000Lower : Lower fffff000000000000Mask fffff000000000000Stock fffff000000000000Goal 6 := by
  have autos : DagMovesOK fffff000000000000Mask fffff000000000000Goal 64 fffff000000000000Moves := dagMovesOfCheck (by decide +kernel)
  apply lowerDag _ _ _ _ autos _ _ _ fffff000000000000Known _ fffff000000000000Roots fffff000000000000All
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · intro c hc; cases hc
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp [fffff000000000000Cuts]

def fffff0000Mask : Word := 0xffff0000
def fffff0000Goal : Word := 0xe8000000
def fffff0000Stock : List Word := [0xaaaa0000, 0xcccc0000, 0xf0f00000, 0xff000000]
def fffff0000Cuts : List Bound := [fff000000Fact]
def fffff0000Fact : Bound := (fffff0000Mask, fffff0000Stock, 5, fffff0000Goal)
def fffff0000Witness : List Witness := [(0xaaaa0000, 27, 26), (0xcccc0000, 27, 25), (0xf0f00000, 29, 25), (0xff000000, 27, 19)]
def fffff0000Forest : Forest := fun i => decodeNode 1 2 0x0 i
def fffff0000States := dagTrace fffff0000Mask fffff0000Stock 4 fffff0000Forest
def fffff0000Links : DagLinks := dagLookupLinks 0x0 0x0 2 1 1 1 0 2
def fffff0000Moves := dagMoves ([] : List (DagMoveRecord 64))
def fffff0000Check := dagCheckNode fffff0000Mask fffff0000Goal none (dagKnownCloses fffff0000Goal fffff0000Cuts) 0 fffff0000States fffff0000Moves fffff0000Links (0,0) (fun _ => [])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff0000Roots : dagCheckRoots fffff0000Mask fffff0000Goal none (dagKnownCloses fffff0000Goal fffff0000Cuts) fffff0000Witness
    (dagRef 0 fffff0000States fffff0000Moves fffff0000Links 0) fffff0000Stock 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff0000All : treeBlock 0 0 fffff0000Check = true := rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff0000Known : Known fffff0000Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) fff000000Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff0000Lower : Lower fffff0000Mask fffff0000Stock fffff0000Goal 5 := by
  have autos : DagMovesOK fffff0000Mask fffff0000Goal 64 fffff0000Moves := dagMovesOfCheck (by decide +kernel)
  apply lowerDag _ _ _ _ autos _ _ _ fffff0000Known _ fffff0000Roots fffff0000All
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · intro c hc; cases hc
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [fffff0000Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b hb
    rcases hb with rfl <;> decide +kernel

def ff0f00000f0f0000Mask : Word := 0xf0f00000f0f0000
def ff0f00000f0f0000Goal : Word := 0xe00000008000000
def ff0f00000f0f0000Stock : List Word := [0xa0a00000a0a0000, 0xc0c00000c0c0000, 0xf0000000f000000, 0xf0f000000000000]
def ff0f00000f0f0000Cuts : List Bound := [ff0000000f000000Fact]
def ff0f00000f0f0000Fact : Bound := (ff0f00000f0f0000Mask, ff0f00000f0f0000Stock, 5, ff0f00000f0f0000Goal)
def ff0f00000f0f0000Witness : List Witness := [(0xa0a00000a0a0000, 27, 26), (0xc0c00000c0c0000, 27, 25), (0xf0000000f000000, 27, 19), (0xf0f000000000000, 57, 25)]
def ff0f00000f0f0000Forest : Forest := fun i => decodeNode 1 2 0x0 i
def ff0f00000f0f0000States := dagTrace ff0f00000f0f0000Mask ff0f00000f0f0000Stock 4 ff0f00000f0f0000Forest
def ff0f00000f0f0000Links : DagLinks := dagLookupLinks 0x0 0x0 2 1 1 1 0 2
def ff0f00000f0f0000Moves := dagMoves ([] : List (DagMoveRecord 64))
def ff0f00000f0f0000Check := dagCheckNode ff0f00000f0f0000Mask ff0f00000f0f0000Goal none (dagKnownCloses ff0f00000f0f0000Goal ff0f00000f0f0000Cuts) 0 ff0f00000f0f0000States ff0f00000f0f0000Moves ff0f00000f0f0000Links (0,0) (fun _ => [])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff0f00000f0f0000Roots : dagCheckRoots ff0f00000f0f0000Mask ff0f00000f0f0000Goal none (dagKnownCloses ff0f00000f0f0000Goal ff0f00000f0f0000Cuts) ff0f00000f0f0000Witness
    (dagRef 0 ff0f00000f0f0000States ff0f00000f0f0000Moves ff0f00000f0f0000Links 0) ff0f00000f0f0000Stock 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff0f00000f0f0000All : treeBlock 0 0 ff0f00000f0f0000Check = true := rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff0f00000f0f0000Known : Known ff0f00000f0f0000Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) ff0000000f000000Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff0f00000f0f0000Lower : Lower ff0f00000f0f0000Mask ff0f00000f0f0000Stock ff0f00000f0f0000Goal 5 := by
  have autos : DagMovesOK ff0f00000f0f0000Mask ff0f00000f0f0000Goal 64 ff0f00000f0f0000Moves := dagMovesOfCheck (by decide +kernel)
  apply lowerDag _ _ _ _ autos _ _ _ ff0f00000f0f0000Known _ ff0f00000f0f0000Roots ff0f00000f0f0000All
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · intro c hc; cases hc
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [ff0f00000f0f0000Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b hb
    rcases hb with rfl <;> decide +kernel

def f3333000033330000Mask : Word := 0x3333000033330000
def f3333000033330000Goal : Word := 0x3200000020000000
def f3333000033330000Stock : List Word := [0x2222000022220000, 0x3030000030300000, 0x3300000033000000, 0x3333000000000000]
def f3333000033330000Fact : Bound := (f3333000033330000Mask, f3333000033330000Stock, 5, f3333000033330000Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f3333000033330000Lower : Lower f3333000033330000Mask f3333000033330000Stock f3333000033330000Goal 5 :=
  dagShiftLower (width := 64) [([(0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)])] ff0f00000f0f0000Lower (by decide +kernel)
def fffff0000ffff0000Mask : Word := 0xffff0000ffff0000
def fffff0000ffff0000Goal : Word := 0xfe800000e8000000
def fffff0000ffff0000Stock : List Word := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]
def fffff0000ffff0000Cuts : List Bound := [fff000000ff000000Fact, faaaa0000aaaa0000Fact, fcccc0000cccc0000Fact, ff0f00000f0f00000Fact, fffff000000000000Fact, fffff0000Fact, ff0f00000f0f0000Fact, f3333000033330000Fact]
def fffff0000ffff0000Fact : Bound := (fffff0000ffff0000Mask, fffff0000ffff0000Stock, 9, fffff0000ffff0000Goal)
def fffff0000ffff0000Witness : List Witness := [(0xaaaa0000aaaa0000, 27, 26), (0xcccc0000cccc0000, 27, 25), (0xf0f00000f0f00000, 29, 25), (0xff000000ff000000, 27, 19), (0xffff000000000000, 55, 23)]
def fffff0000ffff0000Forest : Forest := fun i => decodeNode 6 18 0x30e01633070e24620064b2233307d12031b070e1b6336f0e1c6206cc50192c58071862759881603307d11101c4d8fd16204406c1f44300a0e93f324b0c00f070e026330b0e0862008ccc231b0b0e036200cc5020080407c0 i
def fffff0000ffff0000States := dagTrace fffff0000ffff0000Mask fffff0000ffff0000Stock 8 fffff0000ffff0000Forest
def fffff0000ffff0000Links : DagLinks := dagLookupLinks 0x7ccecdc9336660c0d802d3564ac15829246c8c1182214407ccf81f03c2780d99b0360684d01732a4540a81322604c0981302242d80d001 0x924b206277988143273cc6ca31474c50d00f24021c92c218824c38898cdb62064cccc31b1cc52292c4809c600883d11703f14021c92c11881cc380d881ec38758cdb62058ccd131b08c51801c664b1762759881301c53d11263f45880e0283fd10d93f324b0892c118808c380d8804c380d880ac38258cc762018ccc531b08c526c38958ce362084ccdf31b68c5150334006cb00f04020001f 11 4 12 6 0 5
def fffff0000ffff0000Moves := dagMoves ([] : List (DagMoveRecord 64))
def fffff0000ffff0000Check := dagCheckNode fffff0000ffff0000Mask fffff0000ffff0000Goal none (dagKnownCloses fffff0000ffff0000Goal fffff0000ffff0000Cuts) 39 fffff0000ffff0000States fffff0000ffff0000Moves fffff0000ffff0000Links (0xb0f8623d1a0f8623b1a8fc68370b87460390a8f4643e098ec6c3a0a8dc66390886c301b180e86c1e090782e3f0c0e82e1e0a074703b0c8ec241b088746437098dc301e0b0dc6c3c0c0e4381f0a078383e1986c22390986c663b0b078703a0d078643a0b8dc321d0a874383c0e0786a3d1b0f8703c0d06c6a370e07462390d0e866371a0f0321b0c8e470391b0dc2e1f, 64) (dagTraceTags fffff0000ffff0000Mask 64 (dagTagBases fffff0000ffff0000Stock 0xfdfc999b955975eefbf7ffe5fff7fbbdeec8763f70aff663bc7bfdde7bf8acd35faf13facf0e4f5f 0x7d54c1110950756600010984d0659a9cae985603708be6238274745b0bb828c35aae14a80f0e4559 64) 8 fffff0000ffff0000Forest)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff0000ffff0000Roots : dagCheckRoots fffff0000ffff0000Mask fffff0000ffff0000Goal none (dagKnownCloses fffff0000ffff0000Goal fffff0000ffff0000Cuts) fffff0000ffff0000Witness
    (dagRef 39 fffff0000ffff0000States fffff0000ffff0000Moves fffff0000ffff0000Links 0) fffff0000ffff0000Stock 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff0000ffff0000B0 : treeBlock 0 4 fffff0000ffff0000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff0000ffff0000B4 : treeBlock 4 4 fffff0000ffff0000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff0000ffff0000B8 : treeBlock 8 4 fffff0000ffff0000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff0000ffff0000B12 : treeBlock 12 4 fffff0000ffff0000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff0000ffff0000B16 : treeBlock 16 4 fffff0000ffff0000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff0000ffff0000B20 : treeBlock 20 4 fffff0000ffff0000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff0000ffff0000B24 : treeBlock 24 4 fffff0000ffff0000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff0000ffff0000B28 : treeBlock 28 4 fffff0000ffff0000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff0000ffff0000B32 : treeBlock 32 4 fffff0000ffff0000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff0000ffff0000B36 : treeBlock 36 3 fffff0000ffff0000Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff0000ffff0000All : treeBlock 0 39 fffff0000ffff0000Check = true := (@treeBlock_merge 0 20 19 fffff0000ffff0000Check (@treeBlock_merge 0 8 12 fffff0000ffff0000Check (@treeBlock_merge 0 4 4 fffff0000ffff0000Check fffff0000ffff0000B0 fffff0000ffff0000B4) (@treeBlock_merge 8 4 8 fffff0000ffff0000Check fffff0000ffff0000B8 (@treeBlock_merge 12 4 4 fffff0000ffff0000Check fffff0000ffff0000B12 fffff0000ffff0000B16))) (@treeBlock_merge 20 8 11 fffff0000ffff0000Check (@treeBlock_merge 20 4 4 fffff0000ffff0000Check fffff0000ffff0000B20 fffff0000ffff0000B24) (@treeBlock_merge 28 4 7 fffff0000ffff0000Check fffff0000ffff0000B28 (@treeBlock_merge 32 4 3 fffff0000ffff0000Check fffff0000ffff0000B32 fffff0000ffff0000B36))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff0000ffff0000Known : Known fffff0000ffff0000Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) f3333000033330000Lower) ff0f00000f0f0000Lower) fffff0000Lower) fffff000000000000Lower) ff0f00000f0f00000Lower) fcccc0000cccc0000Lower) faaaa0000aaaa0000Lower) fff000000ff000000Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff0000ffff0000Lower : Lower fffff0000ffff0000Mask fffff0000ffff0000Stock fffff0000ffff0000Goal 9 := by
  have autos : DagMovesOK fffff0000ffff0000Mask fffff0000ffff0000Goal 64 fffff0000ffff0000Moves := dagMovesOfCheck (by decide +kernel)
  apply lowerDag _ _ _ _ autos _ _ _ fffff0000ffff0000Known _ fffff0000ffff0000Roots fffff0000ffff0000All
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · intro c hc; cases hc
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [fffff0000ffff0000Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def fffff00000000Mask : Word := 0xffff00000000
def fffff00000000Goal : Word := 0xe80000000000
def fffff00000000Stock : List Word := [0xaaaa00000000, 0xcccc00000000, 0xf0f000000000, 0xff0000000000]
def fffff00000000Fact : Bound := (fffff00000000Mask, fffff00000000Stock, 5, fffff00000000Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff00000000Lower : Lower fffff00000000Mask fffff00000000Stock fffff00000000Goal 5 :=
  dagShiftLower (width := 64) [([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])] fffff0000Lower (by decide +kernel)
def ff0f0f0f00000000Mask : Word := 0xf0f0f0f00000000
def ff0f0f0f00000000Goal : Word := 0xe00080000000000
def ff0f0f0f00000000Stock : List Word := [0xa0a0a0a00000000, 0xc0c0c0c00000000, 0xf000f0000000000, 0xf0f000000000000]
def ff0f0f0f00000000Fact : Bound := (ff0f0f0f00000000Mask, ff0f0f0f00000000Stock, 5, ff0f0f0f00000000Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff0f0f0f00000000Lower : Lower ff0f0f0f00000000Mask ff0f0f0f00000000Stock ff0f0f0f00000000Goal 5 :=
  dagShiftLower (width := 64) [([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])] ff0f00000f0f0000Lower (by decide +kernel)
def f3333333300000000Mask : Word := 0x3333333300000000
def f3333333300000000Goal : Word := 0x3200200000000000
def f3333333300000000Stock : List Word := [0x2222222200000000, 0x3030303000000000, 0x3300330000000000, 0x3333000000000000]
def f3333333300000000Fact : Bound := (f3333333300000000Mask, f3333333300000000Stock, 5, f3333333300000000Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f3333333300000000Lower : Lower f3333333300000000Mask f3333333300000000Stock f3333333300000000Goal 5 :=
  dagShiftLower (width := 64) [([(0xc3c300000000c3c3, 0), (0xc0c000000000c0c, 2), (0x30300000, 14), (0xc3c30000, 16), (0xc0c0000, 18)], [(0x303000000000, 18), (0xc3c300000000, 16), (0xc0c00000000, 14), (0x3030000000003030, 2)])] ff0f00000f0f0000Lower (by decide +kernel)
def fffffffff00000000Mask : Word := 0xffffffff00000000
def fffffffff00000000Goal : Word := 0xfe80e80000000000
def fffffffff00000000Stock : List Word := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]
def fffffffff00000000Fact : Bound := (fffffffff00000000Mask, fffffffff00000000Stock, 9, fffffffff00000000Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffff00000000Lower : Lower fffffffff00000000Mask fffffffff00000000Stock fffffffff00000000Goal 9 :=
  dagShiftLower (width := 64) [([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])] fffff0000ffff0000Lower (by decide +kernel)
def ff0f0f0f0f0f0f0fMask : Word := 0xf0f0f0f0f0f0f0f
def ff0f0f0f0f0f0f0fGoal : Word := 0xe00080008000000
def ff0f0f0f0f0f0f0fStock : List Word := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]
def ff0f0f0f0f0f0f0fCuts : List Bound := [ff000f000f000f00Fact]
def ff0f0f0f0f0f0f0fFact : Bound := (ff0f0f0f0f0f0f0fMask, ff0f0f0f0f0f0f0fStock, 8, ff0f0f0f0f0f0f0fGoal)
def ff0f0f0f0f0f0f0fWitness : List Witness := [(0xa0a0a0a0a0a0a0a, 27, 26), (0xc0c0c0c0c0c0c0c, 27, 25), (0xf000f000f000f00, 27, 19), (0xf0f00000f0f0000, 27, 11), (0xf0f0f0f00000000, 43, 11)]
def ff0f0f0f0f0f0f0fForest : Forest := fun i => decodeNode 1 2 0x0 i
def ff0f0f0f0f0f0f0fStates := dagTrace ff0f0f0f0f0f0f0fMask ff0f0f0f0f0f0f0fStock 7 ff0f0f0f0f0f0f0fForest
def ff0f0f0f0f0f0f0fLinks : DagLinks := dagLookupLinks 0x0 0x0 2 1 1 1 0 2
def ff0f0f0f0f0f0f0fMoves := dagMoves ([] : List (DagMoveRecord 64))
def ff0f0f0f0f0f0f0fCheck := dagCheckNode ff0f0f0f0f0f0f0fMask ff0f0f0f0f0f0f0fGoal none (dagKnownCloses ff0f0f0f0f0f0f0fGoal ff0f0f0f0f0f0f0fCuts) 0 ff0f0f0f0f0f0f0fStates ff0f0f0f0f0f0f0fMoves ff0f0f0f0f0f0f0fLinks (0,0) (fun _ => [])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff0f0f0f0f0f0f0fRoots : dagCheckRoots ff0f0f0f0f0f0f0fMask ff0f0f0f0f0f0f0fGoal none (dagKnownCloses ff0f0f0f0f0f0f0fGoal ff0f0f0f0f0f0f0fCuts) ff0f0f0f0f0f0f0fWitness
    (dagRef 0 ff0f0f0f0f0f0f0fStates ff0f0f0f0f0f0f0fMoves ff0f0f0f0f0f0f0fLinks 0) ff0f0f0f0f0f0f0fStock 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff0f0f0f0f0f0f0fAll : treeBlock 0 0 ff0f0f0f0f0f0f0fCheck = true := rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff0f0f0f0f0f0f0fKnown : Known ff0f0f0f0f0f0f0fCuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) ff000f000f000f00Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ff0f0f0f0f0f0f0fLower : Lower ff0f0f0f0f0f0f0fMask ff0f0f0f0f0f0f0fStock ff0f0f0f0f0f0f0fGoal 8 := by
  have autos : DagMovesOK ff0f0f0f0f0f0f0fMask ff0f0f0f0f0f0f0fGoal 64 ff0f0f0f0f0f0f0fMoves := dagMovesOfCheck (by decide +kernel)
  apply lowerDag _ _ _ _ autos _ _ _ ff0f0f0f0f0f0f0fKnown _ ff0f0f0f0f0f0f0fRoots ff0f0f0f0f0f0f0fAll
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · intro c hc; cases hc
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [ff0f0f0f0f0f0f0fCuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b hb
    rcases hb with rfl <;> decide +kernel

def f3333333333333333Mask : Word := 0x3333333333333333
def f3333333333333333Goal : Word := 0x3200200020000000
def f3333333333333333Stock : List Word := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]
def f3333333333333333Fact : Bound := (f3333333333333333Mask, f3333333333333333Stock, 8, f3333333333333333Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f3333333333333333Lower : Lower f3333333333333333Mask f3333333333333333Stock f3333333333333333Goal 8 :=
  dagShiftLower (width := 64) [([(0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)])] ff0f0f0f0f0f0f0fLower (by decide +kernel)
def f5555555555555555Mask : Word := 0x5555555555555555
def f5555555555555555Goal : Word := 0x5400400040000000
def f5555555555555555Stock : List Word := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]
def f5555555555555555Fact : Bound := (f5555555555555555Mask, f5555555555555555Stock, 8, f5555555555555555Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f5555555555555555Lower : Lower f5555555555555555Mask f5555555555555555Stock f5555555555555555Goal 8 :=
  dagShiftLower (width := 64) [([(0x8181818181818181, 0), (0x2020202020202020, 1), (0x808080808080808, 2), (0x202020202020202, 3)], [(0x4040404040404040, 3), (0x1010101010101010, 2), (0x404040404040404, 1)])] ff0f0f0f0f0f0f0fLower (by decide +kernel)
def fffffffffMask : Word := 0xffffffff
def fffffffffGoal : Word := 0xe8000000
def fffffffffStock : List Word := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
def fffffffffCuts : List Bound := [fff00ff00Fact]
def fffffffffFact : Bound := (fffffffffMask, fffffffffStock, 6, fffffffffGoal)
def fffffffffWitness : List Witness := [(0xaaaaaaaa, 27, 26), (0xcccccccc, 27, 25), (0xf0f0f0f0, 29, 25), (0xff00ff00, 27, 19), (0xffff0000, 27, 11)]
def fffffffffForest : Forest := fun i => decodeNode 1 2 0x0 i
def fffffffffStates := dagTrace fffffffffMask fffffffffStock 5 fffffffffForest
def fffffffffLinks : DagLinks := dagLookupLinks 0x0 0x0 2 1 1 1 0 2
def fffffffffMoves := dagMoves ([] : List (DagMoveRecord 64))
def fffffffffCheck := dagCheckNode fffffffffMask fffffffffGoal none (dagKnownCloses fffffffffGoal fffffffffCuts) 0 fffffffffStates fffffffffMoves fffffffffLinks (0,0) (fun _ => [])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffRoots : dagCheckRoots fffffffffMask fffffffffGoal none (dagKnownCloses fffffffffGoal fffffffffCuts) fffffffffWitness
    (dagRef 0 fffffffffStates fffffffffMoves fffffffffLinks 0) fffffffffStock 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffAll : treeBlock 0 0 fffffffffCheck = true := rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffKnown : Known fffffffffCuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) fff00ff00Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffLower : Lower fffffffffMask fffffffffStock fffffffffGoal 6 := by
  have autos : DagMovesOK fffffffffMask fffffffffGoal 64 fffffffffMoves := dagMovesOfCheck (by decide +kernel)
  apply lowerDag _ _ _ _ autos _ _ _ fffffffffKnown _ fffffffffRoots fffffffffAll
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · intro c hc; cases hc
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [fffffffffCuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b hb
    rcases hb with rfl <;> decide +kernel

def fffff0000ffffMask : Word := 0xffff0000ffff
def fffff0000ffffGoal : Word := 0xe80000000000
def fffff0000ffffStock : List Word := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]
def fffff0000ffffFact : Bound := (fffff0000ffffMask, fffff0000ffffStock, 6, fffff0000ffffGoal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffff0000ffffLower : Lower fffff0000ffffMask fffff0000ffffStock fffff0000ffffGoal 6 :=
  dagShiftLower (width := 64) [([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])] fffffffffLower (by decide +kernel)
def fffffffffffffffffMask : Word := 0xffffffffffffffff
def fffffffffffffffffGoal : Word := 0xfe80e800e8000000
def fffffffffffffffffStock : List Word := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def fffffffffffffffffCuts : List Bound := [fff00ff00ff00ff00Fact, faaaaaaaaaaaaaaaaFact, fccccccccccccccccFact, ff0f0f0f0f0f0f0f0Fact, fffff0000ffff0000Fact, fffffffff00000000Fact, ff0f0f0f0f0f0f0fFact, f3333333333333333Fact, f5555555555555555Fact, fffffffffFact, fffff0000ffffFact]
def fffffffffffffffffFact : Bound := (fffffffffffffffffMask, fffffffffffffffffStock, 12, fffffffffffffffffGoal)
def fffffffffffffffffWitness : List Witness := [(0xaaaaaaaaaaaaaaaa, 27, 26), (0xcccccccccccccccc, 27, 25), (0xf0f0f0f0f0f0f0f0, 29, 25), (0xff00ff00ff00ff00, 27, 19), (0xffff0000ffff0000, 27, 11), (0xffffffff00000000, 43, 11)]
def fffffffffffffffffForest : Forest := fun i => decodeNode 9 22 0x1e880161cbfc04f0319941c0370319941064d04007c0d870ff319bfc666ff019bfd87e017a23f5870017a23ecc7e019283e4c66017a23c1872f361c3ccc66f3199bcd87ef07a23c5870f0310005e88e7496bad258eb013bac650ea49fb9de88e849639c67e0192837925ae249638804ee2194385296de92837d258de1998064a0cd7a2b41e88d0928361870d81a1341e8ad47a235007ed41a0340c98d100e34407ed07a5b364a0ce7a2334636017a22e9872c761c31cc66c7199b1d87eba7a2315870ba7a230cc7eba928304c66ba7a22ed870be61faede88bc61c2ecc40ba18a005e889d496ad5258b5193ad4050b449fa75e88b2496275870ab4962b0c4eac310ab0c40ac00e2acc7e9d928291e88a531fa94c42a5310294038a4313a75e889e19428527e9e7a227d2589e31027407e0192820125a9849626064e9801425d296809282552588061c2392588f313a3cc428f31023c0388e325a02ab887928220c9688310a20c408800e21cc4e80928204650844a5a064a082496204c40800198064a05b7a29c9e887200e1ecc7e729281dd870771989dc084727a29cde887319f9cc080727a596e4a0707a216e4a0697a21a8c7e6a3109a8c406a00e1a4c965baae18a4a06332598cc426331018c0386231f96e4a05c1a017de965c928175e885c31016c036019280d9e8a4d7a21340505649f9364a05261c148c6252021135e8a4e7a2138c7e4e020135e963692812de8836928111e884549f91525a45496114050444a58daab83d9280f92963e4968f92583e0140f527e369280dc6803a7a58de4a0387a20dd25836007805e880261c8c1870303198c06663061f809e882e61c009e882c31f80a4a02a319809e882461c09d87e247a209587024310009e881e19408527e1e7a207d2581e19f80a4a01819406d296189280652581819980a4a0121a0055e961292804de881218d809e880361c03d87e037a2035870037a202cc7e03928024c66037a201187e047a20158700431000c6280200400407e00 i
def fffffffffffffffffStates := dagTrace fffffffffffffffffMask fffffffffffffffffStock 11 fffffffffffffffffForest
def fffffffffffffffffLinks : DagLinks := dagLookupLinks 0x82aa046808a020800a0008001fe27d65f237bcdec3786ddb67469ce37219c536fd9b966e41b726dc1b706c1dad369d99da668d9a066819a0659194264c5903629987361c187061c183460498015f4d7765d0d7315cc17305cc17035c017005c016c45b016c05a8964658c560356995465501522548152052dd48350994114f8d3d14e8d3734dc13524d053134ad921a478d1e047811e0469118245c514344c513044c113044c10f443490c143010c043010c042110624145050410504040c50033e98f733dc0f703dc0f343c48f013b4cec13b00ec03b00ec03a10e623944e503940e503940e1437c8de13780dd13740dc1364cd36340ccf133c0cf03348cd03340cd0328cca03280ca03190c062fc4bc32ec4bb02ec0bb02ec0b742d48b412d00b402d00b402c10ae22b44ad02b04ac02ac4a8328989f327849e027809c227009c027009932640990264095423d88e122cc8a122808a022808a0219084220c483020c083020c07f41f487c11f007b11ec07a11dcc7161ad86b01a486901a4062717cc59616045531504513138c4e013084b1120c426104441010044000fc43c30ec43b00e843a00e443630d443500d043400cc43030b4c2d00ac82a109cc27009842600944241090024008c4203069810a007c001 0x7ebd11f293f7ba4b1ca63f6e189d966204d8cfcfc3272c8c6c683147b24b1b6627651880fa3272c0c6c66314838c9a0a31a838cca0831a828cca083267aa4b1b4627649880f83272b8c6c6431484009e0c01b81803d903142a803c620087a24b0f4027180021e692c68189d8e62084b0e604c388098cde4620800ccd9e31b630c51fe03338806c9800f178021e2c386724cd8a92c3818cc96627171881faf447da4fde092c7718fd9a6276218817033f378c9c9431b168c5186620248c6c583147dbd11c033f610c512c03f21803c560086098808431b150c51f3250748d2d8031459812c7800f148021e2f446fa4fd7e92c4a98fc766271418817c92c139881ecc397ab0e1e86335e9881e63331c8c6c4c3145e30e07093312a4b1e2f447424fd7692c5918fc6e627121881eef447930fde0c387398fdbc6335d18816233f4a0ccc6c31b118c51d0c38370ccc4431476a4b5d892c75809c42008750ca0400080f9881d0f44498cfc3c314773d11d293f73a4b11a03f34009c3a0086fb0e0ce3330e0c51c892d71a4b1c40270d8021c23280d0020326206fc9416034b0c0c51cb25070252dbc92c55012cc20270b80219d250460d2c2c3146c1931b32506c30e1a40316b3d15aaf446a00fc2a008691931a201c6dbd15b4f446b8d09a63406800fc280080998819d250548d2c243146e49419ef4b66bd114604b4300fc2200862bd118293f5fa4b10a63f30189c206205f24b01e6206530e592c386418cd7a620638cccbc31b070c5178c382ea4cc1a92c62bd118693f5da4b14463f2e189c1862005988186f44418cfc1431404988183250500d2c103145e3d110493f03a4b17cc380318800ac385e3d113e93f0224b17ef445eb0fd76c384f18fd0263301988196f446330fd88c386118fd806335d18813a33f400cccb631b010c5164c3854a4cd4492c5ba4b56c92c5a8c9d42314501881680284fb0e164f445824fd3c92c578ca15e92c57189d5a62156188160c3855807150328543d114e63f5318854a62054c9414801c4fb0e1423284fbd1144f445024fd3c92c5c3d116693f58a4b15463f51989d3a6204ab0e11893342a4b13492d4ca4b130327420c51066204b80a104c384ac9412694b40a4b1243284924b1226274818851e62049b0e11c01c458ca11725045192d126214418811955c43807104c38420ca10525042c9410694b40a4b1372504b252d2892c46992d0c627401880e125033a52cc092c3c0d30ee04c3d8070f32503c30e0ee3313abd14e8f44398cfcbe3143ebd14f8f443d18fcbc6203b0108e40402eb0e0e125037252cb892c368ca0daf443618fcd6621351880dd250348070cc328334940ca64b321884c662033d570c401c2ec940be3402ec940c12502f3d2cb8f443f4940e2f4b37bd10d064b3098fcb662025c94084c4b1db0e0a634c290130ac0282a4940a6c382918c4a0f4527bd109c63f1d1880b0f452bbd10aa93f1ca4b0a204226810070f4425c94092c4b1bb0e090334243d108e93f2324b48a92c24c94088028208cd08325020252c7e92d1f24b08555c1e80a0712501d0d00712501dc94072f4b1bbd10b3250263d2c94f4421a52c7893f1b24b05cf441524fc5092c0e18fc2c6270818804e92c07988066c391930e062633131880603330a0c6c1c31412b0e02693306a4b05cf441624fc4892c1118fc2462706188016620163d103433f050c50126201549404034b040c504af440ca4fc0e92c13b0e00c62002b0e04af440fa4fc0892c143d104cc3f1230e03c63f0c18cc066200fb0e0423280fbd1044f441024fc3c92c0cb0e0363280cc940392500d252c3092c09c9402a34009c9402d2500a3d2c24f4406bd101293f03a4b01ec380318800ac3806bd101693f0224b016f4404c9400af4402bd100ef440330fc08c38083d101cc3f0630e01463f0418cc066201a3d105ec3f16b0e05663f1498cc466200e8cfc2e333088c6c04314853d11fcc3f7e30e1f463f7c18cdde620730cfdba333660c6d723144e00fcfe0332d006c6a00f0080200003f 14 4 13 9 0 5
def fffffffffffffffffMoves := dagMoves ([] : List (DagMoveRecord 64))
def fffffffffffffffffCheck := dagCheckNode fffffffffffffffffMask fffffffffffffffffGoal none (dagKnownCloses fffffffffffffffffGoal fffffffffffffffffCuts) 267 fffffffffffffffffStates fffffffffffffffffMoves fffffffffffffffffLinks (0x70f8121b1986c4c370c078283c140f0301b1a8b4161f108e4142e1a0f4142b198e4241e0e0f04c2e118ac583c188e4522b0586c2a1d0b8dc162b1b0f8703a0e0781c2e1b0dc703c0e0741c1e0b078543a160b4321b150ac1e1f0c8e452390b87c343a0d0786a3d0d06c1a1d160b84a2d148b47039068b4542e138dc1e2f138bc6a37190e8683c198ec321d0986c6637, 64) (dagTraceTags fffffffffffffffffMask 64 (dagTagBases fffffffffffffffffStock 0x96befcf71ad4fff9ff6b9bbbf5ff127fefffff7dfffffdbe9ed9d1afe92defd5f95566fe773a87eb71ee2fc28fe77bcf 0x32aa7c331a44f6f92d8b89bba4be107fcb54965ddfdbbd049488d1aee925cbd0b05762e6733a07ab60e22fc005e56bcf 64) 11 fffffffffffffffffForest)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffRoots : dagCheckRoots fffffffffffffffffMask fffffffffffffffffGoal none (dagKnownCloses fffffffffffffffffGoal fffffffffffffffffCuts) fffffffffffffffffWitness
    (dagRef 267 fffffffffffffffffStates fffffffffffffffffMoves fffffffffffffffffLinks 0) fffffffffffffffffStock 11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB0 : treeBlock 0 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB4 : treeBlock 4 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB8 : treeBlock 8 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB12 : treeBlock 12 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB16 : treeBlock 16 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB20 : treeBlock 20 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB24 : treeBlock 24 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB28 : treeBlock 28 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB32 : treeBlock 32 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB36 : treeBlock 36 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB40 : treeBlock 40 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB44 : treeBlock 44 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB48 : treeBlock 48 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB52 : treeBlock 52 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB56 : treeBlock 56 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB60 : treeBlock 60 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB64 : treeBlock 64 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB68 : treeBlock 68 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB72 : treeBlock 72 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB76 : treeBlock 76 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB80 : treeBlock 80 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB84 : treeBlock 84 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB88 : treeBlock 88 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB92 : treeBlock 92 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB96 : treeBlock 96 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB100 : treeBlock 100 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB104 : treeBlock 104 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB108 : treeBlock 108 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB112 : treeBlock 112 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB116 : treeBlock 116 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB120 : treeBlock 120 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB124 : treeBlock 124 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB128 : treeBlock 128 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB132 : treeBlock 132 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB136 : treeBlock 136 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB140 : treeBlock 140 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB144 : treeBlock 144 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB148 : treeBlock 148 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB152 : treeBlock 152 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB156 : treeBlock 156 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB160 : treeBlock 160 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB164 : treeBlock 164 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB168 : treeBlock 168 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB172 : treeBlock 172 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB176 : treeBlock 176 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB180 : treeBlock 180 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB184 : treeBlock 184 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB188 : treeBlock 188 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB192 : treeBlock 192 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB196 : treeBlock 196 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB200 : treeBlock 200 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB204 : treeBlock 204 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB208 : treeBlock 208 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB212 : treeBlock 212 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB216 : treeBlock 216 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB220 : treeBlock 220 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB224 : treeBlock 224 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB228 : treeBlock 228 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB232 : treeBlock 232 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB236 : treeBlock 236 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB240 : treeBlock 240 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB244 : treeBlock 244 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB248 : treeBlock 248 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB252 : treeBlock 252 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB256 : treeBlock 256 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB260 : treeBlock 260 4 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffB264 : treeBlock 264 3 fffffffffffffffffCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffAll : treeBlock 0 267 fffffffffffffffffCheck = true := (@treeBlock_merge 0 132 135 fffffffffffffffffCheck (@treeBlock_merge 0 64 68 fffffffffffffffffCheck (@treeBlock_merge 0 32 32 fffffffffffffffffCheck (@treeBlock_merge 0 16 16 fffffffffffffffffCheck (@treeBlock_merge 0 8 8 fffffffffffffffffCheck (@treeBlock_merge 0 4 4 fffffffffffffffffCheck fffffffffffffffffB0 fffffffffffffffffB4) (@treeBlock_merge 8 4 4 fffffffffffffffffCheck fffffffffffffffffB8 fffffffffffffffffB12)) (@treeBlock_merge 16 8 8 fffffffffffffffffCheck (@treeBlock_merge 16 4 4 fffffffffffffffffCheck fffffffffffffffffB16 fffffffffffffffffB20) (@treeBlock_merge 24 4 4 fffffffffffffffffCheck fffffffffffffffffB24 fffffffffffffffffB28))) (@treeBlock_merge 32 16 16 fffffffffffffffffCheck (@treeBlock_merge 32 8 8 fffffffffffffffffCheck (@treeBlock_merge 32 4 4 fffffffffffffffffCheck fffffffffffffffffB32 fffffffffffffffffB36) (@treeBlock_merge 40 4 4 fffffffffffffffffCheck fffffffffffffffffB40 fffffffffffffffffB44)) (@treeBlock_merge 48 8 8 fffffffffffffffffCheck (@treeBlock_merge 48 4 4 fffffffffffffffffCheck fffffffffffffffffB48 fffffffffffffffffB52) (@treeBlock_merge 56 4 4 fffffffffffffffffCheck fffffffffffffffffB56 fffffffffffffffffB60)))) (@treeBlock_merge 64 32 36 fffffffffffffffffCheck (@treeBlock_merge 64 16 16 fffffffffffffffffCheck (@treeBlock_merge 64 8 8 fffffffffffffffffCheck (@treeBlock_merge 64 4 4 fffffffffffffffffCheck fffffffffffffffffB64 fffffffffffffffffB68) (@treeBlock_merge 72 4 4 fffffffffffffffffCheck fffffffffffffffffB72 fffffffffffffffffB76)) (@treeBlock_merge 80 8 8 fffffffffffffffffCheck (@treeBlock_merge 80 4 4 fffffffffffffffffCheck fffffffffffffffffB80 fffffffffffffffffB84) (@treeBlock_merge 88 4 4 fffffffffffffffffCheck fffffffffffffffffB88 fffffffffffffffffB92))) (@treeBlock_merge 96 16 20 fffffffffffffffffCheck (@treeBlock_merge 96 8 8 fffffffffffffffffCheck (@treeBlock_merge 96 4 4 fffffffffffffffffCheck fffffffffffffffffB96 fffffffffffffffffB100) (@treeBlock_merge 104 4 4 fffffffffffffffffCheck fffffffffffffffffB104 fffffffffffffffffB108)) (@treeBlock_merge 112 8 12 fffffffffffffffffCheck (@treeBlock_merge 112 4 4 fffffffffffffffffCheck fffffffffffffffffB112 fffffffffffffffffB116) (@treeBlock_merge 120 4 8 fffffffffffffffffCheck fffffffffffffffffB120 (@treeBlock_merge 124 4 4 fffffffffffffffffCheck fffffffffffffffffB124 fffffffffffffffffB128)))))) (@treeBlock_merge 132 68 67 fffffffffffffffffCheck (@treeBlock_merge 132 32 36 fffffffffffffffffCheck (@treeBlock_merge 132 16 16 fffffffffffffffffCheck (@treeBlock_merge 132 8 8 fffffffffffffffffCheck (@treeBlock_merge 132 4 4 fffffffffffffffffCheck fffffffffffffffffB132 fffffffffffffffffB136) (@treeBlock_merge 140 4 4 fffffffffffffffffCheck fffffffffffffffffB140 fffffffffffffffffB144)) (@treeBlock_merge 148 8 8 fffffffffffffffffCheck (@treeBlock_merge 148 4 4 fffffffffffffffffCheck fffffffffffffffffB148 fffffffffffffffffB152) (@treeBlock_merge 156 4 4 fffffffffffffffffCheck fffffffffffffffffB156 fffffffffffffffffB160))) (@treeBlock_merge 164 16 20 fffffffffffffffffCheck (@treeBlock_merge 164 8 8 fffffffffffffffffCheck (@treeBlock_merge 164 4 4 fffffffffffffffffCheck fffffffffffffffffB164 fffffffffffffffffB168) (@treeBlock_merge 172 4 4 fffffffffffffffffCheck fffffffffffffffffB172 fffffffffffffffffB176)) (@treeBlock_merge 180 8 12 fffffffffffffffffCheck (@treeBlock_merge 180 4 4 fffffffffffffffffCheck fffffffffffffffffB180 fffffffffffffffffB184) (@treeBlock_merge 188 4 8 fffffffffffffffffCheck fffffffffffffffffB188 (@treeBlock_merge 192 4 4 fffffffffffffffffCheck fffffffffffffffffB192 fffffffffffffffffB196))))) (@treeBlock_merge 200 32 35 fffffffffffffffffCheck (@treeBlock_merge 200 16 16 fffffffffffffffffCheck (@treeBlock_merge 200 8 8 fffffffffffffffffCheck (@treeBlock_merge 200 4 4 fffffffffffffffffCheck fffffffffffffffffB200 fffffffffffffffffB204) (@treeBlock_merge 208 4 4 fffffffffffffffffCheck fffffffffffffffffB208 fffffffffffffffffB212)) (@treeBlock_merge 216 8 8 fffffffffffffffffCheck (@treeBlock_merge 216 4 4 fffffffffffffffffCheck fffffffffffffffffB216 fffffffffffffffffB220) (@treeBlock_merge 224 4 4 fffffffffffffffffCheck fffffffffffffffffB224 fffffffffffffffffB228))) (@treeBlock_merge 232 16 19 fffffffffffffffffCheck (@treeBlock_merge 232 8 8 fffffffffffffffffCheck (@treeBlock_merge 232 4 4 fffffffffffffffffCheck fffffffffffffffffB232 fffffffffffffffffB236) (@treeBlock_merge 240 4 4 fffffffffffffffffCheck fffffffffffffffffB240 fffffffffffffffffB244)) (@treeBlock_merge 248 8 11 fffffffffffffffffCheck (@treeBlock_merge 248 4 4 fffffffffffffffffCheck fffffffffffffffffB248 fffffffffffffffffB252) (@treeBlock_merge 256 4 7 fffffffffffffffffCheck fffffffffffffffffB256 (@treeBlock_merge 260 4 3 fffffffffffffffffCheck fffffffffffffffffB260 fffffffffffffffffB264)))))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffKnown : Known fffffffffffffffffCuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) fffff0000ffffLower) fffffffffLower) f5555555555555555Lower) f3333333333333333Lower) ff0f0f0f0f0f0f0fLower) fffffffff00000000Lower) fffff0000ffff0000Lower) ff0f0f0f0f0f0f0f0Lower) fccccccccccccccccLower) faaaaaaaaaaaaaaaaLower) fff00ff00ff00ff00Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fffffffffffffffffLower : Lower fffffffffffffffffMask fffffffffffffffffStock fffffffffffffffffGoal 12 := by
  have autos : DagMovesOK fffffffffffffffffMask fffffffffffffffffGoal 64 fffffffffffffffffMoves := dagMovesOfCheck (by decide +kernel)
  apply lowerDag _ _ _ _ autos _ _ _ fffffffffffffffffKnown _ fffffffffffffffffRoots fffffffffffffffffAll
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · intro c hc; cases hc
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [fffffffffffffffffCuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def tableFunction (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4269860864 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.and, [4, 5]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [3, 7]⟩,
    ⟨.and, [2, 8]⟩,
    ⟨.or, [2, 8]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.and, [3, 12]⟩,
    ⟨.or, [6, 14]⟩,
    ⟨.and, [13, 15]⟩,
    ⟨.and, [9, 16]⟩], 17⟩

lemma witness_mono : Monotone2 witness := by simp [Monotone2, witness]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma witness_eval : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = tableFunction x := by
  decide +kernel

lemma large_enough {s : ℕ} (hs : 12 ≤ s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = tableFunction x :=
  ⟨witness, witness_mono, hs, witness_eval⟩

def naturalRaw : List (BitVec 64) :=
  [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
set_option maxRecDepth 10000 in
theorem minSize (s : Nat) (h : HasCircuitSize 6 tableFunction s) : 12 ≤ s :=
  hcsLower (n := 6) naturalRaw (0xfe80e800e8000000 : BitVec 64) 12 tableFunction
    (by decide +kernel) (by decide +kernel) fffffffffffffffffLower s h
end PEqualNP.Outside.L_meta_12056_aux

open PEqualNP.Outside.L_meta_12056_aux in
theorem PEqualNP.Outside.L_meta_12056 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269860864 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269860864 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s h
  exact large_enough (minSize s h)
