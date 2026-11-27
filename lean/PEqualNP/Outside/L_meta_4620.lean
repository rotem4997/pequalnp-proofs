import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_4620

abbrev Wire := ℕ × Bool × Bool
abbrev Row := GateOp × List Wire

def flag (b : Bool) (w : Wire) : Bool := bif b then w.2.2 else w.2.1

def readWire (v : Option Bool) (w : Wire) : ℕ :=
  v.elim w.1 fun b => bif flag b w then 0 else w.1 + 1

def decode (v : Option Bool) (r : Row) : Gate := ⟨r.1, r.2.map (readWire v)⟩

def clamp (k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (min k)⟩

def link (p q a t : ℕ) : Prop := t = a + 1 ∨ t = 0 ∧ (a = p ∨ a = q)

def linked (p q : ℕ) (g h : Gate) : Prop :=
  g.op = h.op ∧ List.Forall₂ (link p q) g.inputs h.inputs

def lawful (p q : Bool → ℕ) (w : Wire) : Prop :=
  ∀ b, flag b w = true → w.1 = min 18 (p b) ∨ w.1 = min 18 (q b)

lemma encodeOne {p q a t : ℕ} (h : link p q a t) :
    (bif decide (t = 0) then 0 else min 18 a + 1) = min 19 t ∧
    (decide (t = 0) = true → min 18 a = min 18 p ∨ min 18 a = min 18 q) := by
  rcases h with rfl | ⟨rfl, rfl | rfl⟩ <;> simp
  omega

lemma packInputs (p q : Bool → ℕ) {xs ys zs : List ℕ}
    (hy : List.Forall₂ (link (p false) (q false)) xs ys)
    (hz : List.Forall₂ (link (p true) (q true)) xs zs) :
    ∃ ws : List Wire, ws.map (readWire none) = xs.map (min 18) ∧
      ws.map (readWire (some false)) = ys.map (min 19) ∧
      ws.map (readWire (some true)) = zs.map (min 19) ∧ ∀ w ∈ ws, lawful p q w := by
  induction hy generalizing zs with
  | nil =>
    cases hz
    exact ⟨[], rfl, rfl, rfl, by simp⟩
  | @cons x y xs ys hxy _ ih =>
    cases hz with
    | @cons _ z _ zs hxz hzs =>
      obtain ⟨ws, hn, hf, ht, hw⟩ := ih hzs
      let w : Wire := (min 18 x, decide (y = 0), decide (z = 0))
      obtain ⟨fy, ly⟩ := encodeOne hxy
      obtain ⟨fz, lz⟩ := encodeOne hxz
      refine ⟨w :: ws, congrArg₂ List.cons rfl hn,
        congrArg₂ List.cons fy hf, congrArg₂ List.cons fz ht, ?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · intro b
        cases b
        · exact ly
        · exact lz
      · exact hw _ hv

lemma packRows (p q : Bool → ℕ) {xs ys zs : List Gate}
    (hy : List.Forall₂ (linked (p false) (q false)) xs ys)
    (hz : List.Forall₂ (linked (p true) (q true)) xs zs) :
    ∃ rows : List Row, rows.map (decode none) = xs.map (clamp 18) ∧
      rows.map (decode (some false)) = ys.map (clamp 19) ∧
      rows.map (decode (some true)) = zs.map (clamp 19) ∧
      ∀ r ∈ rows, ∀ w ∈ r.2, lawful p q w := by
  induction hy generalizing zs with
  | nil =>
    cases hz
    exact ⟨[], rfl, rfl, rfl, by simp⟩
  | @cons x y xs ys hxy _ ih =>
    cases hz with
    | @cons _ z _ zs hxz hzs =>
      obtain ⟨rows, hn, hf, ht, hsafe⟩ := ih hzs
      obtain ⟨ws, wn, wf, wt, wsafe⟩ := packInputs p q hxy.2 hxz.2
      let r : Row := (x.op, ws)
      refine ⟨r :: rows, congrArg₂ List.cons ?_ hn,
        congrArg₂ List.cons ?_ hf, congrArg₂ List.cons ?_ ht, ?_⟩
      · exact congrArg (Gate.mk x.op) wn
      · exact congrArg₂ Gate.mk hxy.1 wf
      · exact congrArg₂ Gate.mk hxz.1 wt
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact wsafe
        · exact hsafe _ hs

end PEqualNP.Outside.L_meta_4620

open PEqualNP.Outside.L_meta_4620

theorem PEqualNP.Outside.L_meta_4620 : have x1 : ℕ → ℕ → PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 x2 : ℕ) (x3 x4 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = x4.op ∧ List.Forall₂ (fun (x5 x6 : ℕ) => x6 = x5 + (1 : ℕ) ∨ x6 = (0 : ℕ) ∧ (x5 = x1 ∨ x5 = x2)) x3.inputs x4.inputs; have x2 : Option Bool → PEqualNP.CircuitLowerBounds.GateOp × List (ℕ × Bool × Bool) → PEqualNP.CircuitLowerBounds.Gate := fun (x2 : Option Bool) (x3 : PEqualNP.CircuitLowerBounds.GateOp × List (ℕ × Bool × Bool)) => { op := x3.1, inputs := List.map (fun (x4 : ℕ × Bool × Bool) => x2.elim x4.1 fun (x5 : Bool) => bif bif x5 then x4.2.2 else x4.2.1 then (0 : ℕ) else x4.1 + (1 : ℕ)) x3.2 : PEqualNP.CircuitLowerBounds.Gate }; ∀ (x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 : Bool → List PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : Bool → ℕ), (∀ (x7 : Bool), List.Forall₂ (x1 (x5 x7) (x6 x7)) x3 (x4 x7)) → ∃ (x8 : List (PEqualNP.CircuitLowerBounds.GateOp × List (ℕ × Bool × Bool))), List.map (x2 Option.none) x8 = List.map (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => { op := x9.op, inputs := List.map (Min.min (18 : ℕ)) x9.inputs : PEqualNP.CircuitLowerBounds.Gate }) x3 ∧ (∀ (x9 : Bool), List.map (x2 (Option.some x9)) x8 = List.map (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => { op := x10.op, inputs := List.map (Min.min (19 : ℕ)) x10.inputs : PEqualNP.CircuitLowerBounds.Gate }) (x4 x9)) ∧ ∀ (x9 : Bool), ∀ x10 ∈ x8, ∀ x12 ∈ x10.2, (bif x9 then x12.2.2 else x12.2.1) = Bool.true → x12.1 = Min.min (18 : ℕ) (x5 x9) ∨ x12.1 = Min.min (18 : ℕ) (x6 x9) := by
  dsimp only
  intro xs s p q h
  obtain ⟨rows, hn, hf, ht, hw⟩ := packRows p q (xs := xs) (ys := s false) (zs := s true) (h false) (h true)
  refine ⟨rows, hn, ?_, ?_⟩
  · intro b
    cases b
    · exact hf
    · exact ht
  · intro b r hr w hw'
    exact hw r hr w hw' b
