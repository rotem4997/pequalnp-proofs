import PEqualNP.Defs
import Mathlib.Tactic

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4518

def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun a g => a ++ [value g a]) w

def rename (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map f⟩

theorem runLen (gs : List Gate) (u : List Bool) : (run gs u).length = u.length+gs.length := by
  induction gs generalizing u with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (u++[value g u])).length = _
    rw [ih]
    simp
    omega

theorem keep (gs : List Gate) (u : List Bool) (i : ℕ) (hi : i<u.length) :
    (run gs u).getD i false = u.getD i false := by
  induction gs generalizing u with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (u ++ [value g u])).getD i false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

theorem appendBit (u : List Bool) (z : Bool) (i : ℕ) :
    (u++[z]).getD i false = if i=u.length then z else u.getD i false := by
  by_cases eq : i=u.length
  · subst i
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right eq]
    by_cases lt : i<u.length
    · exact List.getD_append _ _ _ _ lt
    · rw [List.getD_eq_default (u++[z]) false (by simp; omega),List.getD_eq_default u false (by omega)]

-- A renaming may place earlier values anywhere. Each new gate must still
-- write to the wire that corresponds to its original position.
theorem transport (f : ℕ → ℕ) (gs : List Gate) (u v : List Bool)
    (lookup : ∀ i, u.getD i false = v.getD (f i) false)
    (fresh : ∀ r < gs.length, ∀ i, f i = v.length+r ↔ i = u.length+r) :
    ∀ i, (run gs u).getD i false = (run (gs.map (rename f)) v).getD (f i) false := by
  induction gs generalizing u v with
  | nil => exact lookup
  | cons g gs ih =>
    have same : value g u = value (rename f g) v := by
      simp only [value,rename,List.map_map,Function.comp_def]
      rw [funext lookup]
    apply ih (u++[value g u]) (v++[value (rename f g) v])
    · intro i
      rw [appendBit,appendBit,same]
      have eq := fresh 0 (by simp) i
      simp only [Nat.add_zero] at eq
      simp only [eq,lookup]
    · intro r hr i
      have link := fresh (r+1) (by simp; omega) i
      simpa only [List.length_append,List.length_singleton,Nat.add_assoc,Nat.add_comm 1 r] using link

def shift (n i : ℕ) := if i<n then i else i+1

def rotate (n k i : ℕ) :=
  if i<n+k then shift n i else if i=n+k then n else i

def promoted (n : ℕ) (C : Circuit) (before after : List Gate) (g : Gate) : Circuit :=
  ⟨g :: before.map (rename (shift n)) ++ after.map (rename (rotate n before.length)),
   rotate n before.length C.output⟩

theorem moved (n : ℕ) (C : Circuit) (before after : List Gate) (g : Gate)
    (split : C.gates = before ++ g :: after) (raw : ∀ i ∈ g.inputs, i<n)
    (x : Fin n → Bool) :
    circuitFun n (promoted n C before after g) x = circuitFun n C x ∧
    ((promoted n C before after g).wires (List.ofFn x)).getD n false = value g (List.ofFn x) := by
  let u := List.ofFn x
  let z := value g u
  let old := run before u
  let new := run (before.map (rename (shift n))) (u++[z])
  have n0 : u.length = n := List.length_ofFn
  have olen : old.length = n+before.length := by simp [old,runLen,n0]
  have nlen : new.length = n+before.length+1 := by simp [new,runLen,n0]; omega
  have start (i) : u.getD i false = (u++[z]).getD (shift n i) false := by
    rw [appendBit,n0]
    by_cases lt : i<n
    · simp [shift,lt,show i≠n by omega]
    · simp only [shift,ite_eq_right lt,ite_eq_right (show i+1≠n by omega)]
      rw [List.getD_eq_default u false (by omega),List.getD_eq_default u false (by omega)]
  have early (i) : old.getD i false = new.getD (shift n i) false := by
    apply transport _ _ _ _ start
    intro r _ j
    simp only [List.length_append,List.length_singleton,n0,shift]
    split <;> omega
  have keepZ : new.getD n false = z := by
    change (run _ (u++[z])).getD n false = _
    rw [keep _ _ _ (by simp [n0]),appendBit,n0,ite_eq_left rfl]
  have gate : value g old = z := by
    unfold z value
    congr 1
    apply List.map_congr_left
    intro i hi
    exact keep before u i (by rw [n0]; exact raw i hi)
  have base (i) : (old++[z]).getD i false = new.getD (rotate n before.length i) false := by
    rw [appendBit,olen]
    by_cases lt : i<n+before.length
    · simpa only [rotate,ite_eq_left lt,ite_eq_right (Nat.ne_of_lt lt)] using early i
    · by_cases eq : i=n+before.length
      · simpa only [rotate,ite_eq_right lt,ite_eq_left eq] using keepZ.symm
      · simp only [rotate,ite_eq_right lt,ite_eq_right eq]
        rw [List.getD_eq_default old false (by omega),List.getD_eq_default new false (by omega)]
  have endval := transport (rotate n before.length) after (old++[z]) new base (by
    intro r _ i
    simp only [rotate,shift,nlen,List.length_append,List.length_singleton,olen]
    split <;> split <;> omega) C.output
  have prev : C.wires u = run after (old++[z]) := by
    change run C.gates u = _
    rw [split]
    simp only [run,List.foldl_append,List.foldl_cons]
    change run after (old++[value g old]) = run after (old++[z])
    rw [gate]
  have next : (promoted n C before after g).wires u =
      run (after.map (rename (rotate n before.length))) new := by
    simp only [promoted,Circuit.wires,run,List.foldl_cons,List.foldl_append,new,z,value]
  constructor
  · change ((promoted n C before after g).wires u).getD _ false = (C.wires u).getD C.output false
    rw [prev,next]
    exact endval.symm
  · change ((promoted n C before after g).wires u).getD n false = z
    rw [next,keep _ _ _ (by omega),keepZ]

end PEqualNP.Outside.L_meta_4518

open PEqualNP.Outside.L_meta_4518

theorem PEqualNP.Outside.L_meta_4518 :
    ∀ (C : Circuit) (before after : List Gate) (g : Gate), C.gates = before ++ g :: after →
      FanInTwo C → (∀ w ∈ g.inputs, w < 9) →
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ circuitFun 9 D = circuitFun 9 C ∧
        ∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false =
          g.op.eval (g.inputs.map fun w => (List.ofFn x).getD w false) := by
  intro C before after g split model raw
  refine ⟨promoted 9 C before after g,?_,?_,funext (fun x => (moved 9 C before after g split raw x).1),
    fun x => (moved 9 C before after g split raw x).2⟩
  · intro h mem
    simp only [promoted,List.mem_cons,List.mem_append,List.mem_map] at mem
    rcases mem with (rfl | ⟨v,hv,rfl⟩) | ⟨v,hv,rfl⟩
    · exact model _ (by simp [split])
    · simpa [rename] using model v (by simp [split,hv])
    · simpa [rename] using model v (by simp [split,hv])
  · simp [promoted,Circuit.size,split]
    omega
