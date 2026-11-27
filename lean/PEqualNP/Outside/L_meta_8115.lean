import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8115

-- Helpers adapted from accepted proofs.

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



def AO (n : ℕ) (ds : List Gate) : Prop :=
  (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  ∀ (j : ℕ) (hj : j < ds.length), ∀ i ∈ ds[j].inputs, i < n + j

def Rep (n : ℕ) (ds : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c, ∀ y, f y = c) ∨
    ∃ k < n + ds.length, ∀ y, f y = (run ds (List.ofFn y)).getD k false

theorem rep_app (n : ℕ) (ds : List Gate) (g : Gate) (f : (Fin n → Bool) → Bool)
    (h : Rep n ds f) : Rep n (ds ++ [g]) f := by
  rcases h with h | ⟨k, hk, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨k, by simp; omega, fun y => ?_⟩
    rw [h y, run_prefix _ _ _ _ (by simpa using hk)]

theorem rep_two (n : ℕ) (ds : List Gate) (hds : AO n ds) (o : GateOp)
    (ho : o = GateOp.and ∨ o = GateOp.or) (u v : (Fin n → Bool) → Bool)
    (hu : Rep n ds u) (hv : Rep n ds v) :
    ∃ hs : List Gate, hs.length ≤ 1 ∧ AO n (ds ++ hs) ∧
      Rep n (ds ++ hs) fun y => o.eval [u y, v y] := by
  have triv : ∀ w : (Fin n → Bool) → Bool, Rep n ds w → (∀ y, o.eval [u y, v y] = w y) →
      ∃ hs : List Gate, hs.length ≤ 1 ∧ AO n (ds ++ hs) ∧
      Rep n (ds ++ hs) fun y => o.eval [u y, v y] := by
    intro w hw e
    refine ⟨[], by simp, by simpa using hds, ?_⟩
    rw [List.append_nil, show (fun y => o.eval [u y, v y]) = w from funext e]
    exact hw
  have cst : ∀ c : Bool, Rep n ds fun _ => c := fun c => Or.inl ⟨c, fun _ => rfl⟩
  rcases hu with ⟨c, hc⟩ | ⟨a, ha, hua⟩
  · rcases ho with rfl | rfl <;> cases c
    · exact triv _ (cst false) fun y => by simp [GateOp.eval, hc]
    · exact triv v hv fun y => by simp [GateOp.eval, hc]
    · exact triv v hv fun y => by simp [GateOp.eval, hc]
    · exact triv _ (cst true) fun y => by simp [GateOp.eval, hc]
  · rcases hv with ⟨c, hc⟩ | ⟨b, hb, hvb⟩
    · have hu : Rep n ds u := Or.inr ⟨a, ha, hua⟩
      rcases ho with rfl | rfl <;> cases c
      · exact triv _ (cst false) fun y => by simp [GateOp.eval, hc]
      · exact triv u hu fun y => by simp [GateOp.eval, hc]
      · exact triv u hu fun y => by simp [GateOp.eval, hc]
      · exact triv _ (cst true) fun y => by simp [GateOp.eval, hc]
    · refine ⟨[⟨o, [a, b]⟩], by simp, ⟨?_, ?_⟩, Or.inr ⟨n + ds.length, by simp, fun y => ?_⟩⟩
      · intro g hg
        rcases List.mem_append.1 hg with h | h
        · exact hds.1 g h
        · rw [List.mem_singleton.1 h]; exact ⟨ho, rfl⟩
      · intro j hj i hi
        by_cases h : j < ds.length
        · rw [List.getElem_append_left h] at hi
          exact hds.2 j h i hi
        · have hj' : j = ds.length := by simp at hj; omega
          subst hj'
          simp at hi
          rcases hi with rfl | rfl <;> assumption
      · rw [run_snoc, show n + ds.length = (run ds (List.ofFn y)).length by
          rw [run_length, List.length_ofFn], getD_at]
        simp [hua, hvb]


theorem rep_c1 (n : ℕ) (ds : List Gate) (o : GateOp) (ho : o = GateOp.and ∨ o = GateOp.or)
    (c : Bool) (v : (Fin n → Bool) → Bool) (hv : Rep n ds v) :
    Rep n ds fun y => o.eval [c, v y] := by
  rcases ho with rfl | rfl <;> cases c
  · exact Or.inl ⟨false, fun y => by simp [GateOp.eval]⟩
  · convert hv using 1; funext y; simp [GateOp.eval]
  · convert hv using 1; funext y; simp [GateOp.eval]
  · exact Or.inl ⟨true, fun y => by simp [GateOp.eval]⟩

theorem rep_c2 (n : ℕ) (ds : List Gate) (o : GateOp) (ho : o = GateOp.and ∨ o = GateOp.or)
    (c : Bool) (v : (Fin n → Bool) → Bool) (hv : Rep n ds v) :
    Rep n ds fun y => o.eval [v y, c] := by
  rcases ho with rfl | rfl <;> cases c
  · exact Or.inl ⟨false, fun y => by simp [GateOp.eval]⟩
  · convert hv using 1; funext y; simp [GateOp.eval]
  · convert hv using 1; funext y; simp [GateOp.eval]
  · exact Or.inl ⟨true, fun y => by simp [GateOp.eval]⟩

theorem ao_snoc (n : ℕ) (gs : List Gate) (g : Gate) (a b : ℕ) (hAO : AO n gs)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hI : g.inputs = [a, b])
    (ha : a < n + gs.length) (hb : b < n + gs.length) : AO n (gs ++ [g]) := by
  refine ⟨fun g' hg' => ?_, fun j hj i hi => ?_⟩
  · rcases List.mem_append.1 hg' with h | h
    · exact hAO.1 g' h
    · rw [List.mem_singleton.1 h]; exact ⟨hop, by simp [hI]⟩
  · by_cases h : j < gs.length
    · rw [List.getElem_append_left h] at hi
      exact hAO.2 j h i hi
    · have hj' : j = gs.length := by simp at hj; omega
      subst hj'
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, hI] at hi
      simp at hi
      rcases hi with rfl | rfl <;> assumption

theorem build2 (n : ℕ) (gs : List Gate)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ ds : List Gate, AO n ds ∧ ds.length ≤ gs.length ∧ (ds.length < gs.length ∨ AO n gs) ∧
      ∀ w, Rep n ds fun y => (run gs (List.ofFn y)).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], ⟨by simp, by simp⟩, le_rfl, Or.inr ⟨by simp, by simp⟩, fun w => ?_⟩
    by_cases hw : w < n
    · exact Or.inr ⟨w, by simpa using hw, fun y => rfl⟩
    · exact Or.inl ⟨false, fun y => List.getD_eq_default _ _ (by simp [run]; omega)⟩
  | append_singleton gs g ih =>
    obtain ⟨ds, h1, h2, h2', h3⟩ := ih fun g' h => hops g' (by simp [h])
    obtain ⟨hop, hlen⟩ := hops g (by simp)
    have cfalse : ∀ a, ¬ a < n + gs.length → ∀ y : Fin n → Bool,
        (run gs (List.ofFn y)).getD a false = false := by
      intro a ha y
      exact List.getD_eq_default _ _ (by rw [run_length]; simp; omega)
    have main : ∃ hs : List Gate, hs.length ≤ 1 ∧ (hs.length = 0 ∨ (AO n gs → AO n (gs ++ [g]))) ∧
        AO n (ds ++ hs) ∧ Rep n (ds ++ hs)
        fun y => g.op.eval (g.inputs.map fun i => (run gs (List.ofFn y)).getD i false) := by
      match hI : g.inputs, hlen with
      | [], _ =>
        exact ⟨[], by simp, Or.inl rfl, by simpa using h1, Or.inl ⟨g.op.eval [], fun y => rfl⟩⟩
      | [a], _ =>
        refine ⟨[], by simp, Or.inl rfl, by simpa using h1, ?_⟩
        rw [List.append_nil]
        have e : (fun y : Fin n → Bool => g.op.eval ([a].map fun i =>
            (run gs (List.ofFn y)).getD i false)) =
            fun y => (run gs (List.ofFn y)).getD a false := by
          funext y
          rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
        rw [e]
        exact h3 a
      | [a, b], _ =>
        by_cases ha : a < n + gs.length
        · by_cases hb : b < n + gs.length
          · obtain ⟨hs, k1, k2, k3⟩ := rep_two n ds h1 g.op hop _ _ (h3 a) (h3 b)
            exact ⟨hs, k1, Or.inr fun hAO => ao_snoc n gs g a b hAO hop hI ha hb, k2, k3⟩
          · refine ⟨[], by simp, Or.inl rfl, by simpa using h1, ?_⟩
            rw [List.append_nil]
            have e : (fun y : Fin n → Bool => g.op.eval ([a, b].map fun i =>
                (run gs (List.ofFn y)).getD i false)) =
                fun y => g.op.eval [(run gs (List.ofFn y)).getD a false, false] := by
              funext y
              simp only [List.map_cons, List.map_nil, cfalse b hb y]
            rw [e]
            exact rep_c2 n ds g.op hop false _ (h3 a)
        · refine ⟨[], by simp, Or.inl rfl, by simpa using h1, ?_⟩
          rw [List.append_nil]
          have e : (fun y : Fin n → Bool => g.op.eval ([a, b].map fun i =>
              (run gs (List.ofFn y)).getD i false)) =
              fun y => g.op.eval [false, (run gs (List.ofFn y)).getD b false] := by
            funext y
            simp only [List.map_cons, List.map_nil, cfalse a ha y]
          rw [e]
          exact rep_c1 n ds g.op hop false _ (h3 b)
    obtain ⟨hs, k1, k0, k2, k3⟩ := main
    have k4 : ∀ f : (Fin n → Bool) → Bool, Rep n ds f → Rep n (ds ++ hs) f := by
      intro f hf
      match hs, k1 with
      | [], _ => simpa using hf
      | [g'], _ => exact rep_app n ds g' f hf
    refine ⟨ds ++ hs, k2, by simp; omega, ?_, fun w => ?_⟩
    · rcases k0 with h0 | himp
      · left; simp; omega
      · rcases h2' with hlt | hao
        · left; simp; omega
        · exact Or.inr (himp hao)
    by_cases hw : w = n + gs.length
    · have e : (fun y : Fin n → Bool => (run (gs ++ [g]) (List.ofFn y)).getD w false) =
          fun y => g.op.eval (g.inputs.map fun i => (run gs (List.ofFn y)).getD i false) := by
        funext y
        rw [run_snoc, hw, show n + gs.length = (run gs (List.ofFn y)).length by
          rw [run_length, List.length_ofFn], getD_at]
      rw [e]
      exact k3
    · by_cases hw' : w < n + gs.length
      · have e : (fun y : Fin n → Bool => (run (gs ++ [g]) (List.ofFn y)).getD w false) =
            fun y => (run gs (List.ofFn y)).getD w false := by
          funext y
          exact run_prefix _ _ _ _ (by simpa using hw')
        rw [e]
        exact k4 _ (h3 w)
      · exact Or.inl ⟨false, fun y => List.getD_eq_default _ _ (by
          rw [run_length]; simp; omega)⟩


theorem ofFn_false_getD (n k : ℕ) : (List.ofFn fun _ : Fin n => false).getD k false = false := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : (List.ofFn fun _ : Fin n => false)[k]? with _ | b
  · rfl
  · simp only [Option.getD_some]
    rw [List.getElem?_eq_some_iff] at h
    obtain ⟨_, h⟩ := h
    rw [← h]
    simp

theorem run_false (n : ℕ) (gs : List Gate) (hAO : AO n gs) :
    ∀ k, (run gs (List.ofFn fun _ : Fin n => false)).getD k false = false := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge k n with h | h
    · rw [run_input gs _ k (by simpa using h)]
      exact ofFn_false_getD n k
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      rcases Nat.lt_or_ge j gs.length with h2 | h2
      · have hg := run_gate gs (List.ofFn fun _ : Fin n => false) j h2
        simp only [List.length_ofFn] at hg
        rw [hg]
        obtain ⟨hop, hl⟩ := hAO.1 _ (List.getElem_mem h2)
        obtain ⟨a, b, hab⟩ : ∃ a b, gs[j].inputs = [a, b] := by
          match hI : gs[j].inputs, hl with
          | [a, b], _ => exact ⟨a, b, rfl⟩
        have hm : ∀ i : ℕ, (if i < n + j then
            (run gs (List.ofFn fun _ : Fin n => false)).getD i false else false) = false := by
          intro i
          split_ifs with hi
          · exact ih i hi
          · rfl
        rw [hab]
        simp only [List.map_cons, List.map_nil, hm]
        rcases hop with e | e <;> rw [e] <;> rfl
      · exact List.getD_eq_default _ _ (by rw [run_length]; simp; omega)

end PEqualNP.Outside.L_meta_8115

open PEqualNP.Outside.L_meta_8115 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8115 : have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ (∀ (x3 x4 : Fin (42 : ℕ)), x1 x3 x4 → x2.eval (List.ofFn fun (x6 : Fin (42 : ℕ)) => Decidable.decide (x6 = x3 ∨ x6 = x4)) = Bool.true) ∧ ∀ (x3 : Fin (42 : ℕ) → Bool), (∀ (x4 : Fin (42 : ℕ)), x3 x4 = Bool.true ↔ ∀ (x5 : Fin (42 : ℕ)), x3 x5 = Bool.true → ¬(x1 x4 x5 ∨ x1 x5 x4)) → x2.eval (List.ofFn x3) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → (∃ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x5]? = Option.some x6 ∧ x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x3.wires (List.ofFn fun (x7 : Fin (42 : ℕ)) => Bool.false)).getD ((42 : ℕ) + x5) Bool.false = Bool.true) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x2 x6 ∧ x6.size < x3.size := by
  dsimp only
  intro C ⟨hM, hE, hI⟩ ⟨x5, g, hg, hop, hw⟩
  obtain ⟨ds, h1, h2, h2', h3⟩ := build2 42 C.gates fun g hg => by
    obtain ⟨e1, e2⟩ := hM g hg
    exact ⟨by simpa using e1, e2⟩
  have hlt : ds.length < C.gates.length := by
    rcases h2' with h | h
    · exact h
    · have := run_false 42 C.gates h (42 + x5)
      exact Bool.noConfusion (this.symm.trans hw)
  have hedge : C.eval (List.ofFn fun v : Fin 42 => decide (v = 0 ∨ v = 21)) = true :=
    hE 0 21 (by decide)
  have hind : C.eval (List.ofFn fun v : Fin 42 => decide (v.val < 21)) = false := by
    apply hI
    intro a
    constructor
    · intro ha b hb h
      simp only [decide_eq_true_eq] at ha hb
      rcases h with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega
    · intro h
      by_contra ha
      simp only [decide_eq_true_eq, not_lt] at ha
      apply h ⟨a.val - 21, by omega⟩ (by simp only [decide_eq_true_eq]; omega)
      right
      refine ⟨by simp only; omega, ha, ?_⟩
      show (a.val + 21 - (a.val - 21)) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      rw [show a.val + 21 - (a.val - 21) = 42 by omega]
      decide
  rcases h3 C.output with ⟨c, hc⟩ | ⟨k, hk, hk'⟩
  · have e1 : c = true := (hc (fun v : Fin 42 => decide (v = 0 ∨ v = 21))).symm.trans hedge
    have e2 : c = false := (hc (fun v : Fin 42 => decide (v.val < 21))).symm.trans hind
    exact Bool.noConfusion (e1.symm.trans e2)
  · have heq : ∀ y : Fin 42 → Bool, (⟨ds, k⟩ : Circuit).eval (List.ofFn y) = C.eval (List.ofFn y) :=
      fun y => (hk' y).symm
    refine ⟨⟨ds, k⟩, ⟨fun g hg => ?_, fun a b hab => ?_, fun y hy => ?_⟩, ?_⟩
    · obtain ⟨e1, e2⟩ := h1.1 g hg
      refine ⟨?_, by omega⟩
      rcases e1 with e | e <;> simp [e]
    · rw [heq]
      exact hE a b hab
    · rw [heq]
      exact hI y hy
    · show ds.length < C.gates.length
      exact hlt
