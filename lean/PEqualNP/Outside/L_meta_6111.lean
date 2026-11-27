import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6111

open PEqualNP.Defs.LratEncoding

def positives : List Nat :=
  [130, 136, 257, 260, 320, 514, 544, 576, 1025, 1040, 1056, 2056, 2064,
    2112, 4100, 4104, 4128, 8194, 8196, 8208]

def negatives : List Nat :=
  [127, 129, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087,
    2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426,
    8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]

def rows : List Nat := positives ++ negatives

def target (r : Nat) : Bool := positives.contains r

def flip (l : Nat) : Nat := if l % 2 = 0 then l + 1 else l - 1

theorem litVal_flip (a : Nat → Bool) (l : Nat) : litVal a (flip l) = !litVal a l := by
  unfold flip litVal
  by_cases h : l % 2 = 0
  · have hdiv : (l + 1) / 2 = l / 2 := by omega
    have hmod : (l + 1) % 2 = 1 := by omega
    rw [ite_eq_left h, hdiv, hmod, h]
    cases a (l / 2) <;> rfl
  · have hdiv : (l - 1) / 2 = l / 2 := by omega
    have hmod : (l - 1) % 2 = 0 := by omega
    have hodd : l % 2 = 1 := by omega
    rw [ite_eq_right h, hdiv, hmod, hodd]
    cases a (l / 2) <;> rfl

-- Replay the RUP hints for a single LRAT addition of the empty clause.
def replay (forced : List Nat) : List (List Nat) → Bool
  | [] => false
  | c :: rest =>
    match c.filter (fun l => !(forced.contains (flip l))) with
    | [] => true
    | [l] => replay (l :: forced) rest
    | _ => false

theorem replay_sound (a : Nat → Bool) (forced : List Nat) (hforced : ∀ l ∈ forced, litVal a l = true)
    (hints : List (List Nat)) (hsat : ∀ c ∈ hints, ClauseSat a c)
    (hcheck : replay forced hints = true) : False := by
  induction hints generalizing forced with
  | nil => simp [replay] at hcheck
  | cons c rest ih =>
    obtain ⟨l, hl, htrue⟩ := hsat c (List.mem_cons_self)
    have hkeep : l ∈ c.filter (fun k => !(forced.contains (flip k))) := by
      apply List.mem_filter.mpr
      refine ⟨hl, ?_⟩
      cases h : forced.contains (flip l)
      · rfl
      · have ht := hforced (flip l) (List.contains_iff_mem.mp h)
        simp [litVal_flip, htrue] at ht
    simp only [replay] at hcheck
    split at hcheck
    · rename_i he
      rw [he] at hkeep
      simp at hkeep
    · rename_i k he
      rw [he] at hkeep
      have hk : l = k := List.mem_singleton.mp hkeep
      apply ih (k :: forced) _ (fun d hd => hsat d (List.mem_cons_of_mem _ hd)) hcheck
      intro d hd
      rcases List.mem_cons.mp hd with h | h
      · exact (h.trans hk.symm) ▸ htrue
      · exact hforced d h
    · contradiction

def var (kind gate slot : Nat) : Nat := ix 14 24 kind gate slot

def lastHints : List (List Nat) := [[P (var 0 23 2)], [P (var 7 23 0), Q (var 0 23 2)]]

def paddingHints : List (List Nat) :=
  (List.range 23).reverse.map fun j => [Q (var 7 (j + 1) 0), P (var 7 j 0)]

-- On the negative row 127, every padding gate is true and cannot be the output.
def gateHints (j : Nat) : List (List Nat) :=
  (if j = 23 then [] else [[Q (var 7 j 0), P (var 0 j 2)]]) ++
  [[Q (var 0 j 2), P (var 3 j 127)], [Q (var 6 0 (14 + j)), Q (var 3 j 127)]]

def inputHints : List (List Nat) := (List.range 14).map fun k => [Q (var 6 0 k)]

def hints : List (List Nat) :=
  lastHints ++ paddingHints ++ (List.range 24).flatMap gateHints ++ inputHints ++
    [[Q (var 6 0 38)]] ++ fOutAlo 14 24

def inputRejectRow (k : Nat) : Nat :=
  if k = 1 then 136 else if k = 7 then 257 else 130

theorem inputRejectRow_spec : ∀ k : Fin 14,
    inputRejectRow k.val ∈ rows ∧ (inputRejectRow k.val).testBit k.val ≠ target (inputRejectRow k.val) := by
  decide

theorem mem_outEq {r k : Nat} {c : List Nat} (hr : r ∈ rows) (hk : k < 39)
    (hc : c ∈ outEq 14 24 target k r) : c ∈ fOutEq 14 24 target rows :=
  List.mem_flatMap.mpr ⟨r, hr, List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, hc⟩⟩

theorem mem_pad {j : Nat} (hj : j < 24) :
    [P (var 7 j 0), Q (var 0 j 2)] ∈ fPad 14 24 ∧
    [Q (var 7 j 0), P (var 0 j 2)] ∈ fPad 14 24 := by
  unfold fPad
  constructor
  · exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, by simp [var]⟩
  · exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, by simp [var]⟩

theorem mem_gate {j : Nat} (hj : j < 24) :
    [Q (var 0 j 2), P (var 3 j 127)] ∈ fGate 14 24 rows := by
  exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj,
    List.mem_flatMap.mpr ⟨127, by decide, by simp [gateCl, var]⟩⟩

theorem mem_output_gate {j : Nat} (hj : j < 24) :
    [Q (var 6 0 (14 + j)), Q (var 3 j 127)] ∈ fOutEq 14 24 target rows := by
  have hr : target 127 = false := by decide
  have hlo : ¬ 14 + j < 14 := by omega
  have hhi : 14 + j < 14 + 24 := by omega
  have hsub : 14 + j - 14 = j := by omega
  apply mem_outEq (r := 127) (k := 14 + j) (by decide) (by omega)
  simp [outEq, hlo, hhi, hsub, hr, L, var]

theorem mem_output_input {k : Nat} (hk : k < 14) :
    [Q (var 6 0 k)] ∈ fOutEq 14 24 target rows := by
  obtain ⟨hr, hm⟩ := inputRejectRow_spec ⟨k, hk⟩
  apply mem_outEq (k := k) hr (by omega)
  simpa [outEq, hk, var] using hm

theorem mem_output_constant : [Q (var 6 0 38)] ∈ fOutEq 14 24 target rows :=
  mem_outEq (r := 130) (k := 38) (by decide) (by decide) (by decide)

theorem hints_in_formula {c : List Nat} (hc : c ∈ hints) :
    c ∈ [755464] :: enc 14 24 target rows := by
  simp only [hints, List.mem_append] at hc
  rcases hc with (((((hc | hc) | hc) | hc) | hc) | hc)
  · simp only [lastHints, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact List.mem_cons_self
    · have h := (mem_pad (j := 23) (by decide)).1
      simp only [List.mem_cons, enc, List.mem_append, h, true_or, or_true]
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
    have h : [Q (var 7 (j + 1) 0), P (var 7 j 0)] ∈ fPre 14 24 := by
      exact List.mem_map_of_mem (List.mem_reverse.mp hj)
    simp only [List.mem_cons, enc, List.mem_append, h, true_or, or_true]
  · obtain ⟨j, hj, hc⟩ := List.mem_flatMap.mp hc
    have hj' := List.mem_range.mp hj
    have h₁ := (mem_pad hj').2
    have h₂ := mem_gate hj'
    have h₃ := mem_output_gate hj'
    have hcases : c = [Q (var 7 j 0), P (var 0 j 2)] ∨
        c = [Q (var 0 j 2), P (var 3 j 127)] ∨
        c = [Q (var 6 0 (14 + j)), Q (var 3 j 127)] := by
      by_cases he : j = 23
      · subst j
        change c ∈ [[Q (var 0 23 2), P (var 3 23 127)],
          [Q (var 6 0 (14 + 23)), Q (var 3 23 127)]] at hc
        exact Or.inr (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hc)
      · simpa only [gateHints, ite_eq_right he, List.cons_append, List.nil_append,
          List.mem_cons, List.not_mem_nil, or_false] using hc
    rcases hcases with rfl | rfl | rfl <;>
      simp only [List.mem_cons, enc, List.mem_append, h₁, h₂, h₃, true_or, or_true]
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
    have h := mem_output_input (List.mem_range.mp hk)
    simp only [List.mem_cons, enc, List.mem_append, h, true_or, or_true]
  · have he : c = [Q (var 6 0 38)] := by simpa using hc
    subst c
    simp only [List.mem_cons, enc, List.mem_append, mem_output_constant, true_or, or_true]
  · simp only [List.mem_cons, enc, List.mem_append, hc, true_or, or_true]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
theorem checked : replay [] hints = true := by decide +kernel

theorem unsat : ¬ FormulaSat ([755464] :: enc 14 24 target rows) := by
  rintro ⟨a, ha⟩
  exact replay_sound a [] (by simp) hints (fun c hc => ha c (hints_in_formula hc)) checked

end PEqualNP.Outside.L_meta_6111

theorem PEqualNP.Outside.L_meta_6111 :
    have x1 : List ℕ := [(130 : ℕ), (136 : ℕ), (257 : ℕ), (260 : ℕ), (320 : ℕ), (514 : ℕ), (544 : ℕ), (576 : ℕ), (1025 : ℕ), (1040 : ℕ), (1056 : ℕ), (2056 : ℕ), (2064 : ℕ), (2112 : ℕ), (4100 : ℕ), (4104 : ℕ), (4128 : ℕ), (8194 : ℕ), (8196 : ℕ), (8208 : ℕ)]; have x2 : List ℕ :=   have x2 : List ℕ :=     have x2 : List ℕ :=       have x2 : List ℕ := [(10656 : ℕ), (12353 : ℕ), (13504 : ℕ), (14849 : ℕ), (16256 : ℕ)];       (8488 : ℕ) :: (8713 : ℕ) :: (9288 : ℕ) :: (9992 : ℕ) :: (10273 : ℕ) :: x2;     have x3 : List ℕ := (5186 : ℕ) :: (6147 : ℕ) :: (7426 : ℕ) :: (8297 : ℕ) :: (8416 : ℕ) :: x2;     (4304 : ℕ) :: (4370 : ℕ) :: (4625 : ℕ) :: (5008 : ℕ) :: x3;   have x3 : List ℕ :=     have x3 : List ℕ := (2338 : ℕ) :: (2565 : ℕ) :: (3078 : ℕ) :: (3716 : ℕ) :: (4179 : ℕ) :: x2;     (1220 : ℕ) :: (1290 : ℕ) :: (1548 : ℕ) :: (2087 : ℕ) :: (2212 : ℕ) :: x3;   have x4 : List ℕ := (432 : ℕ) :: (541 : ℕ) :: (660 : ℕ) :: (792 : ℕ) :: (1102 : ℕ) :: x3;   (127 : ℕ) :: (129 : ℕ) :: (244 : ℕ) :: (314 : ℕ) :: x4; ¬PEqualNP.Defs.LratEncoding.FormulaSat ([(755464 : ℕ)] :: PEqualNP.Defs.LratEncoding.enc (14 : ℕ) (24 : ℕ) (fun (x3 : ℕ) => x1.contains x3) (x1 ++ x2)) := by
  exact PEqualNP.Outside.L_meta_6111.unsat
