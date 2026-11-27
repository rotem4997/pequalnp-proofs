import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2650

open PEqualNP.CircuitLowerBounds

-- For every ordered pair of distinct vertices, an automorphism of the Heawood graph, packed
-- in hexadecimal digits: pf u v maps u and v onto 0 and one of 1, 7, 9; qf u v is its
-- inverse; jf u v is that second vertex; adj is the adjacency of the graph. The tables are
-- checked by the kernel below; the circuit is then relabeled along the automorphism.
def PT : ℕ := 0xdcba9876543210000154236cda978b000513246dc79a8b001430526ca7bd980002541639dac87b001342506acdb798001542360bcda978009bac78d0354612009ab87cd3064512007ba89cd56043120097acbd84350162007abc98d65340120079bcad84536102009cb8da74263510000154236cda978b00dcba98765432100020145639ad78cb004150326c7a9db8002153046a7c9d8b003152406adc97b8005132460bdc79a800b9ad78c014563200b798acd50613420079a8bdc46051320097acbd8435016200a79cb8d63510420079bcad8453610200d9bac783546120000513246dc79a8b0020145639ad78cb00dcba9876543210003510426da79cb80025140367ad9c8b0045123067cd9ab80043125609cd7ba800b97ca8d053164200ba987dc106543200a978bcd360154200ba7c9d81530462007a9db8c6415032007b9dac8541630200cb9ad781456320001430526ca7bd98004150326c7a9db8003510426da79cb800dcba9876543210005340126d7abc98006251403ad9c8b7006451230cd9ab8700cba987d065432100cab789d6034521008ba7c9d530462100c8a9bd74650231008ab9c7d3564021008cb9ad7456320100db97ca853164200002541639dac87b002153046a7c9d8b0025140367ad9c8b005340126d7abc9800dcba98765432100054321067dcba980034521609dcab78009bac78d0354612009ab87cd3064512007ba89cd560431200b7ad9c85140362007abc98d653401200ab9c7d8135640200dcba9876543210001342506acdb798003152406adc97b80045123067cd9ab8006251403ad9c8b70054321067dcba9800dcba9876543210006543210dcba98700cba987d065432100cab789d6034521008ba7c9d530462100ca8db976420531008ab9c7d356402100acbd897624350100d9bac783546120001542360bcda978005132460bdc79a80043125609cd7ba8006451230cd9ab870034521609dcab78006543210dcba98700dcba987654321000cb8da79042635100c8b7ad9403625100ab87cd9230645100c8a9bd7465023100a8bdc793246051008cb9ad7456320100dcba9876543210009bac78d035461200b9ad78c014563200b97ca8d053164200cba987d0654321009bac78d035461200cba987d065432100cb8da79042635100dcba987654321000ba987dc106543200ab789dc160345200b97ca8d0531642008a9bd7c146502300ab9c7d8135640200cb9ad781456320009ab87cd306451200b798acd506134200ba987dc106543200cab789d6034521009ab87cd306451200cab789d603452100c8b7ad9403625100ba987dc106543200dcba987654321000da978bc601542300b798acd506134200a7bd98c614305200a9bd7c8314650200c9b7da84136520007ba89cd56043120079a8bdc460513200a978bcd3601542008ba7c9d5304621007ba89cd5604312008ba7c9d530462100ab87cd9230645100ab789dc160345200da978bc601542300dcba987654321000a978bcd3601542007a9db8c6415032007b9dac8541630200db97ca853164200097acbd843501620097acbd8435016200ba7c9d8153046200c8a9bd7465023100b7ad9c8514036200ca8db97642053100c8a9bd7465023100b97ca8d053164200b798acd506134200a978bcd360154200dcba987654321000a79cb8d6351042008d9bac7546120300cd9ab876451230007abc98d653401200a79cb8d6351042007a9db8c6415032008ab9c7d3564021007abc98d6534012008ab9c7d356402100a8bdc793246051008a9bd7c146502300a7bd98c6143052007a9db8c641503200a79cb8d635104200dcba98765432100079bcad8453610200d9bac7835461200079bcad845361020079bcad84536102007b9dac85416302008cb9ad7456320100ab9c7d8135640200acbd8976243501008cb9ad7456320100ab9c7d8135640200a9bd7c83146502007b9dac85416302008d9bac754612030079bcad8453610200dcba987654321000dcba9876543210009cb8da7426351000d9bac78354612000cb9ad78145632000db97ca8531642000dcba987654321000d9bac78354612000dcba987654321000cb9ad78145632000c9b7da8413652000db97ca8531642000cd9ab87645123000d9bac78354612000dcba987654321000dcba9876543210
def QT : ℕ := 0xdcba98765432100056043127ba89cd0065023147c8a9bd00263510479cb8da0053046218ba7c9d00453610279bcad80045632018cb9ad7007acbd8924350160078bcda942360150078cb9ad5632014008a9bd7c1465023007abc98d6534012008ab9c7d3564021009cb8da742635100056043127ba89cd00dcba987654321000410562389a7dbc0026143057bd98ca0024063157b8adc90054163027b9dac80054612038d9bac700a7dbc8923410560078d9bac461203500879bcad5361024008a9bd7c1465023007a9db8c6415032008ab9c7d356402100d9bac7835461200065023147c8a9bd00410562389a7dbc00dcba98765432100062153047c9d8ba0042053167ca8db90045123067cd9ab800452160389dcab7007ad9c8b25140360087dcba9432106500789dcab5216034008adc97b152406300a79cb8d635104200a8c9b7d3652041009dcab78345216000263510479cb8da0026143057bd98ca0062153047c9d8ba00dcba98765432100062341057dbc89a005316420db97ca8005623410dbc89a7007dcba985432106007dbc89a62341050079cb8da2635104008d9bac754612030079bcad84536102008cb9ad7456320100d9c8b7a36251400053046218ba7c9d0024063157b8adc90042053167ca8db90062341057dbc89a00dcba98765432100054321067dcba980054236018bcda97007acbd8924350160078bcda942360150078cb9ad563201400a8db97c1642053007abc98d6534012008acdb79342506100dcba987654321000453610279bcad80054163027b9dac80045123067cd9ab8005316420db97ca80054321067dcba9800dcba9876543210006543210dcba987007dcba985432106007dbc89a62341050079cb8da263510400ad9c8b762514030079bcad8453610200acbd897624350100d9bac7835461200045632018cb9ad70054612038d9bac700452160389dcab7005623410dbc89a70054236018bcda97006543210dcba98700dcba987654321000adc97b83152406008db97ca31642050089cd7ba3125604008d9bac7546120300a9bd7c83146502008cb9ad7456320100dcba9876543210007acbd89243501600a7dbc892341056007ad9c8b2514036007dcba985432106007acbd892435016007dcba98543210600adc97b8315240600dcba98765432100087dcba943210650087cd9ab5123064007ad9c8b25140360097acbd84350162008acdb793425061009dcab7834521600078bcda942360150078d9bac46120350087dcba94321065007dbc89a62341050078bcda94236015007dbc89a6234105008db97ca31642050087dcba9432106500dcba987654321000d78cb9a63201450078d9bac461203500a7bd98c614305200a8bdc793246051009db8c7a32641500078cb9ad563201400879bcad536102400789dcab52160340079cb8da26351040078cb9ad56320140079cb8da26351040089cd7ba31256040087cd9ab512306400d78cb9a632014500dcba987654321000789dcab521603400a79cb8d635104200a8c9b7d365204100d9c8b7a3625140008a9bd7c1465023008a9bd7c1465023008adc97b1524063008d9bac7546120300a8db97c164205300ad9c8b76251403008d9bac75461203007ad9c8b25140360078d9bac461203500789dcab521603400dcba9876543210007a9db8c641503200c8a9bd7465023100cd9ab876451230007abc98d6534012007a9db8c641503200a79cb8d63510420079bcad84536102007abc98d65340120079bcad8453610200a9bd7c831465020097acbd8435016200a7bd98c614305200a79cb8d6351042007a9db8c641503200dcba9876543210008ab9c7d356402100d9bac783546120008ab9c7d3564021008ab9c7d356402100a8c9b7d3652041008cb9ad74563201008acdb79342506100acbd8976243501008cb9ad74563201008acdb79342506100a8bdc79324605100a8c9b7d365204100c8a9bd74650231008ab9c7d356402100dcba987654321000dcba9876543210009cb8da7426351000d9bac783546120009dcab78345216000d9c8b7a362514000dcba987654321000d9bac78354612000dcba9876543210009dcab783452160009db8c7a326415000d9c8b7a362514000cd9ab87645123000d9bac78354612000dcba987654321000dcba9876543210
def JT : ℕ := 0x111111997977910111119797799110111179779991110111977999711110117799979111110179997971111110999797799797790111111979779910111117977999110111197799971110111779997911110117999797111110199979771111110
def ADJ : ℕ := 0x5802c01600310188045002cb005802c0062031008a00580

def pf (u v i : ℕ) : ℕ := (PT >>> (64 * (u * 14 + v) + 4 * i)) &&& 15
def qf (u v i : ℕ) : ℕ := (QT >>> (64 * (u * 14 + v) + 4 * i)) &&& 15
def jf (u v : ℕ) : ℕ := (JT >>> (4 * (u * 14 + v))) &&& 15
def adj (a b : ℕ) : Bool := (ADJ >>> (a * 14 + b)) &&& 1 == 1

def E : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem tab_perm : ∀ u, u < 14 → ∀ v, v < 14 → u ≠ v → ∀ i, i < 14 →
    pf u v i < 14 ∧ qf u v i < 14 ∧ qf u v (pf u v i) = i ∧ pf u v (qf u v i) = i := by
  decide +kernel

theorem tab_edge : ∀ u, u < 14 → ∀ v, v < 14 → u ≠ v → ∀ e ∈ E,
    adj (pf u v e.1) (pf u v e.2) = true ∧ adj (qf u v e.1) (qf u v e.2) = true := by
  decide +kernel

theorem tab_pair : ∀ u, u < 14 → ∀ v, v < 14 → u ≠ v →
    (jf u v = 1 ∨ jf u v = 7 ∨ jf u v = 9) ∧
      ((pf u v u = 0 ∧ pf u v v = jf u v) ∨ (pf u v u = jf u v ∧ pf u v v = 0)) := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem adj_mem : ∀ a, a < 14 → ∀ b, b < 14 → adj a b = true → ((a, b) ∈ E ∨ (b, a) ∈ E) := by
  decide +kernel

theorem getD_snoc (w : List Bool) (b : Bool) (t : ℕ) :
    (w ++ [b]).getD t false =
      if t < w.length then w.getD t false else if t = w.length then b else false := by
  by_cases h1 : t < w.length
  · simp [h1, List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · by_cases h2 : t = w.length
    · subst h2; simp
    · have h4 : ¬ t < (w ++ [b]).length := by simp; omega
      rw [List.getD_eq_default _ _ (not_lt.mp h4)]
      simp [h1, h2]

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def rg (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

theorem fold_rel (r : ℕ → ℕ) (hr1 : ∀ i, 14 ≤ i → r i = i) (hr2 : ∀ i, i < 14 → r i < 14) :
    ∀ (gs : List Gate) (wC wD : List Bool), 14 ≤ wC.length → wD.length = wC.length →
      (∀ i, wD.getD (r i) false = wC.getD i false) →
      ∀ i, ((gs.map (rg r)).foldl step wD).getD (r i) false = (gs.foldl step wC).getD i false := by
  intro gs
  induction gs with
  | nil => intro wC wD _ _ h i; exact h i
  | cons g gs ih =>
    intro wC wD hL hlen hinv
    have hc : g.op.eval ((g.inputs.map r).map fun i => wD.getD i false) =
        g.op.eval (g.inputs.map fun i => wC.getD i false) := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact hinv a
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp only [step, List.length_append, List.length_singleton]; omega
    · simp only [step, rg, List.length_append, List.length_singleton, hlen]
    · intro k
      simp only [step, rg]
      rw [hc, getD_snoc, getD_snoc, hlen]
      by_cases hk : k < 14
      · have h2 : r k < wC.length := by have := hr2 k hk; omega
        have h3 : k < wC.length := by omega
        simp only [h2, h3, ↓reduceIte]
        exact hinv k
      · have h1 := hr1 k (by omega)
        have h5 := hinv k
        rw [h1] at h5 ⊢
        by_cases h3 : k < wC.length
        · simp only [h3, ↓reduceIte]
          exact h5
        · simp only [h3, ↓reduceIte]

theorem edge_inv (u v : ℕ) (hu : u < 14) (hv : v < 14) (huv : u ≠ v) (x : Fin 14 → Bool) :
    (∃ a b : Fin 14, ((a : ℕ), (b : ℕ)) ∈ E ∧
        x ⟨pf u v a, (tab_perm u hu v hv huv a a.2).1⟩ = true ∧
        x ⟨pf u v b, (tab_perm u hu v hv huv b b.2).1⟩ = true) ↔
      (∃ a b : Fin 14, ((a : ℕ), (b : ℕ)) ∈ E ∧ x a = true ∧ x b = true) := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have h1 := (tab_edge u hu v hv huv _ hab).1
    rcases adj_mem _ (tab_perm u hu v hv huv a a.2).1 _ (tab_perm u hu v hv huv b b.2).1 h1 with
      h | h
    · exact ⟨_, _, h, ha, hb⟩
    · exact ⟨_, _, h, hb, ha⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    have h1 := (tab_edge u hu v hv huv _ hab).2
    have qa := tab_perm u hu v hv huv a a.2
    have qb := tab_perm u hu v hv huv b b.2
    have ea : (⟨pf u v (qf u v a), (tab_perm u hu v hv huv _ qa.2.1).1⟩ : Fin 14) = a :=
      Fin.ext qa.2.2.2
    have eb : (⟨pf u v (qf u v b), (tab_perm u hu v hv huv _ qb.2.1).1⟩ : Fin 14) = b :=
      Fin.ext qb.2.2.2
    rcases adj_mem _ qa.2.1 _ qb.2.1 h1 with h | h
    · exact ⟨⟨qf u v a, qa.2.1⟩, ⟨qf u v b, qb.2.1⟩, h, by rw [ea]; exact ha, by rw [eb]; exact hb⟩
    · exact ⟨⟨qf u v b, qb.2.1⟩, ⟨qf u v a, qa.2.1⟩, h, by rw [eb]; exact hb, by rw [ea]; exact ha⟩

end PEqualNP.Outside.L_meta_2650

theorem PEqualNP.Outside.L_meta_2650 : have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Fin (14 : ℕ) → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (14 : ℕ)) => ∀ (x5 : Fin (14 : ℕ) → Bool), x3.eval (List.ofFn x5 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x5 (0 : Fin (14 : ℕ)), x5 x4]]) = Bool.true ↔ x2 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List PEqualNP.CircuitLowerBounds.Gate) (x6 x7 : ℕ), x4.gates = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x6, x7] : PEqualNP.CircuitLowerBounds.Gate } :: x5 → x6 < (14 : ℕ) → x7 < (14 : ℕ) → x6 ≠ x7 → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x13 : Fin (14 : ℕ) → Bool), x4.eval (List.ofFn x13) = Bool.true ↔ x2 x13) → ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x14 ∧ x14.size + (1 : ℕ) ≤ x4.size ∧ (x3 x14 (1 : Fin (14 : ℕ)) ∨ x3 x14 (7 : Fin (14 : ℕ)) ∨ x3 x14 (9 : Fin (14 : ℕ))) := by
  intro x1 x2 x3 C rest u v hgates hu hv huv hmono hfun
  have hx1 : x1 = PEqualNP.Outside.L_meta_2650.E := rfl
  obtain ⟨hj, hpair⟩ := PEqualNP.Outside.L_meta_2650.tab_pair u hu v hv huv
  let r : ℕ → ℕ := fun i => if i < 14 then PEqualNP.Outside.L_meta_2650.pf u v i else i
  have hr1 : ∀ i, 14 ≤ i → r i = i := by
    intro i hi
    have hi' : ¬ i < 14 := by omega
    simp only [r, hi', ↓reduceIte]
  have hr2 : ∀ i, i < 14 → r i < 14 := by
    intro i hi
    simp only [r, hi, ↓reduceIte]
    exact (PEqualNP.Outside.L_meta_2650.tab_perm u hu v hv huv i hi).1
  let D : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨rest.map (PEqualNP.Outside.L_meta_2650.rg r), r C.output⟩
  have hmonoD : PEqualNP.MetaComplexity.Monotone2 D := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    have h0 := hmono g0 (by rw [hgates]; exact List.mem_cons_of_mem _ hg0)
    exact ⟨h0.1, by simpa [PEqualNP.Outside.L_meta_2650.rg] using h0.2⟩
  have hsize : D.size + 1 ≤ C.size := by
    simp [PEqualNP.CircuitLowerBounds.Circuit.size, D, hgates]
  have hx : ∀ (x5 : Fin 14 → Bool) (a : ℕ) (ha : a < 14) (b : Fin 14), a = (b : ℕ) →
      x5 ⟨a, ha⟩ = x5 b := fun x5 a ha b h => congrArg x5 (Fin.ext h)
  have hkey : ∀ jF : Fin 14, (jF : ℕ) = PEqualNP.Outside.L_meta_2650.jf u v → x3 D jF := by
    intro jF hjF x5
    let y : Fin 14 → Bool := fun i =>
      x5 ⟨PEqualNP.Outside.L_meta_2650.pf u v i,
        (PEqualNP.Outside.L_meta_2650.tab_perm u hu v hv huv i i.2).1⟩
    have heval : D.eval (List.ofFn x5 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x5 0, x5 jF]]) =
        C.eval (List.ofFn y) := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
      rw [hgates, List.foldl_cons]
      refine PEqualNP.Outside.L_meta_2650.fold_rel r hr1 hr2 rest _ _ (by simp) (by simp) ?_ C.output
      intro i
      rw [PEqualNP.Outside.L_meta_2650.getD_snoc, PEqualNP.Outside.L_meta_2650.getD_snoc]
      simp only [List.length_ofFn]
      by_cases hi : i < 14
      · have h2 := hr2 i hi
        simp only [h2, hi, ↓reduceIte]
        rw [PEqualNP.Outside.L_meta_2650.ofFn_getD _ _ h2,
          PEqualNP.Outside.L_meta_2650.ofFn_getD _ _ hi]
        simp only [r, hi, ↓reduceIte, y]
      · rw [hr1 i (by omega)]
        by_cases h14 : i = 14
        · subst h14
          simp only [lt_irrefl, ↓reduceIte, List.map_cons, List.map_nil]
          rw [PEqualNP.Outside.L_meta_2650.ofFn_getD _ _ hu,
            PEqualNP.Outside.L_meta_2650.ofFn_getD _ _ hv]
          simp only [y, PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil,
            id, Bool.or_false]
          rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [hx x5 _ _ 0 h1, hx x5 _ _ jF (h2.trans hjF.symm)]
          · rw [hx x5 _ _ 0 h2, hx x5 _ _ jF (h1.trans hjF.symm), Bool.or_comm]
        · simp only [hi, h14, ↓reduceIte]
    rw [heval, hfun y]
    simp only [x2, hx1]
    exact PEqualNP.Outside.L_meta_2650.edge_inv u v hu hv huv x5
  rcases hj with h | h | h
  · exact ⟨D, hmonoD, hsize, Or.inl (hkey 1 (by rw [h]; rfl))⟩
  · exact ⟨D, hmonoD, hsize, Or.inr (Or.inl (hkey 7 (by rw [h]; rfl)))⟩
  · exact ⟨D, hmonoD, hsize, Or.inr (Or.inr (hkey 9 (by rw [h]; rfl)))⟩
