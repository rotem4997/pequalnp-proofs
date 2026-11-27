import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9127 : have x1 : List ℕ := [(256463372304 : ℕ), (8521482511360 : ℕ), (14003410187716736 : ℕ), (55389823206179104 : ℕ), (155696362464215096 : ℕ), (218994303131713984 : ℕ), (183565875465424384 : ℕ), (229736628136996864 : ℕ), (270286071508729856 : ℕ), (288160007409369088 : ℕ), (192860064594267704 : ℕ), (288166778660192704 : ℕ), (283797140973809664 : ℕ)]; have x2 : List ℕ := [(251137 : ℕ), (817232 : ℕ), (3224100 : ℕ), (5542026 : ℕ), (11018243 : ℕ), (9060364 : ℕ), (12746800 : ℕ), (10682560 : ℕ), (13370112 : ℕ), (15731712 : ℕ), (15376435 : ℕ), (16403468 : ℕ), (15664064 : ℕ)]; ∀ (x3 : Fin (58 : ℕ)), ∃ (x4 : Fin (24 : ℕ)), Nat.testBit (1764784 : ℕ) ↑x3 = Nat.testBit (4095 : ℕ) ↑x4 ∧ ∀ (x5 : Fin (13 : ℕ)), if Nat.testBit (1764784 : ℕ) ↑x3 = Bool.true then (x2.getD ↑x5 (0 : ℕ)).testBit ↑x4 = Bool.true → (x1.getD ↑x5 (0 : ℕ)).testBit ↑x3 = Bool.true else (x1.getD ↑x5 (0 : ℕ)).testBit ↑x3 = Bool.true → (x2.getD ↑x5 (0 : ℕ)).testBit ↑x4 = Bool.true := by
  dsimp only
  set_option synthInstance.maxSize 100000 in
  set_option synthInstance.maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
  decide +kernel
