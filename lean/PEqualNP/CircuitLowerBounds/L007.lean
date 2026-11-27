import PEqualNP.Defs
import PEqualNP.CircuitLowerBounds.Helpers.ParityAssembly

/-- Parity is not in AC0: the strings with an odd number of true symbols have no
polynomial-size constant-depth circuits of unbounded fan-in AND, OR and NOT gates (Furst, Saxe
and Sipser 1984; Ajtai 1983; Hastad 1986; proved here by the polynomial method of Razborov
1987 and Smolensky 1987, over the field with three elements). -/
theorem PEqualNP.CircuitLowerBounds.L007 :
    ({x : List Bool | x.count true % 2 = 1} : Language Bool) ∉
      PEqualNP.CircuitLowerBounds.AC0 :=
  PEqualNP.CircuitLowerBounds.Helpers.ParityAC0.parity_not_AC0
