import PEqualNP.Gct.Helpers.Rung.FewRows
import PEqualNP.Gct.Helpers.Rung.RowSystem
import PEqualNP.Gct.Helpers.Rung.BoundedZeros

/-!
# Few rows, unconditionally

`fewRows` applied to the row system (identity I2) and to Fact Z.
-/

namespace PEqualNP.Gct.Rung

theorem fewRows_holds : FewRows := fewRows rowSystem boundedZeros

end PEqualNP.Gct.Rung
