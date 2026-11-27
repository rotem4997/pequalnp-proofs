import PEqualNP.CircuitLowerBounds.Helpers.Switching.CoreSem

/-!
# Switching lemma: the core, in one place

Entry module. Definitions are in `CoreBasic.lean`, the encoding in `CoreEncode.lean`, the count
in `CoreCount.lean` and the translation to the plan's semantic statement in `CoreSem.lean`.
The results other modules consume:

* `Core.card_bad`: `card (bad F l t) ≤ card (R n (l - t)) * (4 w)^t` for `t ≥ 1`;
* `Core.card_bad_ratio`: `card (bad F l t) * (n - l)^t ≤ card (R n l) * (8 w l)^t`;
* `Core.card_R`: `card (R n l) = choose n l * 2^(n - l)`;
* `Core.cert_of_cdt`: canonical depth at most `t` gives certificates of size `t`;
* `Core.switchingSem : Plan.SwitchingSem`.
-/

namespace PEqualNP.CircuitLowerBounds.Switching.Core

/-- The switching lemma of the plan, restated under the name the wiring expects. -/
theorem switchingSem' : Plan.SwitchingSem := switchingSem

end PEqualNP.CircuitLowerBounds.Switching.Core
