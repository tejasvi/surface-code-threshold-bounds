import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows560 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t560 = true := by
  decide +kernel

theorem tot560 : totK PA10K2 A10K2.t560 = [0, 560562284328, 1967068584315, 1880596378290, 433942339120, 13149912228, 0, 0, 0, 0] := by
  decide +kernel

theorem rows561 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t561 = true := by
  decide +kernel

theorem tot561 : totK PA10K2 A10K2.t561 = [0, 445369364801, 1699189942404, 1903278524246, 562928987917, 32470943963, 0, 0, 0, 0] := by
  decide +kernel

theorem rows562 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t562 = true := by
  decide +kernel

theorem tot562 : totK PA10K2 A10K2.t562 = [0, 552537495973, 1853857046285, 1800982301676, 461328633062, 31607162994, 0, 0, 0, 0] := by
  decide +kernel

theorem rows563 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t563 = true := by
  decide +kernel

theorem tot563 : totK PA10K2 A10K2.t563 = [0, 326817226240, 1590818699618, 2041262325915, 637828800730, 51402059204, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
