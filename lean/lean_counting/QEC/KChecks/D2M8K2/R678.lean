import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2712 = true := by
  decide +kernel

theorem tot2712 : totK PD2M8K2 D2M8K2.t2712 = [0, 92333346222, 358353963340, 366201984678, 71831156425, 1232609433, 0, 0] := by
  decide +kernel

theorem rows2713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2713 = true := by
  decide +kernel

theorem tot2713 : totK PD2M8K2 D2M8K2.t2713 = [0, 0, 245762833376, 502554005461, 151587420615, 2330854693, 0, 0] := by
  decide +kernel

theorem rows2714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2714 = true := by
  decide +kernel

theorem tot2714 : totK PD2M8K2 D2M8K2.t2714 = [0, 0, 168094926619, 459868400653, 230535429701, 15642258933, 0, 0] := by
  decide +kernel

theorem rows2715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2715 = true := by
  decide +kernel

theorem tot2715 : totK PD2M8K2 D2M8K2.t2715 = [0, 0, 277569254052, 498430950326, 114046914648, 1081283312, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
