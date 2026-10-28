import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13064 = true := by
  decide +kernel

theorem tot13064 : totK PD2M8K2 D2M8K2.t13064 = [0, 90840904916, 366971774882, 361696159363, 65734717971, 1096505104, 0, 0] := by
  decide +kernel

theorem rows13065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13065 = true := by
  decide +kernel

theorem tot13065 : totK PD2M8K2 D2M8K2.t13065 = [0, 0, 320930116191, 510975958630, 77378627065, 0, 0, 0] := by
  decide +kernel

theorem rows13066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13066 = true := by
  decide +kernel

theorem tot13066 : totK PD2M8K2 D2M8K2.t13066 = [0, 158854370654, 376885221878, 268370949159, 85731961938, 3884009855, 0, 0] := by
  decide +kernel

theorem rows13067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13067 = true := by
  decide +kernel

theorem tot13067 : totK PD2M8K2 D2M8K2.t13067 = [0, 204246893885, 468583882630, 208217484221, 12828756414, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
