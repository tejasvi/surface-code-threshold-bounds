import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3124 = true := by
  decide +kernel

theorem tot3124 : totK PD2M8K2 D2M8K2.t3124 = [8225356785, 182598911426, 456894811128, 242018957437, 17433533548, 0, 0, 0] := by
  decide +kernel

theorem rows3125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3125 = true := by
  decide +kernel

theorem tot3125 : totK PD2M8K2 D2M8K2.t3125 = [171303083261, 452403855039, 279408771809, 29195524301, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3126 = true := by
  decide +kernel

theorem tot3126 : totK PD2M8K2 D2M8K2.t3126 = [198639582419, 483017786759, 222304802675, 12148140469, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3127 = true := by
  decide +kernel

theorem tot3127 : totK PD2M8K2 D2M8K2.t3127 = [63042777117, 296421081447, 377583965688, 167145960940, 17186218589, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
