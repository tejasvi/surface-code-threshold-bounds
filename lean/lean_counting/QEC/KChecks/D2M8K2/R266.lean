import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1064 = true := by
  decide +kernel

theorem tot1064 : totK PD2M8K2 D2M8K2.t1064 = [0, 41029572191, 320837194193, 432122221890, 97448492196, 1369150432, 0, 0] := by
  decide +kernel

theorem rows1065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1065 = true := by
  decide +kernel

theorem tot1065 : totK PD2M8K2 D2M8K2.t1065 = [0, 58275342796, 355388363263, 439505667138, 54017008577, 0, 0, 0] := by
  decide +kernel

theorem rows1066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1066 = true := by
  decide +kernel

theorem tot1066 : totK PD2M8K2 D2M8K2.t1066 = [0, 183619034967, 472016716282, 232240755053, 13574233288, 0, 0, 0] := by
  decide +kernel

theorem rows1067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1067 = true := by
  decide +kernel

theorem tot1067 : totK PD2M8K2 D2M8K2.t1067 = [0, 164845006716, 463369795562, 246105339588, 13535101234, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
