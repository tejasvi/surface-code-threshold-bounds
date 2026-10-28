import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9856 = true := by
  decide +kernel

theorem tot9856 : totK PD2M8K2 D2M8K2.t9856 = [0, 3766812078, 171936546187, 459332954884, 260283297464, 20249401196, 0, 0] := by
  decide +kernel

theorem rows9857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9857 = true := by
  decide +kernel

theorem tot9857 : totK PD2M8K2 D2M8K2.t9857 = [0, 198884268480, 477684381053, 199543187385, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows9858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9858 = true := by
  decide +kernel

theorem tot9858 : totK PD2M8K2 D2M8K2.t9858 = [0, 193530150901, 466898596773, 221338886291, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows9859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9859 = true := by
  decide +kernel

theorem tot9859 : totK PD2M8K2 D2M8K2.t9859 = [0, 18824206913, 288733971449, 460636693457, 105471358198, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
