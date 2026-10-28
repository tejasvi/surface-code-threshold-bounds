import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6312 = true := by
  decide +kernel

theorem tot6312 : totK PD2M8K2 D2M8K2.t6312 = [0, 19240203164, 312966376385, 463134101990, 85453049026, 1198073392, 0, 0] := by
  decide +kernel

theorem rows6313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6313 = true := by
  decide +kernel

theorem tot6313 : totK PD2M8K2 D2M8K2.t6313 = [0, 151103432956, 426758097413, 292254931392, 30414720501, 0, 0, 0] := by
  decide +kernel

theorem rows6314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6314 = true := by
  decide +kernel

theorem tot6314 : totK PD2M8K2 D2M8K2.t6314 = [0, 165588237596, 439508317613, 255454303297, 20699950264, 0, 0, 0] := by
  decide +kernel

theorem rows6315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6315 = true := by
  decide +kernel

theorem tot6315 : totK PD2M8K2 D2M8K2.t6315 = [0, 90561473391, 372213017142, 348485028405, 58320290753, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
