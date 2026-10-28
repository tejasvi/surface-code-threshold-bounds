import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5336 = true := by
  decide +kernel

theorem tot5336 : totK PD2M8K2 D2M8K2.t5336 = [0, 0, 88698579362, 343949033457, 371200367777, 74635696045, 1171084559, 0] := by
  decide +kernel

theorem rows5337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5337 = true := by
  decide +kernel

theorem tot5337 : totK PD2M8K2 D2M8K2.t5337 = [0, 0, 0, 237158995255, 477053170457, 150759087076, 7064420917, 0] := by
  decide +kernel

theorem rows5338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5338 = true := by
  decide +kernel

theorem tot5338 : totK PD2M8K2 D2M8K2.t5338 = [0, 0, 152104580068, 432863306915, 269116760823, 50762483556, 1291861884, 0] := by
  decide +kernel

theorem rows5339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5339 = true := by
  decide +kernel

theorem tot5339 : totK PD2M8K2 D2M8K2.t5339 = [0, 0, 174329890017, 470261777894, 247439715630, 13992345081, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
