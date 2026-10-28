import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7236 = true := by
  decide +kernel

theorem tot7236 : totK PD2M8K2 D2M8K2.t7236 = [0, 0, 0, 285736629291, 505036056293, 95542867549, 1077684915, 0] := by
  decide +kernel

theorem rows7237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7237 = true := by
  decide +kernel

theorem tot7237 : totK PD2M8K2 D2M8K2.t7237 = [0, 0, 0, 204769109453, 464752238416, 168369021287, 9609506048, 0] := by
  decide +kernel

theorem rows7238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7238 = true := by
  decide +kernel

theorem tot7238 : totK PD2M8K2 D2M8K2.t7238 = [0, 0, 0, 196151734214, 497952248065, 171631635148, 6401876813, 0] := by
  decide +kernel

theorem rows7239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7239 = true := by
  decide +kernel

theorem tot7239 : totK PD2M8K2 D2M8K2.t7239 = [0, 0, 0, 265228004220, 491625827410, 128461166250, 3862713773, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
