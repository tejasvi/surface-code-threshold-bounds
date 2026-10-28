import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1380 = true := by
  decide +kernel

theorem tot1380 : totK PD2M8K2 D2M8K2.t1380 = [0, 0, 198361624800, 499427298987, 167735672010, 2518061560, 0, 0] := by
  decide +kernel

theorem rows1381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1381 = true := by
  decide +kernel

theorem tot1381 : totK PD2M8K2 D2M8K2.t1381 = [0, 0, 182946547881, 508588369385, 188820888489, 2448800629, 0, 0] := by
  decide +kernel

theorem rows1382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1382 = true := by
  decide +kernel

theorem tot1382 : totK PD2M8K2 D2M8K2.t1382 = [0, 0, 197772613263, 460582469230, 209825270777, 10816184264, 0, 0] := by
  decide +kernel

theorem rows1383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1383 = true := by
  decide +kernel

theorem tot1383 : totK PD2M8K2 D2M8K2.t1383 = [0, 53299326172, 200791130493, 407092464511, 226062773875, 17376665387, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
