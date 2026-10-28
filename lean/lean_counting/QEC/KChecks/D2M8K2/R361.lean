import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1444 = true := by
  decide +kernel

theorem tot1444 : totK PD2M8K2 D2M8K2.t1444 = [0, 0, 227762493746, 480040100447, 167892515556, 9465708191, 0, 0] := by
  decide +kernel

theorem rows1445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1445 = true := by
  decide +kernel

theorem tot1445 : totK PD2M8K2 D2M8K2.t1445 = [0, 151251940429, 402048063015, 278846204142, 61041476983, 2526216925, 0, 0] := by
  decide +kernel

theorem rows1446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1446 = true := by
  decide +kernel

theorem tot1446 : totK PD2M8K2 D2M8K2.t1446 = [0, 174478519940, 452327579560, 262627895062, 19575576185, 0, 0, 0] := by
  decide +kernel

theorem rows1447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1447 = true := by
  decide +kernel

theorem tot1447 : totK PD2M8K2 D2M8K2.t1447 = [0, 0, 307933790861, 490764555222, 89070026523, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
