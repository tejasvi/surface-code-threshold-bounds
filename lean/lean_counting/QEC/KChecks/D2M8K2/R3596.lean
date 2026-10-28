import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14384 = true := by
  decide +kernel

theorem tot14384 : totK PD2M8K2 D2M8K2.t14384 = [0, 50798055242, 306720165665, 410826254364, 147566293465, 9631076594, 0, 0] := by
  decide +kernel

theorem rows14385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14385 = true := by
  decide +kernel

theorem tot14385 : totK PD2M8K2 D2M8K2.t14385 = [0, 0, 210507033231, 497466558637, 189821711579, 5382912678, 0, 0] := by
  decide +kernel

theorem rows14386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14386 = true := by
  decide +kernel

theorem tot14386 : totK PD2M8K2 D2M8K2.t14386 = [0, 171193259871, 448034255313, 259465982296, 29469449459, 0, 0, 0] := by
  decide +kernel

theorem rows14387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14387 = true := by
  decide +kernel

theorem tot14387 : totK PD2M8K2 D2M8K2.t14387 = [0, 180198569276, 456897867362, 249722891759, 17531572211, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
