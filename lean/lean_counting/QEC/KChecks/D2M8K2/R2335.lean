import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9340 = true := by
  decide +kernel

theorem tot9340 : totK PD2M8K2 D2M8K2.t9340 = [0, 87591894987, 344075283335, 380670560236, 78677093123, 1268739303, 0, 0] := by
  decide +kernel

theorem rows9341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9341 = true := by
  decide +kernel

theorem tot9341 : totK PD2M8K2 D2M8K2.t9341 = [0, 0, 298909703396, 505947147004, 102530417307, 1369820453, 0, 0] := by
  decide +kernel

theorem rows9342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9342 = true := by
  decide +kernel

theorem tot9342 : totK PD2M8K2 D2M8K2.t9342 = [0, 0, 166603768066, 453322654800, 213617717594, 16516604865, 0, 0] := by
  decide +kernel

theorem rows9343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9343 = true := by
  decide +kernel

theorem tot9343 : totK PD2M8K2 D2M8K2.t9343 = [0, 0, 164072893226, 468368213093, 221186990270, 11124903123, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
