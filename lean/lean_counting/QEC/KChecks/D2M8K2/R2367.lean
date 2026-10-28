import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9468 = true := by
  decide +kernel

theorem tot9468 : totK PD2M8K2 D2M8K2.t9468 = [0, 173122873919, 458746217022, 232533404001, 14858663033, 0, 0, 0] := by
  decide +kernel

theorem rows9469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9469 = true := by
  decide +kernel

theorem tot9469 : totK PD2M8K2 D2M8K2.t9469 = [0, 206411770972, 481988463849, 205360081220, 8394630506, 0, 0, 0] := by
  decide +kernel

theorem rows9470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9470 = true := by
  decide +kernel

theorem tot9470 : totK PD2M8K2 D2M8K2.t9470 = [0, 194793459532, 476938168474, 209663238046, 7870241454, 0, 0, 0] := by
  decide +kernel

theorem rows9471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9471 = true := by
  decide +kernel

theorem tot9471 : totK PD2M8K2 D2M8K2.t9471 = [145481999772, 321588545993, 306290886749, 142476606505, 13468148062, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
