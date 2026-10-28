import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9652 = true := by
  decide +kernel

theorem tot9652 : totK PD2M8K2 D2M8K2.t9652 = [0, 0, 214533330393, 489376367917, 172372682567, 7938259948, 0, 0] := by
  decide +kernel

theorem rows9653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9653 = true := by
  decide +kernel

theorem tot9653 : totK PD2M8K2 D2M8K2.t9653 = [0, 178868128735, 450448229298, 264822774589, 30586683198, 0, 0, 0] := by
  decide +kernel

theorem rows9654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9654 = true := by
  decide +kernel

theorem tot9654 : totK PD2M8K2 D2M8K2.t9654 = [0, 196986279015, 484034667410, 215063147542, 11351058633, 0, 0, 0] := by
  decide +kernel

theorem rows9655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9655 = true := by
  decide +kernel

theorem tot9655 : totK PD2M8K2 D2M8K2.t9655 = [0, 37979066117, 324911297181, 445411390693, 95549388804, 1161838861, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
