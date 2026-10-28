import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12572 = true := by
  decide +kernel

theorem tot12572 : totK PD2M8K2 D2M8K2.t12572 = [0, 176185809682, 459533257977, 257695727717, 23583287795, 0, 0, 0] := by
  decide +kernel

theorem rows12573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12573 = true := by
  decide +kernel

theorem tot12573 : totK PD2M8K2 D2M8K2.t12573 = [0, 117450842066, 443104100244, 316461383650, 34277809806, 0, 0, 0] := by
  decide +kernel

theorem rows12574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12574 = true := by
  decide +kernel

theorem tot12574 : totK PD2M8K2 D2M8K2.t12574 = [0, 0, 170831630448, 463495400372, 243089973879, 18697524080, 0, 0] := by
  decide +kernel

theorem rows12575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12575 = true := by
  decide +kernel

theorem tot12575 : totK PD2M8K2 D2M8K2.t12575 = [0, 85167078157, 297735954895, 354846896075, 146047592159, 5430665091, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
