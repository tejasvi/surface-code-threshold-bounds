import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6408 = true := by
  decide +kernel

theorem tot6408 : totK PD2M8K2 D2M8K2.t6408 = [0, 0, 194897358714, 481126738906, 170305549590, 6101825179, 0, 0] := by
  decide +kernel

theorem rows6409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6409 = true := by
  decide +kernel

theorem tot6409 : totK PD2M8K2 D2M8K2.t6409 = [0, 0, 0, 326420080542, 426796987765, 63314734305, 1103454931, 0] := by
  decide +kernel

theorem rows6410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6410 = true := by
  decide +kernel

theorem tot6410 : totK PD2M8K2 D2M8K2.t6410 = [0, 0, 178006512081, 465049564418, 236268654924, 15063360013, 0, 0] := by
  decide +kernel

theorem rows6411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6411 = true := by
  decide +kernel

theorem tot6411 : totK PD2M8K2 D2M8K2.t6411 = [0, 0, 233671010212, 477745406116, 186722102193, 6725739876, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
