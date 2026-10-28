import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9476 = true := by
  decide +kernel

theorem tot9476 : totK PD2M8K2 D2M8K2.t9476 = [162436108136, 395387600269, 259690439483, 89482735149, 6804944647, 0, 0, 0] := by
  decide +kernel

theorem rows9477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9477 = true := by
  decide +kernel

theorem tot9477 : totK PD2M8K2 D2M8K2.t9477 = [203351083038, 480943057843, 211681280641, 11088596027, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9478 = true := by
  decide +kernel

theorem tot9478 : totK PD2M8K2 D2M8K2.t9478 = [15884411423, 314117607168, 477292436718, 99106238711, 1163840124, 0, 0, 0] := by
  decide +kernel

theorem rows9479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9479 = true := by
  decide +kernel

theorem tot9479 : totK PD2M8K2 D2M8K2.t9479 = [35914030162, 229477341115, 442810797649, 167072658111, 10722295415, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
