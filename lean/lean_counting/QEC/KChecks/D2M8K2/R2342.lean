import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9368 = true := by
  decide +kernel

theorem tot9368 : totK PD2M8K2 D2M8K2.t9368 = [0, 159455433995, 405717662666, 295254864303, 67121983226, 2813333534, 0, 0] := by
  decide +kernel

theorem rows9369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9369 = true := by
  decide +kernel

theorem tot9369 : totK PD2M8K2 D2M8K2.t9369 = [0, 172980372552, 464813356111, 263863521790, 20250275926, 0, 0, 0] := by
  decide +kernel

theorem rows9370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9370 = true := by
  decide +kernel

theorem tot9370 : totK PD2M8K2 D2M8K2.t9370 = [0, 0, 230311638073, 511047975568, 158004338247, 2657953051, 0, 0] := by
  decide +kernel

theorem rows9371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9371 = true := by
  decide +kernel

theorem tot9371 : totK PD2M8K2 D2M8K2.t9371 = [0, 121847340634, 347970932226, 305363425297, 109449285443, 7072589504, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
