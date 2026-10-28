import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1480 = true := by
  decide +kernel

theorem tot1480 : totK PD2M8K2 D2M8K2.t1480 = [0, 0, 211062030741, 478727162198, 174881570365, 7680527984, 0, 0] := by
  decide +kernel

theorem rows1481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1481 = true := by
  decide +kernel

theorem tot1481 : totK PD2M8K2 D2M8K2.t1481 = [0, 86902333671, 338931822593, 377931676843, 82813270396, 976161439, 0, 0] := by
  decide +kernel

theorem rows1482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1482 = true := by
  decide +kernel

theorem tot1482 : totK PD2M8K2 D2M8K2.t1482 = [0, 178029660555, 457678873614, 263728918685, 25585357768, 0, 0, 0] := by
  decide +kernel

theorem rows1483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1483 = true := by
  decide +kernel

theorem tot1483 : totK PD2M8K2 D2M8K2.t1483 = [0, 182497872290, 474822227823, 246845826213, 15063670244, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
