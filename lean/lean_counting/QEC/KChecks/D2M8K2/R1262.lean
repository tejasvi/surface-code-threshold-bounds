import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5048 = true := by
  decide +kernel

theorem tot5048 : totK PD2M8K2 D2M8K2.t5048 = [0, 170301832614, 449786259768, 257973374139, 27620205570, 0, 0, 0] := by
  decide +kernel

theorem rows5049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5049 = true := by
  decide +kernel

theorem tot5049 : totK PD2M8K2 D2M8K2.t5049 = [0, 159872292344, 436971572941, 276552091940, 25569386751, 0, 0, 0] := by
  decide +kernel

theorem rows5050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5050 = true := by
  decide +kernel

theorem tot5050 : totK PD2M8K2 D2M8K2.t5050 = [0, 91718010228, 353009327108, 360757042582, 73921734546, 1096505104, 0, 0] := by
  decide +kernel

theorem rows5051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5051 = true := by
  decide +kernel

theorem tot5051 : totK PD2M8K2 D2M8K2.t5051 = [0, 0, 296784998645, 515056905495, 98547386130, 1069412848, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
