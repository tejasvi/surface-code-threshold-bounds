import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6340 = true := by
  decide +kernel

theorem tot6340 : totK PD2M8K2 D2M8K2.t6340 = [0, 0, 208206209256, 479402408256, 182321284332, 11873025674, 0, 0] := by
  decide +kernel

theorem rows6341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6341 = true := by
  decide +kernel

theorem tot6341 : totK PD2M8K2 D2M8K2.t6341 = [0, 163102450447, 437688050930, 292843835281, 37607617248, 0, 0, 0] := by
  decide +kernel

theorem rows6342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6342 = true := by
  decide +kernel

theorem tot6342 : totK PD2M8K2 D2M8K2.t6342 = [0, 165067109471, 462709216162, 258140309356, 25200783376, 0, 0, 0] := by
  decide +kernel

theorem rows6343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6343 = true := by
  decide +kernel

theorem tot6343 : totK PD2M8K2 D2M8K2.t6343 = [0, 0, 220919577569, 490829502798, 162535035770, 5439011083, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
