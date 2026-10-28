import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1296 = true := by
  decide +kernel

theorem tot1296 : totK PD2M8K2 D2M8K2.t1296 = [92934196222, 345517634737, 377830485063, 79663047503, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows1297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1297 = true := by
  decide +kernel

theorem tot1297 : totK PD2M8K2 D2M8K2.t1297 = [0, 246955467276, 484275589624, 158680888296, 4761634222, 0, 0, 0] := by
  decide +kernel

theorem rows1298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1298 = true := by
  decide +kernel

theorem tot1298 : totK PD2M8K2 D2M8K2.t1298 = [0, 182163085273, 460988760081, 228052044539, 17381584168, 0, 0, 0] := by
  decide +kernel

theorem rows1299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1299 = true := by
  decide +kernel

theorem tot1299 : totK PD2M8K2 D2M8K2.t1299 = [0, 183567951525, 483744618423, 213296255917, 9713690252, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
