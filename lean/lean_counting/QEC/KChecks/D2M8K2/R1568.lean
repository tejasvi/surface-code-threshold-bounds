import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6272 = true := by
  decide +kernel

theorem tot6272 : totK PD2M8K2 D2M8K2.t6272 = [0, 162778534594, 480972881051, 241703086710, 9218696319, 0, 0, 0] := by
  decide +kernel

theorem rows6273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6273 = true := by
  decide +kernel

theorem tot6273 : totK PD2M8K2 D2M8K2.t6273 = [123222801663, 352314877131, 310620916248, 114972365703, 6804944647, 0, 0, 0] := by
  decide +kernel

theorem rows6274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6274 = true := by
  decide +kernel

theorem tot6274 : totK PD2M8K2 D2M8K2.t6274 = [173101368068, 438087008579, 271462622155, 30183638042, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6275 = true := by
  decide +kernel

theorem tot6275 : totK PD2M8K2 D2M8K2.t6275 = [126573718153, 442762677267, 312914990041, 26114024681, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
