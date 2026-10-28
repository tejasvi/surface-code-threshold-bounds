import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3300 = true := by
  decide +kernel

theorem tot3300 : totK PD2M8K2 D2M8K2.t3300 = [0, 0, 173692966799, 454775604731, 255195921311, 25307930630, 0, 0] := by
  decide +kernel

theorem rows3301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3301 = true := by
  decide +kernel

theorem tot3301 : totK PD2M8K2 D2M8K2.t3301 = [0, 0, 194185571879, 504201132603, 201198132174, 5430665091, 0, 0] := by
  decide +kernel

theorem rows3302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3302 = true := by
  decide +kernel

theorem tot3302 : totK PD2M8K2 D2M8K2.t3302 = [0, 179003983631, 391286911657, 255604054926, 94903707956, 6761411919, 0, 0] := by
  decide +kernel

theorem rows3303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3303 = true := by
  decide +kernel

theorem tot3303 : totK PD2M8K2 D2M8K2.t3303 = [0, 167383000926, 475303404614, 246608773378, 13782726355, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
