import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2664 = true := by
  decide +kernel

theorem tot2664 : totK PD2M8K2 D2M8K2.t2664 = [0, 183106467492, 429907252943, 288721760919, 39092638573, 0, 0, 0] := by
  decide +kernel

theorem rows2665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2665 = true := by
  decide +kernel

theorem tot2665 : totK PD2M8K2 D2M8K2.t2665 = [0, 159720975415, 468993353040, 253370088519, 15991651849, 0, 0, 0] := by
  decide +kernel

theorem rows2666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2666 = true := by
  decide +kernel

theorem tot2666 : totK PD2M8K2 D2M8K2.t2666 = [0, 88183717169, 349315947169, 362857604107, 102146007305, 13135812311, 0, 0] := by
  decide +kernel

theorem rows2667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2667 = true := by
  decide +kernel

theorem tot2667 : totK PD2M8K2 D2M8K2.t2667 = [0, 0, 162199455996, 457238975489, 262030584388, 16185273316, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
