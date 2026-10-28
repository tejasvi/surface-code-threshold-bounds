import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2104 = true := by
  decide +kernel

theorem tot2104 : totK PD2M8K2 D2M8K2.t2104 = [0, 0, 145606561253, 458282912521, 290731288846, 21329352675, 0, 0] := by
  decide +kernel

theorem rows2105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2105 = true := by
  decide +kernel

theorem tot2105 : totK PD2M8K2 D2M8K2.t2105 = [0, 0, 0, 299825733373, 485313237527, 102656793346, 1242138600, 0] := by
  decide +kernel

theorem rows2106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2106 = true := by
  decide +kernel

theorem tot2106 : totK PD2M8K2 D2M8K2.t2106 = [0, 92075173518, 174953271121, 144522003218, 297447566286, 162275375658, 12610165304, 0] := by
  decide +kernel

theorem rows2107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2107 = true := by
  decide +kernel

theorem tot2107 : totK PD2M8K2 D2M8K2.t2107 = [0, 173924699396, 473534415773, 236747836780, 14566626306, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
