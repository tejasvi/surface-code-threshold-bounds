import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10988 = true := by
  decide +kernel

theorem tot10988 : totK PD2M8K2 D2M8K2.t10988 = [0, 281583479015, 515794718737, 102449784552, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows10989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10989 = true := by
  decide +kernel

theorem tot10989 : totK PD2M8K2 D2M8K2.t10989 = [88915620767, 333264795646, 358425707088, 99269897394, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows10990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10990 = true := by
  decide +kernel

theorem tot10990 : totK PD2M8K2 D2M8K2.t10990 = [189256799898, 451112414075, 250460398980, 27294555379, 0, 0, 0, 0] := by
  decide +kernel

theorem rows10991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10991 = true := by
  decide +kernel

theorem tot10991 : totK PD2M8K2 D2M8K2.t10991 = [104940257743, 396229464281, 350503066623, 40111784305, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
