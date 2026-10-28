import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1156 = true := by
  decide +kernel

theorem tot1156 : totK PD2M8K2 D2M8K2.t1156 = [0, 0, 204285407494, 475328146851, 178577856193, 11780292382, 0, 0] := by
  decide +kernel

theorem rows1157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1157 = true := by
  decide +kernel

theorem tot1157 : totK PD2M8K2 D2M8K2.t1157 = [0, 169478060999, 439304949108, 260643798715, 24721669237, 0, 0, 0] := by
  decide +kernel

theorem rows1158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1158 = true := by
  decide +kernel

theorem tot1158 : totK PD2M8K2 D2M8K2.t1158 = [0, 180462386115, 469421763878, 240274510530, 14293708650, 0, 0, 0] := by
  decide +kernel

theorem rows1159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1159 = true := by
  decide +kernel

theorem tot1159 : totK PD2M8K2 D2M8K2.t1159 = [0, 66011893307, 322482603080, 399404641367, 83002545624, 1162740214, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
