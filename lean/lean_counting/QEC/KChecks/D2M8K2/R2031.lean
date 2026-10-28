import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8124 = true := by
  decide +kernel

theorem tot8124 : totK PD2M8K2 D2M8K2.t8124 = [0, 163609321401, 372376562700, 258965957461, 102589288724, 6800370819, 0, 0] := by
  decide +kernel

theorem rows8125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8125 = true := by
  decide +kernel

theorem tot8125 : totK PD2M8K2 D2M8K2.t8125 = [0, 166008462763, 442756289576, 282906614746, 30173504110, 0, 0, 0] := by
  decide +kernel

theorem rows8126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8126 = true := by
  decide +kernel

theorem tot8126 : totK PD2M8K2 D2M8K2.t8126 = [0, 107725059663, 432306776759, 334759939796, 28948284997, 0, 0, 0] := by
  decide +kernel

theorem rows8127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8127 = true := by
  decide +kernel

theorem tot8127 : totK PD2M8K2 D2M8K2.t8127 = [0, 0, 212615003803, 491107702516, 183332776652, 9587713104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
