import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2120 = true := by
  decide +kernel

theorem tot2120 : totK PD2M8K2 D2M8K2.t2120 = [0, 177877115015, 475164743526, 238923493110, 12526962336, 0, 0, 0] := by
  decide +kernel

theorem rows2121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2121 = true := by
  decide +kernel

theorem tot2121 : totK PD2M8K2 D2M8K2.t2121 = [0, 0, 277522549205, 518978546642, 101178723701, 1096505104, 0, 0] := by
  decide +kernel

theorem rows2122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2122 = true := by
  decide +kernel

theorem tot2122 : totK PD2M8K2 D2M8K2.t2122 = [0, 91504863424, 344728727185, 360732094256, 97137420281, 3884009855, 0, 0] := by
  decide +kernel

theorem rows2123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2123 = true := by
  decide +kernel

theorem tot2123 : totK PD2M8K2 D2M8K2.t2123 = [0, 196246912513, 459162344276, 215321786257, 17033427234, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
