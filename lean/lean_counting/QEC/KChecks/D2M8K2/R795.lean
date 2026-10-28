import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3180 = true := by
  decide +kernel

theorem tot3180 : totK PD2M8K2 D2M8K2.t3180 = [0, 293155563053, 486634687273, 96466361460, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows3181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3181 = true := by
  decide +kernel

theorem tot3181 : totK PD2M8K2 D2M8K2.t3181 = [83233391745, 315543276257, 385561637480, 107555929070, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows3182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3182 = true := by
  decide +kernel

theorem tot3182 : totK PD2M8K2 D2M8K2.t3182 = [155520641074, 448925276866, 274037344731, 24197527909, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3183 = true := by
  decide +kernel

theorem tot3183 : totK PD2M8K2 D2M8K2.t3183 = [182137505762, 466642454972, 253123092915, 18234373184, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
