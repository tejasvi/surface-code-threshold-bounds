import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16124 = true := by
  decide +kernel

theorem tot16124 : totK PD2M8K2 D2M8K2.t16124 = [0, 0, 131660562327, 435991124741, 324639263745, 22462005653, 0, 0] := by
  decide +kernel

theorem rows16125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16125 = true := by
  decide +kernel

theorem tot16125 : totK PD2M8K2 D2M8K2.t16125 = [0, 0, 170667442881, 444335355568, 275435966070, 27893313732, 0, 0] := by
  decide +kernel

theorem rows16126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16126 = true := by
  decide +kernel

theorem tot16126 : totK PD2M8K2 D2M8K2.t16126 = [0, 0, 125579789091, 459363973551, 303882566903, 21305638271, 0, 0] := by
  decide +kernel

theorem rows16127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16127 = true := by
  decide +kernel

theorem tot16127 : totK PD2M8K2 D2M8K2.t16127 = [0, 0, 0, 240762223819, 513104940912, 133908367411, 1238673482, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
