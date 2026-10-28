import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1092 = true := by
  decide +kernel

theorem tot1092 : totK PD2M8K2 D2M8K2.t1092 = [0, 175102991095, 473194874898, 246991937572, 14591369033, 0, 0, 0] := by
  decide +kernel

theorem rows1093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1093 = true := by
  decide +kernel

theorem tot1093 : totK PD2M8K2 D2M8K2.t1093 = [0, 73831062077, 328907876571, 369348440981, 130219021786, 15864095392, 0, 0] := by
  decide +kernel

theorem rows1094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1094 = true := by
  decide +kernel

theorem tot1094 : totK PD2M8K2 D2M8K2.t1094 = [0, 0, 175826685073, 461321327346, 238612318291, 13530797253, 0, 0] := by
  decide +kernel

theorem rows1095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1095 = true := by
  decide +kernel

theorem tot1095 : totK PD2M8K2 D2M8K2.t1095 = [0, 52698856147, 232699534451, 415000502830, 191527228978, 8104085798, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
