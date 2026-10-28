import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9156 = true := by
  decide +kernel

theorem tot9156 : totK PD2M8K2 D2M8K2.t9156 = [140390059244, 433793977511, 299819544468, 34575702040, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9157 = true := by
  decide +kernel

theorem tot9157 : totK PD2M8K2 D2M8K2.t9157 = [174405477553, 453033695515, 237462228976, 13821495057, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9158 = true := by
  decide +kernel

theorem tot9158 : totK PD2M8K2 D2M8K2.t9158 = [65009544155, 315831916644, 412168877735, 91566151386, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows9159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9159 = true := by
  decide +kernel

theorem tot9159 : totK PD2M8K2 D2M8K2.t9159 = [0, 196287766359, 464645248200, 185183668784, 11885407614, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
