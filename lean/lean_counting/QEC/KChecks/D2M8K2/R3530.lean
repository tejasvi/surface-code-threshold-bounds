import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14120 = true := by
  decide +kernel

theorem tot14120 : totK PD2M8K2 D2M8K2.t14120 = [76982444091, 112097098977, 14294754615, 136458277937, 375286522700, 163540927763, 8304201444, 0] := by
  decide +kernel

theorem rows14121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14121 = true := by
  decide +kernel

theorem tot14121 : totK PD2M8K2 D2M8K2.t14121 = [184632646875, 489075213848, 218706895183, 9852138406, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14122 = true := by
  decide +kernel

theorem tot14122 : totK PD2M8K2 D2M8K2.t14122 = [171650519448, 460845256305, 238925432234, 13795945806, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14123 = true := by
  decide +kernel

theorem tot14123 : totK PD2M8K2 D2M8K2.t14123 = [0, 276658002869, 505057120010, 113350361876, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
