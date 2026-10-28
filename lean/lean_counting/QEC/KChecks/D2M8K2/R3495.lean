import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13980 = true := by
  decide +kernel

theorem tot13980 : totK PD2M8K2 D2M8K2.t13980 = [0, 0, 85831680626, 397927601858, 372706838839, 36559087434, 0, 0] := by
  decide +kernel

theorem rows13981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13981 = true := by
  decide +kernel

theorem tot13981 : totK PD2M8K2 D2M8K2.t13981 = [0, 0, 0, 217950635576, 492990401214, 147745523833, 5067863418, 0] := by
  decide +kernel

theorem rows13982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13982 = true := by
  decide +kernel

theorem tot13982 : totK PD2M8K2 D2M8K2.t13982 = [0, 0, 190191371522, 448222570613, 245403037623, 28168177308, 0, 0] := by
  decide +kernel

theorem rows13983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13983 = true := by
  decide +kernel

theorem tot13983 : totK PD2M8K2 D2M8K2.t13983 = [0, 0, 190857575742, 467502083433, 217459709153, 9121934200, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
