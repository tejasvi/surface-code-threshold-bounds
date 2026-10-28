import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t776 = true := by
  decide +kernel

theorem tot776 : totK PD2M8K2 D2M8K2.t776 = [0, 0, 280465745738, 502032612330, 111857938173, 1268739303, 0, 0] := by
  decide +kernel

theorem rows777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t777 = true := by
  decide +kernel

theorem tot777 : totK PD2M8K2 D2M8K2.t777 = [0, 0, 203836053927, 485316855723, 187075742529, 7432205575, 0, 0] := by
  decide +kernel

theorem rows778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t778 = true := by
  decide +kernel

theorem tot778 : totK PD2M8K2 D2M8K2.t778 = [0, 0, 220346310549, 489772870043, 168877112209, 6319091252, 0, 0] := by
  decide +kernel

theorem rows779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t779 = true := by
  decide +kernel

theorem tot779 : totK PD2M8K2 D2M8K2.t779 = [0, 0, 187373332383, 468001255425, 194561723364, 12109972807, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
