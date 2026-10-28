import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7708 = true := by
  decide +kernel

theorem tot7708 : totK PD2M8K2 D2M8K2.t7708 = [0, 0, 0, 210228064378, 475426319242, 183679304069, 11885407614, 0] := by
  decide +kernel

theorem rows7709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7709 = true := by
  decide +kernel

theorem tot7709 : totK PD2M8K2 D2M8K2.t7709 = [0, 0, 177978768650, 437413997845, 254456687611, 25304066943, 0, 0] := by
  decide +kernel

theorem rows7710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7710 = true := by
  decide +kernel

theorem tot7710 : totK PD2M8K2 D2M8K2.t7710 = [0, 0, 202612821693, 468434715007, 207316117864, 12146368384, 0, 0] := by
  decide +kernel

theorem rows7711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7711 = true := by
  decide +kernel

theorem tot7711 : totK PD2M8K2 D2M8K2.t7711 = [0, 0, 36108306995, 330877777193, 430661183371, 74400004025, 1062926506, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
