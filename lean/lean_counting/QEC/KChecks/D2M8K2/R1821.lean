import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7284 = true := by
  decide +kernel

theorem tot7284 : totK PD2M8K2 D2M8K2.t7284 = [0, 0, 177729483550, 467346856368, 249691813376, 15544291832, 0, 0] := by
  decide +kernel

theorem rows7285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7285 = true := by
  decide +kernel

theorem tot7285 : totK PD2M8K2 D2M8K2.t7285 = [0, 0, 181167941177, 455737898908, 228921954885, 17104814242, 0, 0] := by
  decide +kernel

theorem rows7286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7286 = true := by
  decide +kernel

theorem tot7286 : totK PD2M8K2 D2M8K2.t7286 = [0, 0, 74989312342, 355085916965, 393699756541, 70604293572, 1096505104, 0] := by
  decide +kernel

theorem rows7287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7287 = true := by
  decide +kernel

theorem tot7287 : totK PD2M8K2 D2M8K2.t7287 = [0, 0, 0, 277368561821, 513786799847, 97111436758, 1069412848, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
