import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8524 = true := by
  decide +kernel

theorem tot8524 : totK PD2M8K2 D2M8K2.t8524 = [0, 174259303987, 447147970388, 268436455758, 27722559372, 0, 0, 0] := by
  decide +kernel

theorem rows8525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8525 = true := by
  decide +kernel

theorem tot8525 : totK PD2M8K2 D2M8K2.t8525 = [0, 177234874609, 465611293634, 238818234599, 13884849637, 0, 0, 0] := by
  decide +kernel

theorem rows8526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8526 = true := by
  decide +kernel

theorem tot8526 : totK PD2M8K2 D2M8K2.t8526 = [0, 0, 331114791080, 507419422565, 59750759446, 0, 0, 0] := by
  decide +kernel

theorem rows8527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8527 = true := by
  decide +kernel

theorem tot8527 : totK PD2M8K2 D2M8K2.t8527 = [0, 156768896951, 380320773121, 292733922550, 76608406711, 1415142070, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
