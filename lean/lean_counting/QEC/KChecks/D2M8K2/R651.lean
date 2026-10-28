import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2604 = true := by
  decide +kernel

theorem tot2604 : totK PD2M8K2 D2M8K2.t2604 = [0, 88511303760, 359119496849, 370902226221, 70555836911, 1310285577, 0, 0] := by
  decide +kernel

theorem rows2605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2605 = true := by
  decide +kernel

theorem tot2605 : totK PD2M8K2 D2M8K2.t2605 = [0, 93375087334, 386118108520, 394455270676, 45811749215, 0, 0, 0] := by
  decide +kernel

theorem rows2606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2606 = true := by
  decide +kernel

theorem tot2606 : totK PD2M8K2 D2M8K2.t2606 = [0, 173931812376, 446218029481, 266165554398, 21185424687, 0, 0, 0] := by
  decide +kernel

theorem rows2607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2607 = true := by
  decide +kernel

theorem tot2607 : totK PD2M8K2 D2M8K2.t2607 = [0, 162313943983, 477986627734, 266574911938, 13387643949, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
