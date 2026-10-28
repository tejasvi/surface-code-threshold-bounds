import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8096 = true := by
  decide +kernel

theorem tot8096 : totK PD2M8K2 D2M8K2.t8096 = [0, 0, 202145108337, 480414123136, 181763485121, 7430810494, 0, 0] := by
  decide +kernel

theorem rows8097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8097 = true := by
  decide +kernel

theorem tot8097 : totK PD2M8K2 D2M8K2.t8097 = [0, 0, 158250956219, 431686302904, 298561912087, 35405910377, 0, 0] := by
  decide +kernel

theorem rows8098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8098 = true := by
  decide +kernel

theorem tot8098 : totK PD2M8K2 D2M8K2.t8098 = [0, 0, 187602427053, 470200617634, 233494710757, 11938963882, 0, 0] := by
  decide +kernel

theorem rows8099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8099 = true := by
  decide +kernel

theorem tot8099 : totK PD2M8K2 D2M8K2.t8099 = [0, 0, 104921639727, 434184545075, 345100261865, 35676027311, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
