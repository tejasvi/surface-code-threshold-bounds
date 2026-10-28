import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14400 = true := by
  decide +kernel

theorem tot14400 : totK PD2M8K2 D2M8K2.t14400 = [0, 0, 178227003719, 475750518348, 221596612363, 10920774989, 0, 0] := by
  decide +kernel

theorem rows14401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14401 = true := by
  decide +kernel

theorem tot14401 : totK PD2M8K2 D2M8K2.t14401 = [0, 0, 207062690618, 466492180114, 185005401980, 7811909438, 0, 0] := by
  decide +kernel

theorem rows14402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14402 = true := by
  decide +kernel

theorem tot14402 : totK PD2M8K2 D2M8K2.t14402 = [0, 0, 188456384331, 456059170155, 219218393492, 17854363044, 0, 0] := by
  decide +kernel

theorem rows14403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14403 = true := by
  decide +kernel

theorem tot14403 : totK PD2M8K2 D2M8K2.t14403 = [0, 0, 91621921773, 390814214772, 314585918017, 43942237999, 1061529118, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
