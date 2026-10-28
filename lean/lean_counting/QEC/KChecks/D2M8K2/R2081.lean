import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8324 = true := by
  decide +kernel

theorem tot8324 : totK PD2M8K2 D2M8K2.t8324 = [140377068119, 441381198129, 282986161431, 23499603744, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8325 = true := by
  decide +kernel

theorem tot8325 : totK PD2M8K2 D2M8K2.t8325 = [0, 218582211125, 485760982862, 163163897794, 7166294683, 0, 0, 0] := by
  decide +kernel

theorem rows8326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8326 = true := by
  decide +kernel

theorem tot8326 : totK PD2M8K2 D2M8K2.t8326 = [85190975889, 309295373863, 364117770132, 108700596288, 5883432551, 0, 0, 0] := by
  decide +kernel

theorem rows8327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8327 = true := by
  decide +kernel

theorem tot8327 : totK PD2M8K2 D2M8K2.t8327 = [171979095055, 457309310425, 264197429131, 26606411483, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
