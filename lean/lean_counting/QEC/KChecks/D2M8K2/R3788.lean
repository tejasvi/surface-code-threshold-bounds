import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15152 = true := by
  decide +kernel

theorem tot15152 : totK PD2M8K2 D2M8K2.t15152 = [0, 0, 208889684467, 483834848154, 188495300086, 11094071029, 0, 0] := by
  decide +kernel

theorem rows15153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15153 = true := by
  decide +kernel

theorem tot15153 : totK PD2M8K2 D2M8K2.t15153 = [0, 0, 185411227480, 463740654897, 205775746311, 12361325328, 0, 0] := by
  decide +kernel

theorem rows15154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15154 = true := by
  decide +kernel

theorem tot15154 : totK PD2M8K2 D2M8K2.t15154 = [0, 0, 19348689120, 327488972778, 441768288943, 73935247208, 1239866073, 0] := by
  decide +kernel

theorem rows15155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15155 = true := by
  decide +kernel

theorem tot15155 : totK PD2M8K2 D2M8K2.t15155 = [0, 0, 89157132500, 402310145478, 370055796301, 43491252366, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
