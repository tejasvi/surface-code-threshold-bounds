import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16324 = true := by
  decide +kernel

theorem tot16324 : totK PD2M8K2 D2M8K2.t16324 = [0, 0, 193313337400, 481059555925, 222224429649, 12423165040, 0, 0] := by
  decide +kernel

theorem rows16325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16325 = true := by
  decide +kernel

theorem tot16325 : totK PD2M8K2 D2M8K2.t16325 = [0, 0, 38150555787, 322274537912, 450714570748, 86979571627, 1198073392, 0] := by
  decide +kernel

theorem rows16326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16326 = true := by
  decide +kernel

theorem tot16326 : totK PD2M8K2 D2M8K2.t16326 = [0, 0, 0, 209114252620, 485389812945, 170741240917, 7701383478, 0] := by
  decide +kernel

theorem rows16327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16327 = true := by
  decide +kernel

theorem tot16327 : totK PD2M8K2 D2M8K2.t16327 = [0, 0, 162911924887, 453026900347, 268474471766, 28995529854, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
