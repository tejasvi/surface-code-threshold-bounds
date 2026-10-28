import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11500 = true := by
  decide +kernel

theorem tot11500 : totK PD2M8K2 D2M8K2.t11500 = [0, 186315817484, 468684541893, 233000244996, 16921715641, 0, 0, 0] := by
  decide +kernel

theorem rows11501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11501 = true := by
  decide +kernel

theorem tot11501 : totK PD2M8K2 D2M8K2.t11501 = [0, 135869442139, 446257783495, 299881718521, 32643406053, 0, 0, 0] := by
  decide +kernel

theorem rows11502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11502 = true := by
  decide +kernel

theorem tot11502 : totK PD2M8K2 D2M8K2.t11502 = [0, 0, 175492762125, 443982355946, 257605389473, 25370006417, 0, 0] := by
  decide +kernel

theorem rows11503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11503 = true := by
  decide +kernel

theorem tot11503 : totK PD2M8K2 D2M8K2.t11503 = [0, 0, 196798173242, 497813595428, 201912900000, 5430665091, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
