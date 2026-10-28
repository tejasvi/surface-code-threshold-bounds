import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11248 = true := by
  decide +kernel

theorem tot11248 : totK PD2M8K2 D2M8K2.t11248 = [0, 176585565785, 457834182420, 243743481665, 16922139602, 0, 0, 0] := by
  decide +kernel

theorem rows11249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11249 = true := by
  decide +kernel

theorem tot11249 : totK PD2M8K2 D2M8K2.t11249 = [0, 48383029617, 398138338512, 415941725262, 43926756043, 0, 0, 0] := by
  decide +kernel

theorem rows11250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11250 = true := by
  decide +kernel

theorem tot11250 : totK PD2M8K2 D2M8K2.t11250 = [0, 51466644421, 313729420007, 427674460220, 96521019674, 1415142070, 0, 0] := by
  decide +kernel

theorem rows11251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11251 = true := by
  decide +kernel

theorem tot11251 : totK PD2M8K2 D2M8K2.t11251 = [0, 176019453837, 443409430182, 272397192668, 28380708235, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
