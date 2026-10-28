import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8872 = true := by
  decide +kernel

theorem tot8872 : totK PD2M8K2 D2M8K2.t8872 = [161631825924, 451466366641, 272489663855, 19735437758, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8873 = true := by
  decide +kernel

theorem tot8873 : totK PD2M8K2 D2M8K2.t8873 = [77144291610, 375825933288, 408340126616, 67164036368, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8874 = true := by
  decide +kernel

theorem tot8874 : totK PD2M8K2 D2M8K2.t8874 = [71220017884, 255385984102, 389221717058, 149638155335, 10536635055, 0, 0, 0] := by
  decide +kernel

theorem rows8875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8875 = true := by
  decide +kernel

theorem tot8875 : totK PD2M8K2 D2M8K2.t8875 = [182899090761, 471878605712, 256045983328, 23377943564, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
