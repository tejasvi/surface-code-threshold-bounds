import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16072 = true := by
  decide +kernel

theorem tot16072 : totK PD2M8K2 D2M8K2.t16072 = [0, 87932767747, 397740311435, 376657752355, 41634982881, 0, 0, 0] := by
  decide +kernel

theorem rows16073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16073 = true := by
  decide +kernel

theorem tot16073 : totK PD2M8K2 D2M8K2.t16073 = [0, 170872407726, 442483035794, 267000604151, 28239298656, 0, 0, 0] := by
  decide +kernel

theorem rows16074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16074 = true := by
  decide +kernel

theorem tot16074 : totK PD2M8K2 D2M8K2.t16074 = [0, 166260413610, 459392021903, 264278738611, 21888164621, 0, 0, 0] := by
  decide +kernel

theorem rows16075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16075 = true := by
  decide +kernel

theorem tot16075 : totK PD2M8K2 D2M8K2.t16075 = [0, 0, 239575713147, 505669030948, 145545299198, 2304167554, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
