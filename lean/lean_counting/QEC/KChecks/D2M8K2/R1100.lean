import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4400 = true := by
  decide +kernel

theorem tot4400 : totK PD2M8K2 D2M8K2.t4400 = [0, 0, 193120172031, 478156138409, 188921006023, 11873025674, 0, 0] := by
  decide +kernel

theorem rows4401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4401 = true := by
  decide +kernel

theorem tot4401 : totK PD2M8K2 D2M8K2.t4401 = [0, 179370853151, 449860469689, 284123080176, 33947000221, 0, 0, 0] := by
  decide +kernel

theorem rows4402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4402 = true := by
  decide +kernel

theorem tot4402 : totK PD2M8K2 D2M8K2.t4402 = [0, 167668652401, 464693860989, 265524814319, 16308239940, 0, 0, 0] := by
  decide +kernel

theorem rows4403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4403 = true := by
  decide +kernel

theorem tot4403 : totK PD2M8K2 D2M8K2.t4403 = [0, 0, 252620571761, 497194980037, 153882589498, 6837044869, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
