import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9372 = true := by
  decide +kernel

theorem tot9372 : totK PD2M8K2 D2M8K2.t9372 = [0, 186341680448, 451464247113, 223122546087, 17045623460, 0, 0, 0] := by
  decide +kernel

theorem rows9373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9373 = true := by
  decide +kernel

theorem tot9373 : totK PD2M8K2 D2M8K2.t9373 = [0, 85971096469, 370689879876, 350453097042, 63554838375, 1310166938, 0, 0] := by
  decide +kernel

theorem rows9374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9374 = true := by
  decide +kernel

theorem tot9374 : totK PD2M8K2 D2M8K2.t9374 = [0, 15921317223, 310455738801, 500115393034, 67072850469, 0, 0, 0] := by
  decide +kernel

theorem rows9375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9375 = true := by
  decide +kernel

theorem tot9375 : totK PD2M8K2 D2M8K2.t9375 = [0, 164572824674, 443176521642, 276498059061, 30470231449, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
