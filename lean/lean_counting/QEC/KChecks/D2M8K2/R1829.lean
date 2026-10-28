import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7316 = true := by
  decide +kernel

theorem tot7316 : totK PD2M8K2 D2M8K2.t7316 = [0, 139507717382, 365188951255, 291060312602, 83066925340, 2348208889, 0, 0] := by
  decide +kernel

theorem rows7317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7317 = true := by
  decide +kernel

theorem tot7317 : totK PD2M8K2 D2M8K2.t7317 = [0, 172709818768, 431798520268, 280515937100, 30509842242, 0, 0, 0] := by
  decide +kernel

theorem rows7318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7318 = true := by
  decide +kernel

theorem tot7318 : totK PD2M8K2 D2M8K2.t7318 = [0, 105375231182, 415964317436, 323397001907, 34115331695, 0, 0, 0] := by
  decide +kernel

theorem rows7319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7319 = true := by
  decide +kernel

theorem tot7319 : totK PD2M8K2 D2M8K2.t7319 = [0, 0, 313084891864, 524523222967, 82617952132, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
