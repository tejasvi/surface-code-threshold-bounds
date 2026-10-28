import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6436 = true := by
  decide +kernel

theorem tot6436 : totK PD2M8K2 D2M8K2.t6436 = [0, 159992617153, 456963277664, 281347010082, 21404613672, 0, 0, 0] := by
  decide +kernel

theorem rows6437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6437 = true := by
  decide +kernel

theorem tot6437 : totK PD2M8K2 D2M8K2.t6437 = [0, 0, 237051691946, 506452002600, 147526608330, 2304167554, 0, 0] := by
  decide +kernel

theorem rows6438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6438 = true := by
  decide +kernel

theorem tot6438 : totK PD2M8K2 D2M8K2.t6438 = [0, 0, 175724839809, 462764091660, 223125434059, 12601226032, 0, 0] := by
  decide +kernel

theorem rows6439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6439 = true := by
  decide +kernel

theorem tot6439 : totK PD2M8K2 D2M8K2.t6439 = [193081648232, 461015719043, 201379668412, 17806483927, 24003257719, 7077058802, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
