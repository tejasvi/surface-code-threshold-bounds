import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6068 = true := by
  decide +kernel

theorem tot6068 : totK PD2M8K2 D2M8K2.t6068 = [0, 17310721512, 196818286848, 456672738250, 189002488182, 11885407614, 0, 0] := by
  decide +kernel

theorem rows6069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6069 = true := by
  decide +kernel

theorem tot6069 : totK PD2M8K2 D2M8K2.t6069 = [0, 192520490312, 456109805457, 240282914843, 23191563963, 0, 0, 0] := by
  decide +kernel

theorem rows6070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6070 = true := by
  decide +kernel

theorem tot6070 : totK PD2M8K2 D2M8K2.t6070 = [0, 169694819981, 474056582810, 238771017242, 12505175780, 0, 0, 0] := by
  decide +kernel

theorem rows6071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6071 = true := by
  decide +kernel

theorem tot6071 : totK PD2M8K2 D2M8K2.t6071 = [0, 0, 268139263037, 495800857677, 114270541827, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
