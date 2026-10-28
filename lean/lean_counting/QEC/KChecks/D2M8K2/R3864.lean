import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15456 = true := by
  decide +kernel

theorem tot15456 : totK PD2M8K2 D2M8K2.t15456 = [0, 0, 191115995338, 480635963777, 212405426580, 13718472383, 0, 0] := by
  decide +kernel

theorem rows15457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15457 = true := by
  decide +kernel

theorem tot15457 : totK PD2M8K2 D2M8K2.t15457 = [0, 0, 163828516870, 480896424762, 236695415920, 10840514936, 0, 0] := by
  decide +kernel

theorem rows15458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15458 = true := by
  decide +kernel

theorem tot15458 : totK PD2M8K2 D2M8K2.t15458 = [0, 0, 181440704243, 460330266006, 248397741938, 18246066036, 0, 0] := by
  decide +kernel

theorem rows15459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15459 = true := by
  decide +kernel

theorem tot15459 : totK PD2M8K2 D2M8K2.t15459 = [0, 0, 212116998742, 482882632940, 192902622555, 7631604836, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
