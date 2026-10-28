import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15756 = true := by
  decide +kernel

theorem tot15756 : totK PD2M8K2 D2M8K2.t15756 = [0, 0, 148720334287, 454663276407, 274029676374, 17994250727, 0, 0] := by
  decide +kernel

theorem rows15757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15757 = true := by
  decide +kernel

theorem tot15757 : totK PD2M8K2 D2M8K2.t15757 = [0, 0, 0, 281926936702, 496391904251, 95682986094, 2145173282, 0] := by
  decide +kernel

theorem rows15758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15758 = true := by
  decide +kernel

theorem tot15758 : totK PD2M8K2 D2M8K2.t15758 = [0, 0, 169628554409, 426143601757, 235761258838, 49307539961, 2481160468, 0] := by
  decide +kernel

theorem rows15759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15759 = true := by
  decide +kernel

theorem tot15759 : totK PD2M8K2 D2M8K2.t15759 = [0, 0, 159220811529, 444696259871, 273559494256, 20994103364, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
