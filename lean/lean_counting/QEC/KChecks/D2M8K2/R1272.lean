import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5088 = true := by
  decide +kernel

theorem tot5088 : totK PD2M8K2 D2M8K2.t5088 = [0, 176186573368, 439637135368, 278498203925, 30265018328, 0, 0, 0] := by
  decide +kernel

theorem rows5089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5089 = true := by
  decide +kernel

theorem tot5089 : totK PD2M8K2 D2M8K2.t5089 = [0, 92932490688, 420480255127, 345029695614, 36320523458, 0, 0, 0] := by
  decide +kernel

theorem rows5090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5090 = true := by
  decide +kernel

theorem tot5090 : totK PD2M8K2 D2M8K2.t5090 = [0, 0, 299210940157, 527704586951, 95262862024, 1096505104, 0, 0] := by
  decide +kernel

theorem rows5091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5091 = true := by
  decide +kernel

theorem tot5091 : totK PD2M8K2 D2M8K2.t5091 = [0, 0, 212959603619, 493154352322, 172046214615, 5253830308, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
