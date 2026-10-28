import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6360 = true := by
  decide +kernel

theorem tot6360 : totK PD2M8K2 D2M8K2.t6360 = [0, 176264834056, 391457805350, 255354782324, 84842037560, 4147651783, 0, 0] := by
  decide +kernel

theorem rows6361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6361 = true := by
  decide +kernel

theorem tot6361 : totK PD2M8K2 D2M8K2.t6361 = [0, 165471537364, 441696360805, 285312452023, 29714493348, 0, 0, 0] := by
  decide +kernel

theorem rows6362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6362 = true := by
  decide +kernel

theorem tot6362 : totK PD2M8K2 D2M8K2.t6362 = [0, 104271980057, 427788099064, 343136714213, 29966019556, 0, 0, 0] := by
  decide +kernel

theorem rows6363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6363 = true := by
  decide +kernel

theorem tot6363 : totK PD2M8K2 D2M8K2.t6363 = [0, 0, 216610801036, 492430487407, 180485946580, 9587713104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
