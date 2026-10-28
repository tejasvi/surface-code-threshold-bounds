import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14088 = true := by
  decide +kernel

theorem tot14088 : totK PD2M8K2 D2M8K2.t14088 = [0, 19983817196, 276861503433, 499386235833, 107728431912, 1369150432, 0, 0] := by
  decide +kernel

theorem rows14089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14089 = true := by
  decide +kernel

theorem tot14089 : totK PD2M8K2 D2M8K2.t14089 = [0, 160969561908, 445115842278, 279660905877, 29963959770, 0, 0, 0] := by
  decide +kernel

theorem rows14090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14090 = true := by
  decide +kernel

theorem tot14090 : totK PD2M8K2 D2M8K2.t14090 = [0, 208091407215, 480414551329, 209982444359, 10230024217, 0, 0, 0] := by
  decide +kernel

theorem rows14091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14091 = true := by
  decide +kernel

theorem tot14091 : totK PD2M8K2 D2M8K2.t14091 = [0, 37815634106, 288261058203, 393015845763, 178409488824, 21391863750, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
