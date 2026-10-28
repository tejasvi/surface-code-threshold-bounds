import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6440 = true := by
  decide +kernel

theorem tot6440 : totK PD2M8K2 D2M8K2.t6440 = [185908954030, 473631244060, 219854423541, 12534051746, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6441 = true := by
  decide +kernel

theorem tot6441 : totK PD2M8K2 D2M8K2.t6441 = [50403200865, 315006233671, 427068466411, 97721069935, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows6442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6442 = true := by
  decide +kernel

theorem tot6442 : totK PD2M8K2 D2M8K2.t6442 = [51598200566, 347697884858, 445853922011, 58750172096, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6443 = true := by
  decide +kernel

theorem tot6443 : totK PD2M8K2 D2M8K2.t6443 = [196545320008, 472155713406, 228529959239, 19192496613, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
