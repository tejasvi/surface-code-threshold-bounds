import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3632 = true := by
  decide +kernel

theorem tot3632 : totK PD2M8K2 D2M8K2.t3632 = [0, 181224607590, 456357305475, 250589748741, 22762265210, 0, 0, 0] := by
  decide +kernel

theorem rows3633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3633 = true := by
  decide +kernel

theorem tot3633 : totK PD2M8K2 D2M8K2.t3633 = [0, 169940564109, 452343366332, 248079058955, 18068955215, 0, 0, 0] := by
  decide +kernel

theorem rows3634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3634 = true := by
  decide +kernel

theorem tot3634 : totK PD2M8K2 D2M8K2.t3634 = [0, 0, 302697623828, 492207791908, 92192128244, 1096505104, 0, 0] := by
  decide +kernel

theorem rows3635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3635 = true := by
  decide +kernel

theorem tot3635 : totK PD2M8K2 D2M8K2.t3635 = [0, 66937727143, 302822351218, 401144614905, 110479830565, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
