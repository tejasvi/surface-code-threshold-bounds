import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3144 = true := by
  decide +kernel

theorem tot3144 : totK PD2M8K2 D2M8K2.t3144 = [0, 219545807751, 490407527182, 174815287759, 7279578938, 0, 0, 0] := by
  decide +kernel

theorem rows3145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3145 = true := by
  decide +kernel

theorem tot3145 : totK PD2M8K2 D2M8K2.t3145 = [0, 186058255732, 449069301061, 253331593873, 28382709664, 0, 0, 0] := by
  decide +kernel

theorem rows3146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3146 = true := by
  decide +kernel

theorem tot3146 : totK PD2M8K2 D2M8K2.t3146 = [0, 173685690905, 463406639629, 265227018314, 17316690801, 0, 0, 0] := by
  decide +kernel

theorem rows3147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3147 = true := by
  decide +kernel

theorem tot3147 : totK PD2M8K2 D2M8K2.t3147 = [0, 176191278966, 469195044557, 253857187188, 14752274202, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
