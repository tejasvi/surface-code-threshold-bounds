import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8488 = true := by
  decide +kernel

theorem tot8488 : totK PD2M8K2 D2M8K2.t8488 = [0, 0, 212899962354, 495603027699, 167125725921, 4882834716, 0, 0] := by
  decide +kernel

theorem rows8489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8489 = true := by
  decide +kernel

theorem tot8489 : totK PD2M8K2 D2M8K2.t8489 = [38616506213, 44737627256, 162354765108, 417671975754, 213010211568, 17014456371, 0, 0] := by
  decide +kernel

theorem rows8490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8490 = true := by
  decide +kernel

theorem tot8490 : totK PD2M8K2 D2M8K2.t8490 = [165689349726, 447436472970, 279116862582, 29900697905, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8491 = true := by
  decide +kernel

theorem tot8491 : totK PD2M8K2 D2M8K2.t8491 = [196400494532, 481238147526, 229132054704, 12044078933, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
