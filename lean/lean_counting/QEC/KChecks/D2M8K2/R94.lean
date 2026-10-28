import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t376 = true := by
  decide +kernel

theorem tot376 : totK PD2M8K2 D2M8K2.t376 = [0, 175521683754, 483527858903, 234157231410, 10008533666, 0, 0, 0] := by
  decide +kernel

theorem rows377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t377 = true := by
  decide +kernel

theorem tot377 : totK PD2M8K2 D2M8K2.t377 = [0, 0, 260322814246, 483558334915, 123978635248, 2305904642, 0, 0] := by
  decide +kernel

theorem rows378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t378 = true := by
  decide +kernel

theorem tot378 : totK PD2M8K2 D2M8K2.t378 = [0, 51694275795, 249884733370, 387641499016, 152248103995, 10710292732, 0, 0] := by
  decide +kernel

theorem rows379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t379 = true := by
  decide +kernel

theorem tot379 : totK PD2M8K2 D2M8K2.t379 = [0, 202511957096, 476952613684, 212063333919, 11056080877, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
