import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4480 = true := by
  decide +kernel

theorem tot4480 : totK PD2M8K2 D2M8K2.t4480 = [0, 0, 198290636567, 478406796765, 190839671905, 11885407614, 0, 0] := by
  decide +kernel

theorem rows4481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4481 = true := by
  decide +kernel

theorem tot4481 : totK PD2M8K2 D2M8K2.t4481 = [0, 187260791026, 447484734702, 251828360198, 30396081039, 0, 0, 0] := by
  decide +kernel

theorem rows4482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4482 = true := by
  decide +kernel

theorem tot4482 : totK PD2M8K2 D2M8K2.t4482 = [0, 139955743058, 453851338236, 284123894013, 20085876647, 0, 0, 0] := by
  decide +kernel

theorem rows4483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4483 = true := by
  decide +kernel

theorem tot4483 : totK PD2M8K2 D2M8K2.t4483 = [0, 0, 264599914575, 484938159718, 148379533933, 8470662040, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
