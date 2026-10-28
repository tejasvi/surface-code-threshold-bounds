import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12588 = true := by
  decide +kernel

theorem tot12588 : totK PD2M8K2 D2M8K2.t12588 = [0, 0, 171193335882, 475693437165, 218718929636, 10926248329, 0, 0] := by
  decide +kernel

theorem rows12589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12589 = true := by
  decide +kernel

theorem tot12589 : totK PD2M8K2 D2M8K2.t12589 = [0, 0, 157891049441, 477182719552, 231671600458, 12492161858, 0, 0] := by
  decide +kernel

theorem rows12590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12590 = true := by
  decide +kernel

theorem tot12590 : totK PD2M8K2 D2M8K2.t12590 = [0, 0, 0, 299598011568, 463979350077, 79913215258, 1138244013, 0] := by
  decide +kernel

theorem rows12591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12591 = true := by
  decide +kernel

theorem tot12591 : totK PD2M8K2 D2M8K2.t12591 = [0, 0, 173438096905, 461730313135, 257168015237, 22931023829, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
