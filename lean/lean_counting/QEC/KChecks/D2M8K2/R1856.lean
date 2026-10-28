import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7424 = true := by
  decide +kernel

theorem tot7424 : totK PD2M8K2 D2M8K2.t7424 = [0, 187857492270, 449882901884, 236354577133, 20180147233, 0, 0, 0] := by
  decide +kernel

theorem rows7425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7425 = true := by
  decide +kernel

theorem tot7425 : totK PD2M8K2 D2M8K2.t7425 = [0, 75207221427, 362738920768, 380831112833, 76117832946, 1096505104, 0, 0] := by
  decide +kernel

theorem rows7426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7426 = true := by
  decide +kernel

theorem tot7426 : totK PD2M8K2 D2M8K2.t7426 = [0, 0, 295713615873, 517645940195, 96548570939, 1069412848, 0, 0] := by
  decide +kernel

theorem rows7427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7427 = true := by
  decide +kernel

theorem tot7427 : totK PD2M8K2 D2M8K2.t7427 = [0, 0, 185221796248, 463015863679, 213661230467, 12554737991, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
