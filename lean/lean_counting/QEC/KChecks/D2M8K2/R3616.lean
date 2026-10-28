import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14464 = true := by
  decide +kernel

theorem tot14464 : totK PD2M8K2 D2M8K2.t14464 = [161062362423, 394577650346, 288123143424, 66078865291, 2410802975, 0, 0, 0] := by
  decide +kernel

theorem rows14465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14465 = true := by
  decide +kernel

theorem tot14465 : totK PD2M8K2 D2M8K2.t14465 = [157730628328, 441032057140, 287867561236, 30618259789, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14466 = true := by
  decide +kernel

theorem tot14466 : totK PD2M8K2 D2M8K2.t14466 = [106316469095, 411117279003, 337216688081, 37947495766, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14467 = true := by
  decide +kernel

theorem tot14467 : totK PD2M8K2 D2M8K2.t14467 = [0, 224271517676, 481764925270, 179410935832, 9661765460, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
