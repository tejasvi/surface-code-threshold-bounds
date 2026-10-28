import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12720 = true := by
  decide +kernel

theorem tot12720 : totK PD2M8K2 D2M8K2.t12720 = [0, 182676119445, 451779017341, 273075984180, 29032602450, 0, 0, 0] := by
  decide +kernel

theorem rows12721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12721 = true := by
  decide +kernel

theorem tot12721 : totK PD2M8K2 D2M8K2.t12721 = [0, 171664145203, 459183577170, 245327615295, 13861179095, 0, 0, 0] := by
  decide +kernel

theorem rows12722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12722 = true := by
  decide +kernel

theorem tot12722 : totK PD2M8K2 D2M8K2.t12722 = [0, 0, 246118276111, 502664939456, 144623550279, 5984565558, 0, 0] := by
  decide +kernel

theorem rows12723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12723 = true := by
  decide +kernel

theorem tot12723 : totK PD2M8K2 D2M8K2.t12723 = [0, 65882149240, 276423770654, 394612249185, 125819531265, 5852844445, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
