import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t420 = true := by
  decide +kernel

theorem tot420 : totK PD2M8K2 D2M8K2.t420 = [0, 279159876209, 505288326748, 114451500537, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t421 = true := by
  decide +kernel

theorem tot421 : totK PD2M8K2 D2M8K2.t421 = [91232000980, 379077969607, 393157464422, 51297546070, 0, 0, 0, 0] := by
  decide +kernel

theorem rows422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t422 = true := by
  decide +kernel

theorem tot422 : totK PD2M8K2 D2M8K2.t422 = [207632924840, 463856011321, 224215036656, 17384837247, 0, 0, 0, 0] := by
  decide +kernel

theorem rows423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t423 = true := by
  decide +kernel

theorem tot423 : totK PD2M8K2 D2M8K2.t423 = [89410951224, 390928025915, 352044252634, 74996553610, 10443484490, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
