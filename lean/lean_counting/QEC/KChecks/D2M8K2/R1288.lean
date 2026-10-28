import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5152 = true := by
  decide +kernel

theorem tot5152 : totK PD2M8K2 D2M8K2.t5152 = [0, 0, 159512784488, 445855179878, 279186477219, 20623101667, 0, 0] := by
  decide +kernel

theorem rows5153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5153 = true := by
  decide +kernel

theorem tot5153 : totK PD2M8K2 D2M8K2.t5153 = [0, 0, 91625694353, 354118631106, 357161915639, 66763342734, 1096505104, 0] := by
  decide +kernel

theorem rows5154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5154 = true := by
  decide +kernel

theorem tot5154 : totK PD2M8K2 D2M8K2.t5154 = [0, 0, 0, 315174045318, 520606328594, 78029531309, 0, 0] := by
  decide +kernel

theorem rows5155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5155 = true := by
  decide +kernel

theorem tot5155 : totK PD2M8K2 D2M8K2.t5155 = [0, 0, 153051350169, 393328655297, 282178736982, 78433370701, 3884009855, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
