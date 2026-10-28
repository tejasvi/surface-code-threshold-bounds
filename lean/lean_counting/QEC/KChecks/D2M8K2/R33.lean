import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t132 = true := by
  decide +kernel

theorem tot132 : totK PD2M8K2 D2M8K2.t132 = [0, 173091306308, 463733731954, 239644498266, 13597322258, 0, 0, 0] := by
  decide +kernel

theorem rows133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t133 = true := by
  decide +kernel

theorem tot133 : totK PD2M8K2 D2M8K2.t133 = [0, 168893031050, 469938097041, 234740511514, 17078533784, 0, 0, 0] := by
  decide +kernel

theorem rows134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t134 = true := by
  decide +kernel

theorem tot134 : totK PD2M8K2 D2M8K2.t134 = [0, 173720322168, 450617108676, 240103526540, 18109095603, 0, 0, 0] := by
  decide +kernel

theorem rows135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t135 = true := by
  decide +kernel

theorem tot135 : totK PD2M8K2 D2M8K2.t135 = [0, 92453491279, 359089058036, 345668509248, 69099362224, 1095107716, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
