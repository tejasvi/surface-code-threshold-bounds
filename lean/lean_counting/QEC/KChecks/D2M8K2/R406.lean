import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1624 = true := by
  decide +kernel

theorem tot1624 : totK PD2M8K2 D2M8K2.t1624 = [0, 19228354030, 330180723371, 460063480569, 84748440356, 1096505104, 0, 0] := by
  decide +kernel

theorem rows1625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1625 = true := by
  decide +kernel

theorem tot1625 : totK PD2M8K2 D2M8K2.t1625 = [0, 0, 269252588580, 505873830621, 127709020391, 3884009855, 0, 0] := by
  decide +kernel

theorem rows1626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1626 = true := by
  decide +kernel

theorem tot1626 : totK PD2M8K2 D2M8K2.t1626 = [0, 0, 200587811949, 474188356727, 194529399358, 9740140984, 0, 0] := by
  decide +kernel

theorem rows1627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1627 = true := by
  decide +kernel

theorem tot1627 : totK PD2M8K2 D2M8K2.t1627 = [0, 0, 175431248431, 478471891723, 212919386559, 12421902774, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
