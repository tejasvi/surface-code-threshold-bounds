import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11128 = true := by
  decide +kernel

theorem tot11128 : totK PD2M8K2 D2M8K2.t11128 = [0, 0, 192485030668, 450292606088, 202671113551, 16843409175, 0, 0] := by
  decide +kernel

theorem rows11129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11129 = true := by
  decide +kernel

theorem tot11129 : totK PD2M8K2 D2M8K2.t11129 = [0, 0, 197052807435, 485878601697, 193411344602, 9610913563, 0, 0] := by
  decide +kernel

theorem rows11130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11130 = true := by
  decide +kernel

theorem tot11130 : totK PD2M8K2 D2M8K2.t11130 = [0, 0, 193863297414, 464558116589, 196615240468, 12206147664, 0, 0] := by
  decide +kernel

theorem rows11131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11131 = true := by
  decide +kernel

theorem tot11131 : totK PD2M8K2 D2M8K2.t11131 = [0, 0, 19350145302, 302700494989, 432603270334, 101621298821, 1369150432, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
