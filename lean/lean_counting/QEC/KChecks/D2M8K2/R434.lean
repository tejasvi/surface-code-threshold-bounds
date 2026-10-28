import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1736 = true := by
  decide +kernel

theorem tot1736 : totK PD2M8K2 D2M8K2.t1736 = [0, 0, 178725158610, 465650020686, 237586050935, 16959211542, 0, 0] := by
  decide +kernel

theorem rows1737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1737 = true := by
  decide +kernel

theorem tot1737 : totK PD2M8K2 D2M8K2.t1737 = [0, 0, 0, 299751887965, 486190269577, 82475945320, 1096505104, 0] := by
  decide +kernel

theorem rows1738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1738 = true := by
  decide +kernel

theorem tot1738 : totK PD2M8K2 D2M8K2.t1738 = [0, 0, 112447018091, 350031020531, 324723056550, 79123234546, 3821179711, 0] := by
  decide +kernel

theorem rows1739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1739 = true := by
  decide +kernel

theorem tot1739 : totK PD2M8K2 D2M8K2.t1739 = [0, 0, 208365169811, 482033816792, 210677351104, 8586147391, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
