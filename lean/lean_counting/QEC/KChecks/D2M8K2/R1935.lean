import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7740 = true := by
  decide +kernel

theorem tot7740 : totK PD2M8K2 D2M8K2.t7740 = [0, 0, 179505040356, 463601751762, 250583358432, 19698036067, 0, 0] := by
  decide +kernel

theorem rows7741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7741 = true := by
  decide +kernel

theorem tot7741 : totK PD2M8K2 D2M8K2.t7741 = [0, 0, 159947928060, 462560598271, 258491945902, 16236639292, 0, 0] := by
  decide +kernel

theorem rows7742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7742 = true := by
  decide +kernel

theorem tot7742 : totK PD2M8K2 D2M8K2.t7742 = [0, 0, 0, 278806751489, 504121999939, 107022968597, 1164319620, 0] := by
  decide +kernel

theorem rows7743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7743 = true := by
  decide +kernel

theorem tot7743 : totK PD2M8K2 D2M8K2.t7743 = [0, 0, 45589247412, 213753113700, 419938421042, 180524561061, 11885407614, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
