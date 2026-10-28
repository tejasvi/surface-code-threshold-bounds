import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10732 = true := by
  decide +kernel

theorem tot10732 : totK PD2M8K2 D2M8K2.t10732 = [0, 0, 37670822061, 339256594711, 431167005895, 73436929744, 1096505104, 0] := by
  decide +kernel

theorem rows10733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10733 = true := by
  decide +kernel

theorem tot10733 : totK PD2M8K2 D2M8K2.t10733 = [0, 0, 34713142644, 277498834301, 458555802056, 115373681980, 3884009855, 0] := by
  decide +kernel

theorem rows10734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10734 = true := by
  decide +kernel

theorem tot10734 : totK PD2M8K2 D2M8K2.t10734 = [0, 0, 197418460502, 468152322828, 234851790570, 19350607301, 0, 0] := by
  decide +kernel

theorem rows10735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10735 = true := by
  decide +kernel

theorem tot10735 : totK PD2M8K2 D2M8K2.t10735 = [0, 0, 107926153024, 433734367250, 335970345004, 26834294198, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
