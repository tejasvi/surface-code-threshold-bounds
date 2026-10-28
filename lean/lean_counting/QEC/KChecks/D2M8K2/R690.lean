import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2760 = true := by
  decide +kernel

theorem tot2760 : totK PD2M8K2 D2M8K2.t2760 = [0, 189442788215, 480538719334, 218240957034, 8090591079, 0, 0, 0] := by
  decide +kernel

theorem rows2761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2761 = true := by
  decide +kernel

theorem tot2761 : totK PD2M8K2 D2M8K2.t2761 = [0, 59737629380, 336952737633, 409341793712, 82158549458, 1369150432, 0, 0] := by
  decide +kernel

theorem rows2762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2762 = true := by
  decide +kernel

theorem tot2762 : totK PD2M8K2 D2M8K2.t2762 = [0, 93610018881, 385093533361, 397395276239, 53862419503, 0, 0, 0] := by
  decide +kernel

theorem rows2763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2763 = true := by
  decide +kernel

theorem tot2763 : totK PD2M8K2 D2M8K2.t2763 = [0, 174769799367, 449243063566, 260801264857, 20811159491, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
