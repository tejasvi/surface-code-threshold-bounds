import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2896 = true := by
  decide +kernel

theorem tot2896 : totK PD2M8K2 D2M8K2.t2896 = [0, 155621559350, 444290849583, 278003808980, 19422061650, 0, 0, 0] := by
  decide +kernel

theorem rows2897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2897 = true := by
  decide +kernel

theorem tot2897 : totK PD2M8K2 D2M8K2.t2897 = [94892842607, 315002117822, 324155242278, 148644169672, 13554132542, 0, 0, 0] := by
  decide +kernel

theorem rows2898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2898 = true := by
  decide +kernel

theorem tot2898 : totK PD2M8K2 D2M8K2.t2898 = [193421325370, 455780661198, 225976123802, 17115888737, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2899 = true := by
  decide +kernel

theorem tot2899 : totK PD2M8K2 D2M8K2.t2899 = [88672862763, 361594631930, 349730631906, 71152137058, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
