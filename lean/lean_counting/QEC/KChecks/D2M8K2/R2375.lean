import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9500 = true := by
  decide +kernel

theorem tot9500 : totK PD2M8K2 D2M8K2.t9500 = [0, 181662183390, 469617257628, 250909499236, 23114551210, 0, 0, 0] := by
  decide +kernel

theorem rows9501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9501 = true := by
  decide +kernel

theorem tot9501 : totK PD2M8K2 D2M8K2.t9501 = [0, 166927552458, 465691399783, 256248434845, 13557312044, 0, 0, 0] := by
  decide +kernel

theorem rows9502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9502 = true := by
  decide +kernel

theorem tot9502 : totK PD2M8K2 D2M8K2.t9502 = [0, 0, 280922087873, 480627066302, 129293545035, 4031931762, 0, 0] := by
  decide +kernel

theorem rows9503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9503 = true := by
  decide +kernel

theorem tot9503 : totK PD2M8K2 D2M8K2.t9503 = [0, 89442567638, 335464971511, 389064721162, 94883188176, 1186940923, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
