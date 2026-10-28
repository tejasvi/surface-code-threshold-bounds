import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8048 = true := by
  decide +kernel

theorem tot8048 : totK PD2M8K2 D2M8K2.t8048 = [0, 88680480173, 412167593661, 359744786595, 41973513366, 0, 0, 0] := by
  decide +kernel

theorem rows8049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8049 = true := by
  decide +kernel

theorem tot8049 : totK PD2M8K2 D2M8K2.t8049 = [0, 0, 283010103542, 511474633780, 100012470007, 1369150432, 0, 0] := by
  decide +kernel

theorem rows8050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8050 = true := by
  decide +kernel

theorem tot8050 : totK PD2M8K2 D2M8K2.t8050 = [0, 156961448103, 452571665325, 281494778698, 28738853978, 0, 0, 0] := by
  decide +kernel

theorem rows8051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8051 = true := by
  decide +kernel

theorem tot8051 : totK PD2M8K2 D2M8K2.t8051 = [0, 187146092051, 454242338164, 228951688247, 16753589577, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
