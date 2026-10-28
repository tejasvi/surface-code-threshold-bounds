import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15248 = true := by
  decide +kernel

theorem tot15248 : totK PD2M8K2 D2M8K2.t15248 = [0, 0, 0, 208803859899, 496041167904, 180315413084, 5528812079, 0] := by
  decide +kernel

theorem rows15249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15249 = true := by
  decide +kernel

theorem tot15249 : totK PD2M8K2 D2M8K2.t15249 = [0, 0, 0, 202221738192, 489119665871, 170152062597, 5293351784, 0] := by
  decide +kernel

theorem rows15250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15250 = true := by
  decide +kernel

theorem tot15250 : totK PD2M8K2 D2M8K2.t15250 = [0, 0, 0, 0, 294446205849, 460379618033, 94040601224, 1369150432] := by
  decide +kernel

theorem rows15251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15251 = true := by
  decide +kernel

theorem tot15251 : totK PD2M8K2 D2M8K2.t15251 = [0, 0, 0, 86403723232, 417789535311, 324377305911, 26125122931, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
