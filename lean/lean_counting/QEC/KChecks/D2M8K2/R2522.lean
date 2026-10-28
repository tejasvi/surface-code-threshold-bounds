import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10088 = true := by
  decide +kernel

theorem tot10088 : totK PD2M8K2 D2M8K2.t10088 = [0, 97159392467, 314064978290, 328115342900, 152860584108, 13552619715, 0, 0] := by
  decide +kernel

theorem rows10089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10089 = true := by
  decide +kernel

theorem tot10089 : totK PD2M8K2 D2M8K2.t10089 = [0, 193081481212, 481035127744, 219884692948, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows10090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10090 = true := by
  decide +kernel

theorem tot10090 : totK PD2M8K2 D2M8K2.t10090 = [0, 51412906490, 320463648248, 432715110456, 90257443021, 1369150432, 0, 0] := by
  decide +kernel

theorem rows10091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10091 = true := by
  decide +kernel

theorem tot10091 : totK PD2M8K2 D2M8K2.t10091 = [0, 93574619190, 388464232349, 397261940926, 49798896370, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
