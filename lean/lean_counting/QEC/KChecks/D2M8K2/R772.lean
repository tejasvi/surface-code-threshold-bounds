import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3088 = true := by
  decide +kernel

theorem tot3088 : totK PD2M8K2 D2M8K2.t3088 = [0, 180411496856, 446696483004, 248450359896, 18098379758, 0, 0, 0] := by
  decide +kernel

theorem rows3089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3089 = true := by
  decide +kernel

theorem tot3089 : totK PD2M8K2 D2M8K2.t3089 = [0, 72194400375, 341802084886, 406195209526, 85171189873, 1164319620, 0, 0] := by
  decide +kernel

theorem rows3090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3090 = true := by
  decide +kernel

theorem tot3090 : totK PD2M8K2 D2M8K2.t3090 = [0, 0, 257649249511, 485270373797, 143056936060, 8419352411, 0, 0] := by
  decide +kernel

theorem rows3091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3091 = true := by
  decide +kernel

theorem tot3091 : totK PD2M8K2 D2M8K2.t3091 = [0, 165657465514, 436172549038, 286873903608, 33422260914, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
