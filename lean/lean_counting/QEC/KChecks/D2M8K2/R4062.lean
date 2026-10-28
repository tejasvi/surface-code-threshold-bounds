import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16248 = true := by
  decide +kernel

theorem tot16248 : totK PD2M8K2 D2M8K2.t16248 = [0, 0, 86448444628, 333784731498, 373038481449, 92580260195, 4030866388, 0] := by
  decide +kernel

theorem rows16249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16249 = true := by
  decide +kernel

theorem tot16249 : totK PD2M8K2 D2M8K2.t16249 = [0, 0, 183607637682, 483703735881, 202459500454, 8404381410, 0, 0] := by
  decide +kernel

theorem rows16250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16250 = true := by
  decide +kernel

theorem tot16250 : totK PD2M8K2 D2M8K2.t16250 = [0, 0, 46280444320, 339616468354, 416703219699, 56458980527, 1096505104, 0] := by
  decide +kernel

theorem rows16251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16251 = true := by
  decide +kernel

theorem tot16251 : totK PD2M8K2 D2M8K2.t16251 = [0, 0, 161314879595, 443488387903, 279418863494, 14520373548, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
