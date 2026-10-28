import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11856 = true := by
  decide +kernel

theorem tot11856 : totK PD2M8K2 D2M8K2.t11856 = [0, 160500127258, 456801482031, 267038862927, 19728255962, 0, 0, 0] := by
  decide +kernel

theorem rows11857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11857 = true := by
  decide +kernel

theorem tot11857 : totK PD2M8K2 D2M8K2.t11857 = [0, 0, 243433928623, 511002629317, 136033626654, 2309606161, 0, 0] := by
  decide +kernel

theorem rows11858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11858 = true := by
  decide +kernel

theorem tot11858 : totK PD2M8K2 D2M8K2.t11858 = [0, 84506102996, 352429925339, 357071392582, 90625996235, 7274065870, 0, 0] := by
  decide +kernel

theorem rows11859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11859 = true := by
  decide +kernel

theorem tot11859 : totK PD2M8K2 D2M8K2.t11859 = [0, 176886532114, 453104272408, 264743977085, 27214288998, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
