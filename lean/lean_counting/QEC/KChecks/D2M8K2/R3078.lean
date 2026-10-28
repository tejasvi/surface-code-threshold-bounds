import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12312 = true := by
  decide +kernel

theorem tot12312 : totK PD2M8K2 D2M8K2.t12312 = [198368748028, 475338103523, 218224060988, 12534051746, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12313 = true := by
  decide +kernel

theorem tot12313 : totK PD2M8K2 D2M8K2.t12313 = [31327661012, 300858579463, 440964951740, 100120905347, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows12314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12314 = true := by
  decide +kernel

theorem tot12314 : totK PD2M8K2 D2M8K2.t12314 = [85427504293, 367784529745, 409506881924, 51393844628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12315 = true := by
  decide +kernel

theorem tot12315 : totK PD2M8K2 D2M8K2.t12315 = [161235500875, 440506127116, 282070399991, 30462929994, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
