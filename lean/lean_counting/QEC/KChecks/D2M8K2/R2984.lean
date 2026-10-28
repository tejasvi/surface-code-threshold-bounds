import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11936 = true := by
  decide +kernel

theorem tot11936 : totK PD2M8K2 D2M8K2.t11936 = [0, 273724920346, 503249274103, 114176648671, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows11937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11937 = true := by
  decide +kernel

theorem tot11937 : totK PD2M8K2 D2M8K2.t11937 = [93305483181, 387518032948, 387891279354, 49363638825, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11938 = true := by
  decide +kernel

theorem tot11938 : totK PD2M8K2 D2M8K2.t11938 = [192982854656, 462780556057, 240582828409, 18936406781, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11939 = true := by
  decide +kernel

theorem tot11939 : totK PD2M8K2 D2M8K2.t11939 = [137410187384, 442385595493, 287960660621, 31399919336, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
