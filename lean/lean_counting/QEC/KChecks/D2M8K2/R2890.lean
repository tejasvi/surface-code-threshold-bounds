import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11560 = true := by
  decide +kernel

theorem tot11560 : totK PD2M8K2 D2M8K2.t11560 = [171611975712, 458805938444, 243616261325, 13795945806, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11561 = true := by
  decide +kernel

theorem tot11561 : totK PD2M8K2 D2M8K2.t11561 = [0, 281176234985, 503820401103, 109781075009, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows11562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11562 = true := by
  decide +kernel

theorem tot11562 : totK PD2M8K2 D2M8K2.t11562 = [87704378323, 386595461517, 383970876730, 44541733020, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11563 = true := by
  decide +kernel

theorem tot11563 : totK PD2M8K2 D2M8K2.t11563 = [164737772804, 447362928340, 267070719341, 26927543067, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
