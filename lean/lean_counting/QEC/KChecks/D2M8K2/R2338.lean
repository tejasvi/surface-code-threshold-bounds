import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9352 = true := by
  decide +kernel

theorem tot9352 : totK PD2M8K2 D2M8K2.t9352 = [0, 168120394157, 446209498477, 276967912245, 29350723805, 0, 0, 0] := by
  decide +kernel

theorem rows9353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9353 = true := by
  decide +kernel

theorem tot9353 : totK PD2M8K2 D2M8K2.t9353 = [0, 197952468995, 483642550848, 224248632379, 10140659148, 0, 0, 0] := by
  decide +kernel

theorem rows9354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9354 = true := by
  decide +kernel

theorem tot9354 : totK PD2M8K2 D2M8K2.t9354 = [0, 30291347117, 271135396736, 406322790021, 186117088039, 21400436502, 0, 0] := by
  decide +kernel

theorem rows9355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9355 = true := by
  decide +kernel

theorem tot9355 : totK PD2M8K2 D2M8K2.t9355 = [0, 0, 203701738158, 483426245304, 201501969218, 7994456143, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
