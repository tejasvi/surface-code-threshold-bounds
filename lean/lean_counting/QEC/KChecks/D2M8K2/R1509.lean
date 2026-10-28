import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6036 = true := by
  decide +kernel

theorem tot6036 : totK PD2M8K2 D2M8K2.t6036 = [0, 0, 228967185152, 484677854628, 176365916763, 9649412842, 0, 0] := by
  decide +kernel

theorem rows6037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6037 = true := by
  decide +kernel

theorem tot6037 : totK PD2M8K2 D2M8K2.t6037 = [0, 96077652455, 327445294023, 356097149298, 95927265341, 3546687146, 0, 0] := by
  decide +kernel

theorem rows6038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6038 = true := by
  decide +kernel

theorem tot6038 : totK PD2M8K2 D2M8K2.t6038 = [0, 180635736514, 444830914384, 254251614598, 29189528148, 0, 0, 0] := by
  decide +kernel

theorem rows6039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6039 = true := by
  decide +kernel

theorem tot6039 : totK PD2M8K2 D2M8K2.t6039 = [0, 123361854911, 436643787239, 304969997794, 24179811569, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
