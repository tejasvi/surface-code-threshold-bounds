import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3608 = true := by
  decide +kernel

theorem tot3608 : totK PD2M8K2 D2M8K2.t3608 = [0, 65614097781, 283885053678, 401929916058, 122755722298, 5874298072, 0, 0] := by
  decide +kernel

theorem rows3609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3609 = true := by
  decide +kernel

theorem tot3609 : totK PD2M8K2 D2M8K2.t3609 = [0, 181720178412, 469969551466, 254847950871, 23172067211, 0, 0, 0] := by
  decide +kernel

theorem rows3610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3610 = true := by
  decide +kernel

theorem tot3610 : totK PD2M8K2 D2M8K2.t3610 = [0, 166518054515, 461604671189, 256959841110, 16240274002, 0, 0, 0] := by
  decide +kernel

theorem rows3611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3611 = true := by
  decide +kernel

theorem tot3611 : totK PD2M8K2 D2M8K2.t3611 = [0, 0, 256835146338, 484802246600, 147592503928, 8464368736, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
