import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3312 = true := by
  decide +kernel

theorem tot3312 : totK PD2M8K2 D2M8K2.t3312 = [0, 0, 331649455263, 519193171210, 74939808324, 0, 0, 0] := by
  decide +kernel

theorem rows3313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3313 = true := by
  decide +kernel

theorem tot3313 : totK PD2M8K2 D2M8K2.t3313 = [0, 157181858693, 379427787975, 273520044187, 90485100888, 3880716147, 0, 0] := by
  decide +kernel

theorem rows3314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3314 = true := by
  decide +kernel

theorem tot3314 : totK PD2M8K2 D2M8K2.t3314 = [0, 167814298848, 455037333683, 270864589085, 19228989693, 0, 0, 0] := by
  decide +kernel

theorem rows3315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3315 = true := by
  decide +kernel

theorem tot3315 : totK PD2M8K2 D2M8K2.t3315 = [0, 92353366773, 351842380329, 368073245569, 79134354242, 1231730743, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
