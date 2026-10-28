import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t816 = true := by
  decide +kernel

theorem tot816 : totK PD2M8K2 D2M8K2.t816 = [0, 88945508586, 349844893215, 384996024225, 78510265739, 1198073392, 0, 0] := by
  decide +kernel

theorem rows817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t817 = true := by
  decide +kernel

theorem tot817 : totK PD2M8K2 D2M8K2.t817 = [0, 0, 247842338982, 490294044150, 156456300621, 8470662040, 0, 0] := by
  decide +kernel

theorem rows818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t818 = true := by
  decide +kernel

theorem tot818 : totK PD2M8K2 D2M8K2.t818 = [0, 121044791806, 355825330126, 306454263270, 85356030356, 3581949829, 0, 0] := by
  decide +kernel

theorem rows819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t819 = true := by
  decide +kernel

theorem tot819 : totK PD2M8K2 D2M8K2.t819 = [0, 187199252044, 445126487598, 237567094315, 24607577938, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
