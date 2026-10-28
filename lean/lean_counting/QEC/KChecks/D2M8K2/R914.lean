import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3656 = true := by
  decide +kernel

theorem tot3656 : totK PD2M8K2 D2M8K2.t3656 = [0, 71770560379, 354038895965, 401062823142, 80204167168, 1210106048, 0, 0] := by
  decide +kernel

theorem rows3657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3657 = true := by
  decide +kernel

theorem tot3657 : totK PD2M8K2 D2M8K2.t3657 = [0, 73275311424, 306221210934, 403710205084, 117346379793, 3724448267, 0, 0] := by
  decide +kernel

theorem rows3658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3658 = true := by
  decide +kernel

theorem tot3658 : totK PD2M8K2 D2M8K2.t3658 = [0, 183259839414, 465741051626, 209106460683, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows3659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3659 = true := by
  decide +kernel

theorem tot3659 : totK PD2M8K2 D2M8K2.t3659 = [0, 138081896298, 436775877283, 274840902179, 18971587269, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
