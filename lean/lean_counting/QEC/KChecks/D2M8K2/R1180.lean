import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4720 = true := by
  decide +kernel

theorem tot4720 : totK PD2M8K2 D2M8K2.t4720 = [0, 93305483181, 376031466979, 399503705618, 53013397475, 0, 0, 0] := by
  decide +kernel

theorem rows4721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4721 = true := by
  decide +kernel

theorem tot4721 : totK PD2M8K2 D2M8K2.t4721 = [0, 159311086397, 452923958562, 290112402682, 23535962710, 0, 0, 0] := by
  decide +kernel

theorem rows4722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4722 = true := by
  decide +kernel

theorem tot4722 : totK PD2M8K2 D2M8K2.t4722 = [0, 174351684497, 469246248788, 245015340654, 12596964668, 0, 0, 0] := by
  decide +kernel

theorem rows4723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4723 = true := by
  decide +kernel

theorem tot4723 : totK PD2M8K2 D2M8K2.t4723 = [0, 0, 181162326301, 446799117063, 258154345457, 25330507241, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
