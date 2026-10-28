import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10888 = true := by
  decide +kernel

theorem tot10888 : totK PD2M8K2 D2M8K2.t10888 = [0, 0, 146753975262, 443487005937, 273678171959, 18602682617, 0, 0] := by
  decide +kernel

theorem rows10889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10889 = true := by
  decide +kernel

theorem tot10889 : totK PD2M8K2 D2M8K2.t10889 = [0, 0, 0, 289446119515, 477953640275, 84286303403, 1239866073, 0] := by
  decide +kernel

theorem rows10890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10890 = true := by
  decide +kernel

theorem tot10890 : totK PD2M8K2 D2M8K2.t10890 = [0, 0, 161410853672, 442255411680, 291611939874, 31118957687, 0, 0] := by
  decide +kernel

theorem rows10891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10891 = true := by
  decide +kernel

theorem tot10891 : totK PD2M8K2 D2M8K2.t10891 = [0, 0, 191268717805, 481767644695, 225651714251, 12454366108, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
