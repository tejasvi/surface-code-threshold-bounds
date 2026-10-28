import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t600 = true := by
  decide +kernel

theorem tot600 : totK PD2M8K2 D2M8K2.t600 = [177574188988, 465363391900, 235434206695, 17034666133, 0, 0, 0, 0] := by
  decide +kernel

theorem rows601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t601 = true := by
  decide +kernel

theorem tot601 : totK PD2M8K2 D2M8K2.t601 = [0, 279203161757, 507566397512, 100187539713, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t602 = true := by
  decide +kernel

theorem tot602 : totK PD2M8K2 D2M8K2.t602 = [87415767316, 333560466897, 371215466832, 102077018655, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t603 = true := by
  decide +kernel

theorem tot603 : totK PD2M8K2 D2M8K2.t603 = [176231221276, 445288943453, 255007225783, 26935985863, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
