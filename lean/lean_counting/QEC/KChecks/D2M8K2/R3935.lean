import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15740 = true := by
  decide +kernel

theorem tot15740 : totK PD2M8K2 D2M8K2.t15740 = [0, 0, 0, 179650071948, 461572477842, 248335682053, 20681061753, 0] := by
  decide +kernel

theorem rows15741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15741 = true := by
  decide +kernel

theorem tot15741 : totK PD2M8K2 D2M8K2.t15741 = [0, 0, 0, 251929740011, 473946244230, 180012353118, 7288565651, 0] := by
  decide +kernel

theorem rows15742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15742 = true := by
  decide +kernel

theorem tot15742 : totK PD2M8K2 D2M8K2.t15742 = [0, 0, 0, 209223861823, 483542267547, 198940437754, 11570316886, 0] := by
  decide +kernel

theorem rows15743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15743 = true := by
  decide +kernel

theorem tot15743 : totK PD2M8K2 D2M8K2.t15743 = [0, 0, 0, 188071086058, 473904882874, 208845984865, 12183533023, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
