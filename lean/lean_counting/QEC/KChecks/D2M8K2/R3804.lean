import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15216 = true := by
  decide +kernel

theorem tot15216 : totK PD2M8K2 D2M8K2.t15216 = [0, 0, 184739628904, 463276699682, 246672699122, 18764965837, 0, 0] := by
  decide +kernel

theorem rows15217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15217 = true := by
  decide +kernel

theorem tot15217 : totK PD2M8K2 D2M8K2.t15217 = [0, 0, 179659210869, 476546106819, 245477873357, 15790928673, 0, 0] := by
  decide +kernel

theorem rows15218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15218 = true := by
  decide +kernel

theorem tot15218 : totK PD2M8K2 D2M8K2.t15218 = [0, 0, 154305128355, 459630032271, 260840521213, 14164725606, 0, 0] := by
  decide +kernel

theorem rows15219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15219 = true := by
  decide +kernel

theorem tot15219 : totK PD2M8K2 D2M8K2.t15219 = [0, 0, 0, 253231724873, 496161187490, 114529880917, 2125526286, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
