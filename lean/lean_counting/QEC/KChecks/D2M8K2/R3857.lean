import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15428 = true := by
  decide +kernel

theorem tot15428 : totK PD2M8K2 D2M8K2.t15428 = [0, 0, 203012760955, 484213986696, 214990680515, 10855399327, 0, 0] := by
  decide +kernel

theorem rows15429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15429 = true := by
  decide +kernel

theorem tot15429 : totK PD2M8K2 D2M8K2.t15429 = [0, 0, 193393524780, 471156174249, 222318678190, 12876692821, 0, 0] := by
  decide +kernel

theorem rows15430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15430 = true := by
  decide +kernel

theorem tot15430 : totK PD2M8K2 D2M8K2.t15430 = [0, 0, 164293745551, 445980434381, 280497194468, 27214788375, 0, 0] := by
  decide +kernel

theorem rows15431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15431 = true := by
  decide +kernel

theorem tot15431 : totK PD2M8K2 D2M8K2.t15431 = [0, 0, 138165766869, 438290457489, 285066002315, 22327055745, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
