import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15316 = true := by
  decide +kernel

theorem tot15316 : totK PD2M8K2 D2M8K2.t15316 = [0, 0, 84969655104, 274480328264, 369343446202, 154690447303, 8173611642, 0] := by
  decide +kernel

theorem rows15317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15317 = true := by
  decide +kernel

theorem tot15317 : totK PD2M8K2 D2M8K2.t15317 = [0, 0, 172039666610, 454558360940, 269062306653, 24166510011, 0, 0] := by
  decide +kernel

theorem rows15318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15318 = true := by
  decide +kernel

theorem tot15318 : totK PD2M8K2 D2M8K2.t15318 = [0, 0, 155100548217, 450385808922, 277148942119, 21718976722, 0, 0] := by
  decide +kernel

theorem rows15319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15319 = true := by
  decide +kernel

theorem tot15319 : totK PD2M8K2 D2M8K2.t15319 = [0, 0, 0, 228917614989, 507841382579, 144255095053, 5138457373, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
