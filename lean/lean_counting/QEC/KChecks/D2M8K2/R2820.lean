import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11280 = true := by
  decide +kernel

theorem tot11280 : totK PD2M8K2 D2M8K2.t11280 = [0, 182638964787, 484175088427, 243574778345, 15955732371, 0, 0, 0] := by
  decide +kernel

theorem rows11281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11281 = true := by
  decide +kernel

theorem tot11281 : totK PD2M8K2 D2M8K2.t11281 = [0, 173119182785, 461576189472, 235831596817, 14874568699, 0, 0, 0] := by
  decide +kernel

theorem rows11282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11282 = true := by
  decide +kernel

theorem tot11282 : totK PD2M8K2 D2M8K2.t11282 = [0, 0, 279437837755, 486728060431, 108955627522, 1162935789, 0, 0] := by
  decide +kernel

theorem rows11283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11283 = true := by
  decide +kernel

theorem tot11283 : totK PD2M8K2 D2M8K2.t11283 = [0, 48964430500, 233729788555, 386295582759, 166989121846, 11853261585, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
