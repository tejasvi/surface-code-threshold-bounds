import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11052 = true := by
  decide +kernel

theorem tot11052 : totK PD2M8K2 D2M8K2.t11052 = [177147189031, 437434485692, 266228764939, 28787699928, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11053 = true := by
  decide +kernel

theorem tot11053 : totK PD2M8K2 D2M8K2.t11053 = [100362271081, 404688602309, 337079309627, 41869551668, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11054 = true := by
  decide +kernel

theorem tot11054 : totK PD2M8K2 D2M8K2.t11054 = [0, 223798350808, 485791270821, 172890423704, 8423393484, 0, 0, 0] := by
  decide +kernel

theorem rows11055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11055 = true := by
  decide +kernel

theorem tot11055 : totK PD2M8K2 D2M8K2.t11055 = [104502498990, 347209218710, 337260775741, 87898809802, 3462014130, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
