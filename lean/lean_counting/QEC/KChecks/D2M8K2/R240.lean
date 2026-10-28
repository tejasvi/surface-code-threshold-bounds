import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t960 = true := by
  decide +kernel

theorem tot960 : totK PD2M8K2 D2M8K2.t960 = [0, 284861342678, 510291793339, 104267852103, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t961 = true := by
  decide +kernel

theorem tot961 : totK PD2M8K2 D2M8K2.t961 = [179491426632, 436181798527, 270976468738, 33122120570, 0, 0, 0, 0] := by
  decide +kernel

theorem rows962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t962 = true := by
  decide +kernel

theorem tot962 : totK PD2M8K2 D2M8K2.t962 = [170119561386, 460786965488, 248650753158, 18339826511, 0, 0, 0, 0] := by
  decide +kernel

theorem rows963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t963 = true := by
  decide +kernel

theorem tot963 : totK PD2M8K2 D2M8K2.t963 = [36785965276, 272517748204, 394130464116, 184666916980, 21303575461, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
