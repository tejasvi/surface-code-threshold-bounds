import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t168 = true := by
  decide +kernel

theorem tot168 : totK PD2M8K2 D2M8K2.t168 = [0, 125278809470, 432199938876, 309684762688, 23734783229, 0, 0, 0] := by
  decide +kernel

theorem rows169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t169 = true := by
  decide +kernel

theorem tot169 : totK PD2M8K2 D2M8K2.t169 = [0, 0, 236729087962, 474689240745, 140724727404, 4931404646, 0, 0] := by
  decide +kernel

theorem rows170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t170 = true := by
  decide +kernel

theorem tot170 : totK PD2M8K2 D2M8K2.t170 = [0, 171507680179, 449534483055, 260103832771, 29978516145, 0, 0, 0] := by
  decide +kernel

theorem rows171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t171 = true := by
  decide +kernel

theorem tot171 : totK PD2M8K2 D2M8K2.t171 = [0, 174760730628, 451043587342, 260500640363, 18438957999, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
