import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7196 = true := by
  decide +kernel

theorem tot7196 : totK PD2M8K2 D2M8K2.t7196 = [0, 0, 198330297140, 466045688540, 197997457832, 7984731767, 0, 0] := by
  decide +kernel

theorem rows7197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7197 = true := by
  decide +kernel

theorem tot7197 : totK PD2M8K2 D2M8K2.t7197 = [0, 0, 107128985356, 423160748904, 325180736056, 29655915937, 0, 0] := by
  decide +kernel

theorem rows7198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7198 = true := by
  decide +kernel

theorem tot7198 : totK PD2M8K2 D2M8K2.t7198 = [0, 0, 0, 290832312107, 488509681741, 79370357476, 1310285577, 0] := by
  decide +kernel

theorem rows7199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7199 = true := by
  decide +kernel

theorem tot7199 : totK PD2M8K2 D2M8K2.t7199 = [0, 0, 173716571837, 440370733056, 281082309987, 33575737335, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
