import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7360 = true := by
  decide +kernel

theorem tot7360 : totK PD2M8K2 D2M8K2.t7360 = [0, 78822937643, 319607744452, 381121349915, 104381736344, 3884009855, 0, 0] := by
  decide +kernel

theorem rows7361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7361 = true := by
  decide +kernel

theorem tot7361 : totK PD2M8K2 D2M8K2.t7361 = [0, 177902928000, 458440902096, 264848189965, 26369933502, 0, 0, 0] := by
  decide +kernel

theorem rows7362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7362 = true := by
  decide +kernel

theorem tot7362 : totK PD2M8K2 D2M8K2.t7362 = [0, 160390059804, 453535669995, 267501804088, 22797711407, 0, 0, 0] := by
  decide +kernel

theorem rows7363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7363 = true := by
  decide +kernel

theorem tot7363 : totK PD2M8K2 D2M8K2.t7363 = [0, 0, 247943105242, 504928510643, 141187355562, 2304167554, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
