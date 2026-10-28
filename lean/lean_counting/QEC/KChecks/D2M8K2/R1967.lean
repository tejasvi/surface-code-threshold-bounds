import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7868 = true := by
  decide +kernel

theorem tot7868 : totK PD2M8K2 D2M8K2.t7868 = [0, 0, 18921877044, 306754573658, 443305993197, 83888814731, 1206465782, 0] := by
  decide +kernel

theorem rows7869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7869 = true := by
  decide +kernel

theorem tot7869 : totK PD2M8K2 D2M8K2.t7869 = [0, 0, 92812290212, 407040902433, 354934087033, 34819058541, 0, 0] := by
  decide +kernel

theorem rows7870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7870 = true := by
  decide +kernel

theorem tot7870 : totK PD2M8K2 D2M8K2.t7870 = [0, 0, 185985881239, 469123110418, 242031119928, 15150283323, 0, 0] := by
  decide +kernel

theorem rows7871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7871 = true := by
  decide +kernel

theorem tot7871 : totK PD2M8K2 D2M8K2.t7871 = [0, 0, 202319258987, 485916705893, 208785744921, 11681530597, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
