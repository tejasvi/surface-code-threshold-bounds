import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7152 = true := by
  decide +kernel

theorem tot7152 : totK PD2M8K2 D2M8K2.t7152 = [0, 156854759878, 461839551330, 266055982938, 16264020352, 0, 0, 0] := by
  decide +kernel

theorem rows7153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7153 = true := by
  decide +kernel

theorem tot7153 : totK PD2M8K2 D2M8K2.t7153 = [0, 0, 261556231130, 509048739366, 117925357024, 1164319620, 0, 0] := by
  decide +kernel

theorem rows7154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7154 = true := by
  decide +kernel

theorem tot7154 : totK PD2M8K2 D2M8K2.t7154 = [0, 57479709716, 234354027416, 401426448603, 173789767047, 11885407614, 0, 0] := by
  decide +kernel

theorem rows7155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7155 = true := by
  decide +kernel

theorem tot7155 : totK PD2M8K2 D2M8K2.t7155 = [0, 182274302322, 466009675982, 239247350242, 13918229285, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
