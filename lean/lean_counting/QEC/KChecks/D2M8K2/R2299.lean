import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9196 = true := by
  decide +kernel

theorem tot9196 : totK PD2M8K2 D2M8K2.t9196 = [133007663386, 352132540972, 313622134246, 88120091742, 3575904516, 0, 0, 0] := by
  decide +kernel

theorem rows9197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9197 = true := by
  decide +kernel

theorem tot9197 : totK PD2M8K2 D2M8K2.t9197 = [161555937130, 437115915723, 279012814100, 30498142501, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9198 = true := by
  decide +kernel

theorem tot9198 : totK PD2M8K2 D2M8K2.t9198 = [124192078066, 438495959658, 304685753809, 24721318460, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9199 = true := by
  decide +kernel

theorem tot9199 : totK PD2M8K2 D2M8K2.t9199 = [0, 295122503909, 512585327324, 100559127369, 1096156699, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
