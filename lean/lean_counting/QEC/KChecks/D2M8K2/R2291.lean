import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9164 = true := by
  decide +kernel

theorem tot9164 : totK PD2M8K2 D2M8K2.t9164 = [159329899136, 439066434883, 276919644685, 37785119068, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9165 = true := by
  decide +kernel

theorem tot9165 : totK PD2M8K2 D2M8K2.t9165 = [170077859691, 438352184274, 255216868462, 19994244721, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9166 = true := by
  decide +kernel

theorem tot9166 : totK PD2M8K2 D2M8K2.t9166 = [91637619653, 366132528323, 366342164595, 67624402252, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows9167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9167 = true := by
  decide +kernel

theorem tot9167 : totK PD2M8K2 D2M8K2.t9167 = [0, 310517514928, 505421327534, 80038085676, 1069412848, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
