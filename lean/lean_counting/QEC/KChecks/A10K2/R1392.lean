import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5568 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5568 = true := by
  decide +kernel

theorem tot5568 : totK PA10K2 A10K2.t5568 = [0, 455179774352, 1678658648098, 1877616100768, 636206733637, 52217965572, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5569 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5569 = true := by
  decide +kernel

theorem tot5569 : totK PA10K2 A10K2.t5569 = [0, 0, 893821895089, 2354501066600, 1304480899878, 127803501213, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5570 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5570 = true := by
  decide +kernel

theorem tot5570 : totK PA10K2 A10K2.t5570 = [0, 484426815356, 1626739334405, 1792922134362, 843293781176, 173145139255, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows5571 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5571 = true := by
  decide +kernel

theorem tot5571 : totK PA10K2 A10K2.t5571 = [0, 141362337536, 972014863382, 2040071529302, 1522073525368, 274018804675, 6853348008, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
