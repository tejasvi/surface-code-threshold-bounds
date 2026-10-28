import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1140 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1140 = true := by
  decide +kernel

theorem tot1140 : totK PA10K2 A10K2.t1140 = [0, 0, 0, 328627686157, 1543692303403, 2161778338028, 850585754523, 62012163500, 0, 0] := by
  decide +kernel

theorem rows1141 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1141 = true := by
  decide +kernel

theorem tot1141 : totK PA10K2 A10K2.t1141 = [0, 0, 0, 0, 547659747105, 1963451101351, 1891499381757, 397959185771, 12132367858, 0] := by
  decide +kernel

theorem rows1142 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1142 = true := by
  decide +kernel

theorem tot1142 : totK PA10K2 A10K2.t1142 = [0, 321107158991, 1064688976361, 1082600829786, 351332326954, 530223721936, 1032239334456, 501217979401, 48886019071, 0] := by
  decide +kernel

theorem rows1143 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1143 = true := by
  decide +kernel

theorem tot1143 : totK PA10K2 A10K2.t1143 = [0, 552923900324, 1950341655161, 1920938287676, 451744455058, 18560348465, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
