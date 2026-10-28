import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8140 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8140 = true := by
  decide +kernel

theorem tot8140 : totK PA10K2 A10K2.t8140 = [0, 0, 615230447397, 2035510287388, 1880925499677, 465214215361, 21904379589, 0, 0, 0] := by
  decide +kernel

theorem rows8141 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8141 = true := by
  decide +kernel

theorem tot8141 : totK PA10K2 A10K2.t8141 = [0, 0, 0, 675170775870, 2190265217313, 1759021780969, 305444309724, 6853348008, 0, 0] := by
  decide +kernel

theorem rows8142 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8142 = true := by
  decide +kernel

theorem tot8142 : totK PA10K2 A10K2.t8142 = [0, 0, 0, 444543774934, 1802390747085, 2158700476984, 663366692235, 24454642747, 0, 0] := by
  decide +kernel

theorem rows8143 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8143 = true := by
  decide +kernel

theorem tot8143 : totK PA10K2 A10K2.t8143 = [0, 0, 0, 560467005157, 1865792097038, 1785409581341, 507615366741, 43553281686, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
