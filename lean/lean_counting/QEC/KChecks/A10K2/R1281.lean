import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5124 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5124 = true := by
  decide +kernel

theorem tot5124 : totK PA10K2 A10K2.t5124 = [0, 325104351284, 1563901013529, 2055944362168, 764653325973, 62003616945, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5125 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5125 = true := by
  decide +kernel

theorem tot5125 : totK PA10K2 A10K2.t5125 = [0, 0, 454019149417, 1814833784394, 1905866022109, 501550559756, 31768748853, 0, 0, 0] := by
  decide +kernel

theorem rows5126 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5126 = true := by
  decide +kernel

theorem tot5126 : totK PA10K2 A10K2.t5126 = [0, 486200565638, 1698618075752, 1828022228620, 699080594116, 74847964626, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5127 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5127 = true := by
  decide +kernel

theorem tot5127 : totK PA10K2 A10K2.t5127 = [0, 298064684126, 1523048505265, 2140255019793, 768820315680, 53383554103, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
