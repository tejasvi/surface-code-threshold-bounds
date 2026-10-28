import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7736 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7736 = true := by
  decide +kernel

theorem tot7736 : totK PA10K2 A10K2.t7736 = [0, 0, 538217299603, 1918926853968, 2016525443399, 589854643850, 38041561157, 0, 0, 0] := by
  decide +kernel

theorem rows7737 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7737 = true := by
  decide +kernel

theorem tot7737 : totK PA10K2 A10K2.t7737 = [0, 0, 121146523123, 1068610901134, 2242574028654, 1482379399403, 263435088860, 6585347165, 0, 0] := by
  decide +kernel

theorem rows7738 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7738 = true := by
  decide +kernel

theorem tot7738 : totK PA10K2 A10K2.t7738 = [0, 0, 0, 500351304947, 1928276685920, 2065908849473, 543553129979, 18813240752, 0, 0] := by
  decide +kernel

theorem rows7739 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7739 = true := by
  decide +kernel

theorem tot7739 : totK PA10K2 A10K2.t7739 = [0, 0, 0, 542184860159, 1808611518182, 1771298238498, 622039172226, 63792639202, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
