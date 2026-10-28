import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows664 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t664 = true := by
  decide +kernel

theorem tot664 : totK PA10K2 A10K2.t664 = [0, 282936105235, 1231649907449, 1950800416850, 1124988277724, 219727073494, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows665 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t665 = true := by
  decide +kernel

theorem tot665 : totK PA10K2 A10K2.t665 = [0, 217158502480, 1187425345399, 2109674423236, 1346449105933, 239890217735, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows666 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t666 = true := by
  decide +kernel

theorem tot666 : totK PA10K2 A10K2.t666 = [0, 0, 524230453363, 1869721471674, 1972785225105, 528966633263, 31559907735, 0, 0, 0] := by
  decide +kernel

theorem rows667 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t667 = true := by
  decide +kernel

theorem tot667 : totK PA10K2 A10K2.t667 = [0, 0, 394487094067, 1769814229912, 2063907339756, 555359148353, 32885668568, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
