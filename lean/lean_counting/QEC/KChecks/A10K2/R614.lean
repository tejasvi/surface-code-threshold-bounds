import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2456 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2456 = true := by
  decide +kernel

theorem tot2456 : totK PA10K2 A10K2.t2456 = [0, 438284880787, 1655705567168, 1934829268275, 581114038045, 50267370225, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2457 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2457 = true := by
  decide +kernel

theorem tot2457 : totK PA10K2 A10K2.t2457 = [0, 166299333163, 1384702395956, 2228236985006, 810116271558, 58503570348, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2458 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2458 = true := by
  decide +kernel

theorem tot2458 : totK PA10K2 A10K2.t2458 = [0, 316825215404, 1214806949370, 1808464537397, 1105634211411, 227545341017, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows2459 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2459 = true := by
  decide +kernel

theorem tot2459 : totK PA10K2 A10K2.t2459 = [0, 521358057488, 1893470039731, 1926124105827, 461365104335, 11647900320, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
