import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows872 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t872 = true := by
  decide +kernel

theorem tot872 : totK PA10K2 A10K2.t872 = [0, 495733772273, 1912233276312, 2058390697742, 543973045272, 18813240752, 0, 0, 0, 0] := by
  decide +kernel

theorem rows873 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t873 = true := by
  decide +kernel

theorem tot873 : totK PA10K2 A10K2.t873 = [0, 483091387081, 1745133979833, 1871551233850, 645431159483, 63792639202, 0, 0, 0, 0] := by
  decide +kernel

theorem rows874 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t874 = true := by
  decide +kernel

theorem tot874 : totK PA10K2 A10K2.t874 = [0, 296957029898, 1464533696242, 2230091474847, 916565492338, 67798867528, 0, 0, 0, 0] := by
  decide +kernel

theorem rows875 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t875 = true := by
  decide +kernel

theorem tot875 : totK PA10K2 A10K2.t875 = [0, 110277202043, 692592509111, 1757801226249, 1729712291320, 484097327546, 31082886609, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
