import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2648 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2648 = true := by
  decide +kernel

theorem tot2648 : totK PA10K2 A10K2.t2648 = [0, 304053839609, 1521982147981, 2063381030090, 726219779339, 53385992088, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2649 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2649 = true := by
  decide +kernel

theorem tot2649 : totK PA10K2 A10K2.t2649 = [0, 0, 703633006293, 2134037706914, 1537249200134, 255003358674, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows2650 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2650 = true := by
  decide +kernel

theorem tot2650 : totK PA10K2 A10K2.t2650 = [0, 0, 502087800410, 1912131891216, 1898741787576, 442999931776, 25633273041, 0, 0, 0] := by
  decide +kernel

theorem rows2651 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2651 = true := by
  decide +kernel

theorem tot2651 : totK PA10K2 A10K2.t2651 = [0, 0, 464748938522, 1749120921259, 2039755072487, 617450365503, 38831184896, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
