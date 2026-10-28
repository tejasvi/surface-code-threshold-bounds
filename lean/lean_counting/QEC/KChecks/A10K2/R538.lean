import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2152 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2152 = true := by
  decide +kernel

theorem tot2152 : totK PA10K2 A10K2.t2152 = [0, 316846731414, 1211555311564, 1813716518359, 1136422018931, 228626692062, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows2153 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2153 = true := by
  decide +kernel

theorem tot2153 : totK PA10K2 A10K2.t2153 = [0, 527310909255, 1909498648598, 1942191083438, 465421964609, 12244162943, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2154 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2154 = true := by
  decide +kernel

theorem tot2154 : totK PA10K2 A10K2.t2154 = [0, 0, 698153625379, 2071987876790, 1653802747968, 384309099204, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows2155 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2155 = true := by
  decide +kernel

theorem tot2155 : totK PA10K2 A10K2.t2155 = [0, 176986670399, 981617380077, 1872861924120, 1380861260385, 227092835029, 5718040558, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
