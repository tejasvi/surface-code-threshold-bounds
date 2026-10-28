import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7524 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7524 = true := by
  decide +kernel

theorem tot7524 : totK PA10K2 A10K2.t7524 = [0, 514073912822, 1786310139937, 1804268316392, 603630666820, 61755549055, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7525 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7525 = true := by
  decide +kernel

theorem tot7525 : totK PA10K2 A10K2.t7525 = [0, 306750524226, 1481574121064, 2109651940002, 786598811188, 53385992088, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7526 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7526 = true := by
  decide +kernel

theorem tot7526 : totK PA10K2 A10K2.t7526 = [0, 0, 723726636381, 2133401482891, 1551506933788, 270631587530, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows7527 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7527 = true := by
  decide +kernel

theorem tot7527 : totK PA10K2 A10K2.t7527 = [0, 0, 463773659899, 1812523276432, 1967135635076, 498911265639, 31987876949, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
