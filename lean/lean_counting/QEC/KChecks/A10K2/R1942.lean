import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7768 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7768 = true := by
  decide +kernel

theorem tot7768 : totK PA10K2 A10K2.t7768 = [0, 465644095695, 1793876135056, 2113922037892, 713285501945, 39260890035, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7769 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7769 = true := by
  decide +kernel

theorem tot7769 : totK PA10K2 A10K2.t7769 = [0, 0, 593181773731, 2029261505962, 2000791430905, 490205189222, 13803657628, 0, 0, 0] := by
  decide +kernel

theorem rows7770 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7770 = true := by
  decide +kernel

theorem tot7770 : totK PA10K2 A10K2.t7770 = [0, 0, 525189321057, 1874029981798, 1921342716425, 594963428671, 49111353342, 0, 0, 0] := by
  decide +kernel

theorem rows7771 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7771 = true := by
  decide +kernel

theorem tot7771 : totK PA10K2 A10K2.t7771 = [0, 0, 526962436300, 1814974271185, 1813865489312, 480033304109, 31222411477, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
