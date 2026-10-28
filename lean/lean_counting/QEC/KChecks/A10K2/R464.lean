import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1856 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1856 = true := by
  decide +kernel

theorem tot1856 : totK PA10K2 A10K2.t1856 = [0, 0, 574864650674, 1876212845337, 1893203426759, 602478477487, 49180423016, 0, 0, 0] := by
  decide +kernel

theorem rows1857 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1857 = true := by
  decide +kernel

theorem tot1857 : totK PA10K2 A10K2.t1857 = [0, 0, 552828098849, 1926845139063, 1918501843006, 519089558597, 31080743953, 0, 0, 0] := by
  decide +kernel

theorem rows1858 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1858 = true := by
  decide +kernel

theorem tot1858 : totK PA10K2 A10K2.t1858 = [0, 0, 0, 806340477447, 2280397597817, 1585720457925, 268480765259, 6904928264, 0, 0] := by
  decide +kernel

theorem rows1859 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1859 = true := by
  decide +kernel

theorem tot1859 : totK PA10K2 A10K2.t1859 = [0, 0, 335575915953, 1435034814437, 2123182781594, 965525428132, 81356666222, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
