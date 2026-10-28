import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3956 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3956 = true := by
  decide +kernel

theorem tot3956 : totK PA10K2 A10K2.t3956 = [0, 0, 479419663260, 1836936119628, 2018218723896, 634474500616, 49180423016, 0, 0, 0] := by
  decide +kernel

theorem rows3957 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3957 = true := by
  decide +kernel

theorem tot3957 : totK PA10K2 A10K2.t3957 = [0, 0, 302916131585, 1467083411674, 2165110901138, 948919532388, 77349677273, 0, 0, 0] := by
  decide +kernel

theorem rows3958 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3958 = true := by
  decide +kernel

theorem tot3958 : totK PA10K2 A10K2.t3958 = [0, 0, 308525764274, 1268748828182, 1954675229140, 1252584440759, 217713650884, 6904928264, 0, 0] := by
  decide +kernel

theorem rows3959 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3959 = true := by
  decide +kernel

theorem tot3959 : totK PA10K2 A10K2.t3959 = [0, 0, 495583288092, 1820950037609, 1975524280068, 613065744908, 37937958489, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
