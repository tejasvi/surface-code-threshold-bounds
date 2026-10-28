import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6188 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6188 = true := by
  decide +kernel

theorem tot6188 : totK PA10K2 A10K2.t6188 = [0, 295757175837, 1456686305620, 2224797735739, 1055292616401, 105912879342, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6189 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6189 = true := by
  decide +kernel

theorem tot6189 : totK PA10K2 A10K2.t6189 = [0, 0, 546166833956, 1900531056172, 1996629104114, 575528235270, 35503361870, 0, 0, 0] := by
  decide +kernel

theorem rows6190 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6190 = true := by
  decide +kernel

theorem tot6190 : totK PA10K2 A10K2.t6190 = [0, 0, 447630199909, 1785906655212, 1982910421152, 519273246874, 31222411477, 0, 0, 0] := by
  decide +kernel

theorem rows6191 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6191 = true := by
  decide +kernel

theorem tot6191 : totK PA10K2 A10K2.t6191 = [0, 0, 125260897486, 954850254414, 1941496738835, 1359465440674, 342971015804, 25239774317, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
