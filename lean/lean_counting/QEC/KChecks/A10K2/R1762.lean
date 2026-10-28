import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7048 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7048 = true := by
  decide +kernel

theorem tot7048 : totK PA10K2 A10K2.t7048 = [0, 0, 309157067044, 1102569097867, 1563956555554, 1316101632585, 521827591986, 48886019071, 0, 0] := by
  decide +kernel

theorem rows7049 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7049 = true := by
  decide +kernel

theorem tot7049 : totK PA10K2 A10K2.t7049 = [0, 0, 496223740363, 1845935660622, 1954997179827, 571235057999, 24118925455, 0, 0, 0] := by
  decide +kernel

theorem rows7050 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7050 = true := by
  decide +kernel

theorem tot7050 : totK PA10K2 A10K2.t7050 = [0, 0, 0, 551036292679, 1966978156187, 1756219253250, 378342907837, 12477124820, 0, 0] := by
  decide +kernel

theorem rows7051 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7051 = true := by
  decide +kernel

theorem tot7051 : totK PA10K2 A10K2.t7051 = [0, 0, 368328999156, 1478708590021, 1967212918693, 936807944937, 104673476193, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
