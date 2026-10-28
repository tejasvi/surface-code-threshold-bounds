import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7544 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7544 = true := by
  decide +kernel

theorem tot7544 : totK PA10K2 A10K2.t7544 = [0, 0, 239541746934, 1125725124408, 1941016243764, 1171837841807, 196354414767, 6034215561, 0, 0] := by
  decide +kernel

theorem rows7545 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7545 = true := by
  decide +kernel

theorem tot7545 : totK PA10K2 A10K2.t7545 = [0, 0, 579671886207, 1911061939236, 1755315917041, 465226434402, 31806683705, 0, 0, 0] := by
  decide +kernel

theorem rows7546 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7546 = true := by
  decide +kernel

theorem tot7546 : totK PA10K2 A10K2.t7546 = [0, 0, 0, 950976111987, 2375715376497, 1175257161174, 106096018005, 0, 0, 0] := by
  decide +kernel

theorem rows7547 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7547 = true := by
  decide +kernel

theorem tot7547 : totK PA10K2 A10K2.t7547 = [0, 0, 0, 510330955464, 1975501627973, 1831391529870, 372971018301, 11740475125, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
