import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1356 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1356 = true := by
  decide +kernel

theorem tot1356 : totK PA10K2 A10K2.t1356 = [0, 0, 220242025791, 1293005453214, 2192752425532, 1143872939981, 116644859889, 0, 0, 0] := by
  decide +kernel

theorem rows1357 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1357 = true := by
  decide +kernel

theorem tot1357 : totK PA10K2 A10K2.t1357 = [0, 0, 0, 547008320956, 1870333483075, 1777261553764, 452464612827, 30831673886, 0, 0] := by
  decide +kernel

theorem rows1358 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1358 = true := by
  decide +kernel

theorem tot1358 : totK PA10K2 A10K2.t1358 = [0, 0, 542435260935, 1738852495590, 1763776279436, 598477285284, 63336853319, 0, 0, 0] := by
  decide +kernel

theorem rows1359 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1359 = true := by
  decide +kernel

theorem tot1359 : totK PA10K2 A10K2.t1359 = [0, 0, 176773216825, 1329654972656, 2165151189068, 852853254782, 51923819182, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
