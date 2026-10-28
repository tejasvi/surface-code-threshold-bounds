import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7012 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7012 = true := by
  decide +kernel

theorem tot7012 : totK PA10K2 A10K2.t7012 = [0, 0, 297007965898, 1487229689098, 2161784259506, 838318387492, 60544467592, 0, 0, 0] := by
  decide +kernel

theorem rows7013 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7013 = true := by
  decide +kernel

theorem tot7013 : totK PA10K2 A10K2.t7013 = [0, 0, 75181334839, 655306833593, 1879328706071, 1658137799545, 365784184372, 12477124820, 0, 0] := by
  decide +kernel

theorem rows7014 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7014 = true := by
  decide +kernel

theorem tot7014 : totK PA10K2 A10K2.t7014 = [0, 0, 364062028007, 1619442701969, 1975831516723, 662456430653, 52178729445, 0, 0, 0] := by
  decide +kernel

theorem rows7015 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7015 = true := by
  decide +kernel

theorem tot7015 : totK PA10K2 A10K2.t7015 = [0, 0, 395918985492, 1615761064415, 2026962111228, 727890974462, 47276256389, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
