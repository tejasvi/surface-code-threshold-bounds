import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.t12 = true := by
  decide +kernel

theorem tot12 : totK PA6K2 A6K2.t12 = [357242426959, 1421640407503, 1899548524788, 727212887395, 60016229439, 0] := by
  decide +kernel

end QECKChecks.A6K2
