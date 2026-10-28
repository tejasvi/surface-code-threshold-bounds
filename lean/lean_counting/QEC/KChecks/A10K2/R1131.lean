import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4524 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4524 = true := by
  decide +kernel

theorem tot4524 : totK PA10K2 A10K2.t4524 = [0, 354783864037, 1369314161062, 1955634000882, 1168928875866, 205658988676, 5624717336, 0, 0, 0] := by
  decide +kernel

theorem rows4525 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4525 = true := by
  decide +kernel

theorem tot4525 : totK PA10K2 A10K2.t4525 = [0, 443716125017, 1757621378043, 2043156278413, 670428170196, 39285800361, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4526 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4526 = true := by
  decide +kernel

theorem tot4526 : totK PA10K2 A10K2.t4526 = [0, 0, 594606946281, 2069504315301, 2026933456668, 474176363140, 13244237517, 0, 0, 0] := by
  decide +kernel

theorem rows4527 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4527 = true := by
  decide +kernel

theorem tot4527 : totK PA10K2 A10K2.t4527 = [301604122727, 764078323321, 717890209622, 1178236015769, 1359135312463, 525365468709, 49137922124, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
