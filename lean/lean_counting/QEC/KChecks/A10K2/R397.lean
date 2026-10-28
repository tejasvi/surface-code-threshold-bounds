import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1588 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1588 = true := by
  decide +kernel

theorem tot1588 : totK PA10K2 A10K2.t1588 = [0, 0, 428173725744, 1784843626514, 2139756432419, 768558761292, 59214072530, 0, 0, 0] := by
  decide +kernel

theorem rows1589 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1589 = true := by
  decide +kernel

theorem tot1589 : totK PA10K2 A10K2.t1589 = [0, 0, 0, 777809781693, 2291703099916, 1751416122039, 296350482946, 6853348008, 0, 0] := by
  decide +kernel

theorem rows1590 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1590 = true := by
  decide +kernel

theorem tot1590 : totK PA10K2 A10K2.t1590 = [0, 372870017859, 1236859875103, 1280430465482, 790060142395, 875566823825, 370422949141, 29687484142, 0, 0] := by
  decide +kernel

theorem rows1591 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1591 = true := by
  decide +kernel

theorem tot1591 : totK PA10K2 A10K2.t1591 = [0, 470421043736, 1843126243481, 2004356592431, 538598439042, 16226811436, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
