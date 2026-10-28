import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2324 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2324 = true := by
  decide +kernel

theorem tot2324 : totK PA10K2 A10K2.t2324 = [0, 0, 500856004971, 1887919141072, 1985551241079, 505976531461, 11345765311, 0, 0, 0] := by
  decide +kernel

theorem rows2325 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2325 = true := by
  decide +kernel

theorem tot2325 : totK PA10K2 A10K2.t2325 = [0, 0, 0, 643209170329, 2097355759597, 1738214228850, 403201300042, 25660650750, 0, 0] := by
  decide +kernel

theorem rows2326 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2326 = true := by
  decide +kernel

theorem tot2326 : totK PA10K2 A10K2.t2326 = [0, 0, 512239663181, 1787695137053, 1955855168150, 743320634420, 69056990224, 0, 0, 0] := by
  decide +kernel

theorem rows2327 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2327 = true := by
  decide +kernel

theorem tot2327 : totK PA10K2 A10K2.t2327 = [0, 0, 321744867345, 1537138035557, 2198079387275, 840281161625, 51440488911, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
