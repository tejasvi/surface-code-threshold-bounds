import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3456 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3456 = true := by
  decide +kernel

theorem tot3456 : totK PA10K2 A10K2.t3456 = [0, 0, 0, 0, 592187068828, 2058058052903, 1617779812924, 245042660883, 6354482628, 0] := by
  decide +kernel

theorem rows3457 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3457 = true := by
  decide +kernel

theorem tot3457 : totK PA10K2 A10K2.t3457 = [0, 0, 0, 0, 577895136071, 1901677982987, 1738067313076, 464180747607, 32239129156, 0] := by
  decide +kernel

theorem rows3458 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3458 = true := by
  decide +kernel

theorem tot3458 : totK PA10K2 A10K2.t3458 = [0, 0, 0, 0, 519366920241, 1906725006684, 1867506522064, 443751590303, 18533161629, 0] := by
  decide +kernel

theorem rows3459 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3459 = true := by
  decide +kernel

theorem tot3459 : totK PA10K2 A10K2.t3459 = [0, 0, 0, 0, 463555320687, 1792754713610, 1876257682965, 475408746194, 31889781550, 0] := by
  decide +kernel

end QECKChecks.A10K2
