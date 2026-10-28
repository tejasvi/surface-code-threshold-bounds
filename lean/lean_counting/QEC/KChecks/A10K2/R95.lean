import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows380 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t380 = true := by
  decide +kernel

theorem tot380 : totK PA10K2 A10K2.t380 = [0, 307352106778, 1466137284455, 2163886014645, 960488305589, 83186244116, 0, 0, 0, 0] := by
  decide +kernel

theorem rows381 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t381 = true := by
  decide +kernel

theorem tot381 : totK PA10K2 A10K2.t381 = [0, 107721783669, 619735243888, 1860352495356, 1814321397532, 432251438288, 25295400199, 0, 0, 0] := by
  decide +kernel

theorem rows382 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t382 = true := by
  decide +kernel

theorem tot382 : totK PA10K2 A10K2.t382 = [0, 520463895361, 1988766658437, 2039656081773, 543963645092, 26633081157, 0, 0, 0, 0] := by
  decide +kernel

theorem rows383 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t383 = true := by
  decide +kernel

theorem tot383 : totK PA10K2 A10K2.t383 = [0, 0, 687396576397, 2163523886369, 1770978913861, 368059437110, 12692412833, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
