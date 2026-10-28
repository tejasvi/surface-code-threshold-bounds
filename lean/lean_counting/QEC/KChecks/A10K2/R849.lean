import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3396 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3396 = true := by
  decide +kernel

theorem tot3396 : totK PA10K2 A10K2.t3396 = [0, 0, 441144930090, 1542951795351, 1733428711285, 846780479461, 154174150815, 6034215561, 0, 0] := by
  decide +kernel

theorem rows3397 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3397 = true := by
  decide +kernel

theorem tot3397 : totK PA10K2 A10K2.t3397 = [0, 0, 279086387381, 1505998709247, 2109005496617, 683852065855, 38312905762, 0, 0, 0] := by
  decide +kernel

theorem rows3398 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3398 = true := by
  decide +kernel

theorem tot3398 : totK PA10K2 A10K2.t3398 = [0, 0, 172257101782, 914743685299, 1949308465970, 1392801777558, 223382956298, 6354482628, 0, 0] := by
  decide +kernel

theorem rows3399 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3399 = true := by
  decide +kernel

theorem tot3399 : totK PA10K2 A10K2.t3399 = [0, 0, 560926345385, 1937932907507, 1999924500655, 514728856203, 26374032118, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
