import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1128 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1128 = true := by
  decide +kernel

theorem tot1128 : totK PA10K2 A10K2.t1128 = [0, 0, 566704506361, 1869495263064, 1775211585978, 521818167759, 50125290734, 0, 0, 0] := by
  decide +kernel

theorem rows1129 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1129 = true := by
  decide +kernel

theorem tot1129 : totK PA10K2 A10K2.t1129 = [0, 0, 151085706990, 1099341109608, 2096486988412, 1318432009604, 242674984028, 11918539728, 0, 0] := by
  decide +kernel

theorem rows1130 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1130 = true := by
  decide +kernel

theorem tot1130 : totK PA10K2 A10K2.t1130 = [0, 0, 278936468995, 1219107095909, 1960038750492, 1312878668129, 159907062993, 0, 0, 0] := by
  decide +kernel

theorem rows1131 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1131 = true := by
  decide +kernel

theorem tot1131 : totK PA10K2 A10K2.t1131 = [0, 0, 487641058152, 1773351646780, 1957355649438, 602937101581, 33055448423, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
