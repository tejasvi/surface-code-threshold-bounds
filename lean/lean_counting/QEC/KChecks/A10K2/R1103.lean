import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4412 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4412 = true := by
  decide +kernel

theorem tot4412 : totK PA10K2 A10K2.t4412 = [0, 0, 171544902261, 1055917632247, 2049121348145, 1204624446739, 195498568830, 6034215561, 0, 0] := by
  decide +kernel

theorem rows4413 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4413 = true := by
  decide +kernel

theorem tot4413 : totK PA10K2 A10K2.t4413 = [0, 0, 452623900372, 1692396630600, 1887499615799, 605590264169, 51663824867, 0, 0, 0] := by
  decide +kernel

theorem rows4414 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4414 = true := by
  decide +kernel

theorem tot4414 : totK PA10K2 A10K2.t4414 = [0, 0, 209103078700, 1433424628482, 2185524927405, 791621793580, 59604237579, 0, 0, 0] := by
  decide +kernel

theorem rows4415 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4415 = true := by
  decide +kernel

theorem tot4415 : totK PA10K2 A10K2.t4415 = [0, 0, 0, 647560014736, 2126363148939, 1599008024317, 269800140905, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
