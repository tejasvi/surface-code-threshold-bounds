import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4528 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4528 = true := by
  decide +kernel

theorem tot4528 : totK PA10K2 A10K2.t4528 = [458361379514, 1788883374292, 2002932871670, 569508157530, 32040661968, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4529 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4529 = true := by
  decide +kernel

theorem tot4529 : totK PA10K2 A10K2.t4529 = [0, 681263342069, 2072380393406, 1677163864908, 393201683838, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4530 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4530 = true := by
  decide +kernel

theorem tot4530 : totK PA10K2 A10K2.t4530 = [276491011440, 1231727531194, 1899828780256, 1178092803107, 209245271061, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4531 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4531 = true := by
  decide +kernel

theorem tot4531 : totK PA10K2 A10K2.t4531 = [502204280108, 1848938928980, 1929605607713, 546695676725, 31939474209, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
