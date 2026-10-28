import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6444 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6444 = true := by
  decide +kernel

theorem tot6444 : totK PA10K2 A10K2.t6444 = [0, 0, 479850183922, 1786656972632, 1910775598994, 636029604497, 62889663184, 0, 0, 0] := by
  decide +kernel

theorem rows6445 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6445 = true := by
  decide +kernel

theorem tot6445 : totK PA10K2 A10K2.t6445 = [0, 0, 295773208175, 1418679254738, 2170004087101, 1002970536857, 98421719230, 0, 0, 0] := by
  decide +kernel

theorem rows6446 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6446 = true := by
  decide +kernel

theorem tot6446 : totK PA10K2 A10K2.t6446 = [0, 0, 284564927155, 1293772095962, 1954960200578, 1119987790632, 204306650622, 7007974415, 0, 0] := by
  decide +kernel

theorem rows6447 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6447 = true := by
  decide +kernel

theorem tot6447 : totK PA10K2 A10K2.t6447 = [0, 0, 539273461554, 1962448809347, 2105104462089, 561235210996, 25068640818, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
