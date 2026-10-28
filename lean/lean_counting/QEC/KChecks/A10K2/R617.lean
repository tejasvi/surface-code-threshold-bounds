import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2468 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2468 = true := by
  decide +kernel

theorem tot2468 : totK PA10K2 A10K2.t2468 = [0, 0, 0, 563442927351, 1942985732815, 1644890259078, 398731080277, 25239774317, 0, 0] := by
  decide +kernel

theorem rows2469 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2469 = true := by
  decide +kernel

theorem tot2469 : totK PA10K2 A10K2.t2469 = [0, 0, 314393602148, 1308434570974, 1889597859374, 1002063386993, 164620672964, 5365973533, 0, 0] := by
  decide +kernel

theorem rows2470 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2470 = true := by
  decide +kernel

theorem tot2470 : totK PA10K2 A10K2.t2470 = [0, 0, 414829995136, 1778601748404, 1848209762518, 467012866883, 31858652250, 0, 0, 0] := by
  decide +kernel

theorem rows2471 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2471 = true := by
  decide +kernel

theorem tot2471 : totK PA10K2 A10K2.t2471 = [0, 0, 200297707313, 1042315150083, 1951495422429, 1103115923417, 170162482128, 5528811039, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
