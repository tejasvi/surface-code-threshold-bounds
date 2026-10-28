import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3500 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3500 = true := by
  decide +kernel

theorem tot3500 : totK PA10K2 A10K2.t3500 = [0, 0, 0, 466342254351, 1698096538350, 1889678583905, 523310667116, 36266333350, 0, 0] := by
  decide +kernel

theorem rows3501 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3501 = true := by
  decide +kernel

theorem tot3501 : totK PA10K2 A10K2.t3501 = [0, 0, 0, 112574319960, 1273104093189, 2310445845050, 844348106369, 55456150709, 0, 0] := by
  decide +kernel

theorem rows3502 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3502 = true := by
  decide +kernel

theorem tot3502 : totK PA10K2 A10K2.t3502 = [0, 0, 0, 346042688399, 1277347454387, 1875731518475, 1000183122519, 185179544212, 6354482628, 0] := by
  decide +kernel

theorem rows3503 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3503 = true := by
  decide +kernel

theorem tot3503 : totK PA10K2 A10K2.t3503 = [0, 0, 0, 521933158885, 1879707277314, 1840698704784, 390252030183, 16709336065, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
