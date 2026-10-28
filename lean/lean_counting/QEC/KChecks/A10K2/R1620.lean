import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6480 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6480 = true := by
  decide +kernel

theorem tot6480 : totK PA10K2 A10K2.t6480 = [0, 0, 616509182687, 1995034757497, 1770540209353, 419873119372, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows6481 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6481 = true := by
  decide +kernel

theorem tot6481 : totK PA10K2 A10K2.t6481 = [0, 231394348301, 1025400705711, 1845660391530, 1299144216798, 220752355506, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows6482 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6482 = true := by
  decide +kernel

theorem tot6482 : totK PA10K2 A10K2.t6482 = [0, 452227343263, 1810754849125, 1887612540054, 498070429196, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6483 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6483 = true := by
  decide +kernel

theorem tot6483 : totK PA10K2 A10K2.t6483 = [0, 0, 695012620270, 2204226055174, 1456717072172, 148319882509, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
