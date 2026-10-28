import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2572 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2572 = true := by
  decide +kernel

theorem tot2572 : totK PA10K2 A10K2.t2572 = [503939570210, 1817678565820, 1923958402927, 556654347602, 32846095359, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2573 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2573 = true := by
  decide +kernel

theorem tot2573 : totK PA10K2 A10K2.t2573 = [0, 695856263765, 2061833793958, 1662824757979, 392274116972, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2574 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2574 = true := by
  decide +kernel

theorem tot2574 : totK PA10K2 A10K2.t2574 = [197293910428, 1012195150003, 1902707971416, 1411307190349, 243433885733, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2575 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2575 = true := by
  decide +kernel

theorem tot2575 : totK PA10K2 A10K2.t2575 = [584532985931, 1884387063788, 1792384003296, 512276974178, 31941609474, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
