import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3028 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3028 = true := by
  decide +kernel

theorem tot3028 : totK PA10K2 A10K2.t3028 = [0, 199895226948, 999438482584, 1958267623699, 1401102062872, 239658172800, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows3029 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3029 = true := by
  decide +kernel

theorem tot3029 : totK PA10K2 A10K2.t3029 = [0, 443649105951, 1801539941597, 1985401402185, 538618097421, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3030 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3030 = true := by
  decide +kernel

theorem tot3030 : totK PA10K2 A10K2.t3030 = [0, 91765184009, 857847187302, 2095965526992, 1437429279871, 203177879795, 5982052406, 0, 0, 0] := by
  decide +kernel

theorem rows3031 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3031 = true := by
  decide +kernel

theorem tot3031 : totK PA10K2 A10K2.t3031 = [0, 567294121113, 1930117060894, 1967741363990, 564873520526, 36887185061, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
