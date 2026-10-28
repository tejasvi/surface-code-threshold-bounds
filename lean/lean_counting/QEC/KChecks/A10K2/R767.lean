import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3068 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3068 = true := by
  decide +kernel

theorem tot3068 : totK PA10K2 A10K2.t3068 = [0, 0, 146298270939, 1098418710015, 2124380196334, 1329171957543, 261566042585, 20340910120, 0, 0] := by
  decide +kernel

theorem rows3069 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3069 = true := by
  decide +kernel

theorem tot3069 : totK PA10K2 A10K2.t3069 = [0, 0, 85721494493, 725559233224, 1889446303825, 1674820843813, 344279376232, 11202879745, 0, 0] := by
  decide +kernel

theorem rows3070 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3070 = true := by
  decide +kernel

theorem tot3070 : totK PA10K2 A10K2.t3070 = [0, 0, 557822838406, 1951100090129, 1843435432519, 450421405035, 26521581199, 0, 0, 0] := by
  decide +kernel

theorem rows3071 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3071 = true := by
  decide +kernel

theorem tot3071 : totK PA10K2 A10K2.t3071 = [0, 0, 15452630616, 750782078593, 2196449822175, 1429013770326, 202449232936, 5982052406, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
