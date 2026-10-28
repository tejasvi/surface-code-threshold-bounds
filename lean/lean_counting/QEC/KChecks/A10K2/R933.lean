import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3732 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3732 = true := by
  decide +kernel

theorem tot3732 : totK PA10K2 A10K2.t3732 = [0, 0, 111960841626, 988285615964, 2231022651132, 1550191925576, 259734373161, 6962742351, 0, 0] := by
  decide +kernel

theorem rows3733 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3733 = true := by
  decide +kernel

theorem tot3733 : totK PA10K2 A10K2.t3733 = [0, 0, 565678425547, 1803535536283, 1693037715897, 577434851961, 56778554925, 0, 0, 0] := by
  decide +kernel

theorem rows3734 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3734 = true := by
  decide +kernel

theorem tot3734 : totK PA10K2 A10K2.t3734 = [0, 0, 129948670344, 1036055705161, 2026317162600, 1067660161503, 198907055918, 19313972475, 0, 0] := by
  decide +kernel

theorem rows3735 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3735 = true := by
  decide +kernel

theorem tot3735 : totK PA10K2 A10K2.t3735 = [0, 0, 294356378534, 1068080162627, 1750234275517, 1227654273346, 255754150211, 10760911071, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
