import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7576 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7576 = true := by
  decide +kernel

theorem tot7576 : totK PA10K2 A10K2.t7576 = [0, 0, 431788502220, 1738500551066, 2151540036620, 700484340461, 38670148117, 0, 0, 0] := by
  decide +kernel

theorem rows7577 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7577 = true := by
  decide +kernel

theorem tot7577 : totK PA10K2 A10K2.t7577 = [0, 578438043648, 1891333995843, 1762484452734, 588346703208, 229731352608, 37674658091, 0, 0, 0] := by
  decide +kernel

theorem rows7578 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7578 = true := by
  decide +kernel

theorem tot7578 : totK PA10K2 A10K2.t7578 = [0, 96573236373, 900120574923, 2083954178554, 1559823717777, 345836002371, 18355439443, 0, 0, 0] := by
  decide +kernel

theorem rows7579 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7579 = true := by
  decide +kernel

theorem tot7579 : totK PA10K2 A10K2.t7579 = [0, 302473110854, 1383627618954, 2111943019401, 1080631363606, 114732697551, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
