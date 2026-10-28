import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7976 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7976 = true := by
  decide +kernel

theorem tot7976 : totK PA10K2 A10K2.t7976 = [0, 0, 613737279027, 2031397233030, 1917579304200, 465258009220, 16972980469, 0, 0, 0] := by
  decide +kernel

theorem rows7977 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7977 = true := by
  decide +kernel

theorem tot7977 : totK PA10K2 A10K2.t7977 = [0, 0, 0, 687399700878, 2179683538121, 1766152861384, 286840891769, 6772895877, 0, 0] := by
  decide +kernel

theorem rows7978 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7978 = true := by
  decide +kernel

theorem tot7978 : totK PA10K2 A10K2.t7978 = [0, 0, 0, 429134734895, 1775725302561, 2171470991035, 683271667537, 30048946301, 0, 0] := by
  decide +kernel

theorem rows7979 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7979 = true := by
  decide +kernel

theorem tot7979 : totK PA10K2 A10K2.t7979 = [0, 0, 0, 639249217937, 1979980967276, 1750968096481, 418039258759, 38009196205, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
