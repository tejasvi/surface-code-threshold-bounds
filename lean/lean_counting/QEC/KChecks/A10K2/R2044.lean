import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8176 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8176 = true := by
  decide +kernel

theorem tot8176 : totK PA10K2 A10K2.t8176 = [0, 0, 0, 45274709553, 830703047942, 2084699138859, 1565056357504, 296290850880, 11694325420, 0] := by
  decide +kernel

theorem rows8177 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8177 = true := by
  decide +kernel

theorem tot8177 : totK PA10K2 A10K2.t8177 = [0, 0, 0, 295402180247, 1339851254351, 2049979020795, 1051828066964, 110125839654, 0, 0] := by
  decide +kernel

theorem rows8178 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8178 = true := by
  decide +kernel

theorem tot8178 : totK PA10K2 A10K2.t8178 = [0, 0, 0, 464903275228, 1825604988434, 2027643802129, 584216589732, 16689849620, 0, 0] := by
  decide +kernel

theorem rows8179 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8179 = true := by
  decide +kernel

theorem tot8179 : totK PA10K2 A10K2.t8179 = [0, 0, 0, 0, 587553677432, 2009157170589, 1802668476027, 333383364734, 11918539728, 0] := by
  decide +kernel

end QECKChecks.A10K2
