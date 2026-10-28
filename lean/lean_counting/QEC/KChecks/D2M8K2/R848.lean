import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3392 = true := by
  decide +kernel

theorem tot3392 : totK PD2M8K2 D2M8K2.t3392 = [0, 67193450784, 262200862389, 393979767514, 168775525981, 8078182869, 0, 0] := by
  decide +kernel

theorem rows3393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3393 = true := by
  decide +kernel

theorem tot3393 : totK PD2M8K2 D2M8K2.t3393 = [0, 173568875684, 454975383382, 265701127159, 25861863702, 0, 0, 0] := by
  decide +kernel

theorem rows3394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3394 = true := by
  decide +kernel

theorem tot3394 : totK PD2M8K2 D2M8K2.t3394 = [0, 89046023357, 359286525322, 387633912098, 73180310098, 1164319620, 0, 0] := by
  decide +kernel

theorem rows3395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3395 = true := by
  decide +kernel

theorem tot3395 : totK PD2M8K2 D2M8K2.t3395 = [0, 60801937767, 288762558689, 421822618078, 117609530061, 4008488258, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
