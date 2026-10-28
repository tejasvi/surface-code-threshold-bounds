import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13464 = true := by
  decide +kernel

theorem tot13464 : totK PD2M8K2 D2M8K2.t13464 = [0, 0, 186932003959, 448362917013, 242301104692, 19478124415, 0, 0] := by
  decide +kernel

theorem rows13465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13465 = true := by
  decide +kernel

theorem tot13465 : totK PD2M8K2 D2M8K2.t13465 = [0, 0, 194568353146, 461427160426, 228562152495, 16988898864, 0, 0] := by
  decide +kernel

theorem rows13466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13466 = true := by
  decide +kernel

theorem tot13466 : totK PD2M8K2 D2M8K2.t13466 = [0, 0, 37670822061, 338603536632, 424520180387, 79618963564, 1096505104, 0] := by
  decide +kernel

theorem rows13467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13467 = true := by
  decide +kernel

theorem tot13467 : totK PD2M8K2 D2M8K2.t13467 = [0, 0, 28183367107, 275577211696, 465871810526, 122082424814, 3884009855, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
