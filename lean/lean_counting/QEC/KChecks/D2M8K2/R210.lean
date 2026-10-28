import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t840 = true := by
  decide +kernel

theorem tot840 : totK PD2M8K2 D2M8K2.t840 = [0, 0, 209137417036, 469588972307, 193355038484, 11367430297, 0, 0] := by
  decide +kernel

theorem rows841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t841 = true := by
  decide +kernel

theorem tot841 : totK PD2M8K2 D2M8K2.t841 = [0, 0, 187857271974, 482666970997, 228827548557, 12697780669, 0, 0] := by
  decide +kernel

theorem rows842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t842 = true := by
  decide +kernel

theorem tot842 : totK PD2M8K2 D2M8K2.t842 = [0, 200152141736, 474627971381, 196623171975, 9785860968, 2388935008, 0, 0] := by
  decide +kernel

theorem rows843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t843 = true := by
  decide +kernel

theorem tot843 : totK PD2M8K2 D2M8K2.t843 = [0, 197133337073, 470541333046, 214097955251, 12534051746, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
