import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10316 = true := by
  decide +kernel

theorem tot10316 : totK PD2M8K2 D2M8K2.t10316 = [0, 176244221605, 436880883054, 264384052470, 30211850834, 0, 0, 0] := by
  decide +kernel

theorem rows10317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10317 = true := by
  decide +kernel

theorem tot10317 : totK PD2M8K2 D2M8K2.t10317 = [0, 156166882922, 464829373996, 271632325218, 18721956145, 0, 0, 0] := by
  decide +kernel

theorem rows10318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10318 = true := by
  decide +kernel

theorem tot10318 : totK PD2M8K2 D2M8K2.t10318 = [0, 0, 291563798004, 512751347944, 101281697851, 1096505104, 0, 0] := by
  decide +kernel

theorem rows10319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10319 = true := by
  decide +kernel

theorem tot10319 : totK PD2M8K2 D2M8K2.t10319 = [0, 0, 209163727991, 496994428763, 177096425572, 5253830308, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
