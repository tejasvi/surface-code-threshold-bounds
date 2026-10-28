import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6216 = true := by
  decide +kernel

theorem tot6216 : totK PD2M8K2 D2M8K2.t6216 = [0, 153782674338, 477810771158, 237519144219, 11023652771, 0, 0, 0] := by
  decide +kernel

theorem rows6217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6217 = true := by
  decide +kernel

theorem tot6217 : totK PD2M8K2 D2M8K2.t6217 = [0, 166793992307, 459535235739, 239926120791, 14051232035, 0, 0, 0] := by
  decide +kernel

theorem rows6218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6218 = true := by
  decide +kernel

theorem tot6218 : totK PD2M8K2 D2M8K2.t6218 = [0, 0, 286622228667, 467673861183, 84269848735, 1206465782, 0, 0] := by
  decide +kernel

theorem rows6219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6219 = true := by
  decide +kernel

theorem tot6219 : totK PD2M8K2 D2M8K2.t6219 = [0, 163898307800, 435068280553, 297621806455, 32762817837, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
