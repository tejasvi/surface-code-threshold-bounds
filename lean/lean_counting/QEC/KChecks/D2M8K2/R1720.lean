import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6880 = true := by
  decide +kernel

theorem tot6880 : totK PD2M8K2 D2M8K2.t6880 = [93924006320, 346325820688, 384821565533, 81225562505, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows6881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6881 = true := by
  decide +kernel

theorem tot6881 : totK PD2M8K2 D2M8K2.t6881 = [0, 264890536630, 497046921429, 141777414732, 3699256714, 0, 0, 0] := by
  decide +kernel

theorem rows6882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6882 = true := by
  decide +kernel

theorem tot6882 : totK PD2M8K2 D2M8K2.t6882 = [0, 183794706961, 465187893790, 222286566296, 17080783126, 0, 0, 0] := by
  decide +kernel

theorem rows6883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6883 = true := by
  decide +kernel

theorem tot6883 : totK PD2M8K2 D2M8K2.t6883 = [0, 168454325960, 475223442340, 230408796605, 9354552220, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
