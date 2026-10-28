import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10864 = true := by
  decide +kernel

theorem tot10864 : totK PD2M8K2 D2M8K2.t10864 = [0, 0, 172292400984, 455960791207, 250443978385, 27103937290, 0, 0] := by
  decide +kernel

theorem rows10865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10865 = true := by
  decide +kernel

theorem tot10865 : totK PD2M8K2 D2M8K2.t10865 = [0, 0, 174297120531, 452864870025, 258708978735, 15265226509, 0, 0] := by
  decide +kernel

theorem rows10866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10866 = true := by
  decide +kernel

theorem tot10866 : totK PD2M8K2 D2M8K2.t10866 = [0, 107656719942, 327451298258, 315790748364, 143846737252, 13566920432, 0, 0] := by
  decide +kernel

theorem rows10867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10867 = true := by
  decide +kernel

theorem tot10867 : totK PD2M8K2 D2M8K2.t10867 = [0, 195011420560, 452550459479, 221417467763, 15333191763, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
