import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2924 = true := by
  decide +kernel

theorem tot2924 : totK PD2M8K2 D2M8K2.t2924 = [0, 207341593153, 478007027753, 200320639163, 7651299259, 0, 0, 0] := by
  decide +kernel

theorem rows2925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2925 = true := by
  decide +kernel

theorem tot2925 : totK PD2M8K2 D2M8K2.t2925 = [0, 176825736941, 486057092687, 242298178470, 12227244834, 0, 0, 0] := by
  decide +kernel

theorem rows2926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2926 = true := by
  decide +kernel

theorem tot2926 : totK PD2M8K2 D2M8K2.t2926 = [0, 170174465498, 466794314273, 225577867531, 12574356851, 0, 0, 0] := by
  decide +kernel

theorem rows2927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2927 = true := by
  decide +kernel

theorem tot2927 : totK PD2M8K2 D2M8K2.t2927 = [0, 176335119313, 450414334931, 253090310953, 22828318141, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
