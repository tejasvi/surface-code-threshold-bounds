import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t884 = true := by
  decide +kernel

theorem tot884 : totK PD2M8K2 D2M8K2.t884 = [0, 170991135313, 445558768815, 260357241345, 31784647553, 0, 0, 0] := by
  decide +kernel

theorem rows885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t885 = true := by
  decide +kernel

theorem tot885 : totK PD2M8K2 D2M8K2.t885 = [0, 162890377827, 436336026794, 274330375839, 29596997383, 0, 0, 0] := by
  decide +kernel

theorem rows886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t886 = true := by
  decide +kernel

theorem tot886 : totK PD2M8K2 D2M8K2.t886 = [0, 89753051296, 375150941278, 365352045237, 60659489491, 1198073392, 0, 0] := by
  decide +kernel

theorem rows887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t887 = true := by
  decide +kernel

theorem tot887 : totK PD2M8K2 D2M8K2.t887 = [0, 0, 229668216068, 487192972817, 165642081411, 8466643012, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
