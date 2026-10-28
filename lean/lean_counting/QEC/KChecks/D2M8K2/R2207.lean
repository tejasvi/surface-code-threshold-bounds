import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8828 = true := by
  decide +kernel

theorem tot8828 : totK PD2M8K2 D2M8K2.t8828 = [0, 0, 175032388950, 429690076550, 269235998781, 26280039449, 0, 0] := by
  decide +kernel

theorem rows8829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8829 = true := by
  decide +kernel

theorem tot8829 : totK PD2M8K2 D2M8K2.t8829 = [0, 0, 127326471390, 459833903304, 293513432446, 19263202544, 0, 0] := by
  decide +kernel

theorem rows8830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8830 = true := by
  decide +kernel

theorem tot8830 : totK PD2M8K2 D2M8K2.t8830 = [0, 0, 18114697088, 303975145040, 466636841124, 91643035381, 1332468113, 0] := by
  decide +kernel

theorem rows8831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8831 = true := by
  decide +kernel

theorem tot8831 : totK PD2M8K2 D2M8K2.t8831 = [0, 0, 185873174082, 463959493183, 239600259199, 20063464395, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
