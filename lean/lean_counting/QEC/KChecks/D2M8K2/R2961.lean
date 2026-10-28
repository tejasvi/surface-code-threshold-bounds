import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11844 = true := by
  decide +kernel

theorem tot11844 : totK PD2M8K2 D2M8K2.t11844 = [0, 0, 192817630493, 471662435257, 196559636839, 11898096860, 0, 0] := by
  decide +kernel

theorem rows11845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11845 = true := by
  decide +kernel

theorem tot11845 : totK PD2M8K2 D2M8K2.t11845 = [0, 0, 0, 312478548654, 440961909656, 73123898264, 1061529118, 0] := by
  decide +kernel

theorem rows11846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11846 = true := by
  decide +kernel

theorem tot11846 : totK PD2M8K2 D2M8K2.t11846 = [0, 89184852111, 179668821910, 226123920518, 277690921353, 77687341865, 3718133097, 0] := by
  decide +kernel

theorem rows11847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11847 = true := by
  decide +kernel

theorem tot11847 : totK PD2M8K2 D2M8K2.t11847 = [0, 180998137571, 466403063230, 225616664629, 12580527958, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
