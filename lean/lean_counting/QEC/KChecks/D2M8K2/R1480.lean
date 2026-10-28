import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5920 = true := by
  decide +kernel

theorem tot5920 : totK PD2M8K2 D2M8K2.t5920 = [162788535687, 442007768291, 277088972144, 30239336881, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5921 = true := by
  decide +kernel

theorem tot5921 : totK PD2M8K2 D2M8K2.t5921 = [209229565426, 481984910890, 208331299866, 10446638850, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5922 = true := by
  decide +kernel

theorem tot5922 : totK PD2M8K2 D2M8K2.t5922 = [23524547868, 271729125128, 413991444288, 189066131957, 21391863750, 0, 0, 0] := by
  decide +kernel

theorem rows5923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5923 = true := by
  decide +kernel

theorem tot5923 : totK PD2M8K2 D2M8K2.t5923 = [0, 200900773523, 476307615228, 202013557559, 7983871751, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
