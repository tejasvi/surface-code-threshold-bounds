import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2640 = true := by
  decide +kernel

theorem tot2640 : totK PD2M8K2 D2M8K2.t2640 = [0, 0, 204131857371, 486532416013, 183829295084, 4627616211, 0, 0] := by
  decide +kernel

theorem rows2641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2641 = true := by
  decide +kernel

theorem tot2641 : totK PD2M8K2 D2M8K2.t2641 = [0, 0, 153375468926, 434482990427, 297952097572, 33047998259, 0, 0] := by
  decide +kernel

theorem rows2642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2642 = true := by
  decide +kernel

theorem tot2642 : totK PD2M8K2 D2M8K2.t2642 = [0, 0, 190384588041, 469666464594, 233292557475, 12844960481, 0, 0] := by
  decide +kernel

theorem rows2643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2643 = true := by
  decide +kernel

theorem tot2643 : totK PD2M8K2 D2M8K2.t2643 = [0, 0, 125503896557, 440504406062, 315177300205, 32619914848, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
