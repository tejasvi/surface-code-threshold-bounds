import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1308 = true := by
  decide +kernel

theorem tot1308 : totK PD2M8K2 D2M8K2.t1308 = [0, 118839580924, 354728199620, 318215990150, 81173700837, 3472187823, 0, 0] := by
  decide +kernel

theorem rows1309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1309 = true := by
  decide +kernel

theorem tot1309 : totK PD2M8K2 D2M8K2.t1309 = [0, 187453522826, 462325871174, 243620209044, 18418208341, 0, 0, 0] := by
  decide +kernel

theorem rows1310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1310 = true := by
  decide +kernel

theorem tot1310 : totK PD2M8K2 D2M8K2.t1310 = [0, 19036608703, 332176713054, 443021000230, 72854937599, 1053411165, 0, 0] := by
  decide +kernel

theorem rows1311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1311 = true := by
  decide +kernel

theorem tot1311 : totK PD2M8K2 D2M8K2.t1311 = [0, 106590470555, 345252890074, 329186093967, 81826407553, 3667207281, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
