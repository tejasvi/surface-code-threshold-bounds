import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9576 = true := by
  decide +kernel

theorem tot9576 : totK PD2M8K2 D2M8K2.t9576 = [197939427042, 462044162996, 212269203874, 13776407499, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9577 = true := by
  decide +kernel

theorem tot9577 : totK PD2M8K2 D2M8K2.t9577 = [41656869575, 320079231356, 437485000751, 96993586074, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows9578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9578 = true := by
  decide +kernel

theorem tot9578 : totK PD2M8K2 D2M8K2.t9578 = [66869018694, 351315370845, 434702190053, 56877698371, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9579 = true := by
  decide +kernel

theorem tot9579 : totK PD2M8K2 D2M8K2.t9579 = [164443040794, 438161075013, 275838188059, 29688315834, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
