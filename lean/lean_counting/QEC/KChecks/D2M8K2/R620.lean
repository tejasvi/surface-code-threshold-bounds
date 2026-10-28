import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2480 = true := by
  decide +kernel

theorem tot2480 : totK PD2M8K2 D2M8K2.t2480 = [0, 291785437234, 493526844272, 103447375056, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows2481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2481 = true := by
  decide +kernel

theorem tot2481 : totK PD2M8K2 D2M8K2.t2481 = [149847357467, 409062875396, 332914551618, 43380854154, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2482 = true := by
  decide +kernel

theorem tot2482 : totK PD2M8K2 D2M8K2.t2482 = [188940122064, 476641635555, 227830406926, 15508364590, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2483 = true := by
  decide +kernel

theorem tot2483 : totK PD2M8K2 D2M8K2.t2483 = [88183717169, 396775771916, 375959066591, 55126634818, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
