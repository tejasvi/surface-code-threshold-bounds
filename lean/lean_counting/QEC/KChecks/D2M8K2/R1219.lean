import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4876 = true := by
  decide +kernel

theorem tot4876 : totK PD2M8K2 D2M8K2.t4876 = [0, 0, 0, 220918564925, 485273179883, 162051505499, 3368874774, 0] := by
  decide +kernel

theorem rows4877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4877 = true := by
  decide +kernel

theorem tot4877 : totK PD2M8K2 D2M8K2.t4877 = [0, 0, 0, 193775842144, 460482467225, 237492073849, 21117123477, 0] := by
  decide +kernel

theorem rows4878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4878 = true := by
  decide +kernel

theorem tot4878 : totK PD2M8K2 D2M8K2.t4878 = [0, 0, 0, 205008019428, 481997960257, 186298526496, 8818045175, 0] := by
  decide +kernel

theorem rows4879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4879 = true := by
  decide +kernel

theorem tot4879 : totK PD2M8K2 D2M8K2.t4879 = [0, 0, 0, 191286175152, 478801268755, 226060537592, 16277061306, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
