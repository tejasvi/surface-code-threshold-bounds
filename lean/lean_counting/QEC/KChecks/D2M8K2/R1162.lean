import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4648 = true := by
  decide +kernel

theorem tot4648 : totK PD2M8K2 D2M8K2.t4648 = [0, 0, 193124114836, 482053621312, 231301907897, 12247173712, 0, 0] := by
  decide +kernel

theorem rows4649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4649 = true := by
  decide +kernel

theorem tot4649 : totK PD2M8K2 D2M8K2.t4649 = [0, 0, 16141487850, 303835930755, 470927962812, 104841912215, 1268739303, 0] := by
  decide +kernel

theorem rows4650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4650 = true := by
  decide +kernel

theorem tot4650 : totK PD2M8K2 D2M8K2.t4650 = [0, 0, 0, 218536544877, 496457274468, 168842528923, 5070749721, 0] := by
  decide +kernel

theorem rows4651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4651 = true := by
  decide +kernel

theorem tot4651 : totK PD2M8K2 D2M8K2.t4651 = [0, 162906912950, 334787191007, 127769247101, 144676849500, 116179156346, 11868390580, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
