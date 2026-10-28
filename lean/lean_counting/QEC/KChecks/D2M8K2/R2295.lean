import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9180 = true := by
  decide +kernel

theorem tot9180 : totK PD2M8K2 D2M8K2.t9180 = [0, 155316677276, 467445787963, 240719596591, 11127237002, 0, 0, 0] := by
  decide +kernel

theorem rows9181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9181 = true := by
  decide +kernel

theorem tot9181 : totK PD2M8K2 D2M8K2.t9181 = [0, 192565357731, 471612561011, 211468821245, 12403393969, 0, 0, 0] := by
  decide +kernel

theorem rows9182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9182 = true := by
  decide +kernel

theorem tot9182 : totK PD2M8K2 D2M8K2.t9182 = [0, 219341329755, 488127640722, 179331181587, 5274443905, 0, 0, 0] := by
  decide +kernel

theorem rows9183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9183 = true := by
  decide +kernel

theorem tot9183 : totK PD2M8K2 D2M8K2.t9183 = [94305354095, 242592834031, 346660195811, 216371170090, 17433533548, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
