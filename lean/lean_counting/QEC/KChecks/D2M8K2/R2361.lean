import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9444 = true := by
  decide +kernel

theorem tot9444 : totK PD2M8K2 D2M8K2.t9444 = [155609748651, 457641571646, 266171836054, 24737759532, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9445 = true := by
  decide +kernel

theorem tot9445 : totK PD2M8K2 D2M8K2.t9445 = [150890891956, 442972888999, 276011611067, 21373993227, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9446 = true := by
  decide +kernel

theorem tot9446 : totK PD2M8K2 D2M8K2.t9446 = [0, 195371674985, 480261456856, 186485363296, 9587713104, 0, 0, 0] := by
  decide +kernel

theorem rows9447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9447 = true := by
  decide +kernel

theorem tot9447 : totK PD2M8K2 D2M8K2.t9447 = [87204366028, 344506319635, 357789043502, 88237255845, 3462014130, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
