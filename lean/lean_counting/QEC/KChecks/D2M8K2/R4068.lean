import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16272 = true := by
  decide +kernel

theorem tot16272 : totK PD2M8K2 D2M8K2.t16272 = [0, 0, 181818599164, 469896107044, 250884695712, 23088263254, 0, 0] := by
  decide +kernel

theorem rows16273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16273 = true := by
  decide +kernel

theorem tot16273 : totK PD2M8K2 D2M8K2.t16273 = [0, 0, 165000193981, 477131711204, 249418126521, 12072969046, 0, 0] := by
  decide +kernel

theorem rows16274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16274 = true := by
  decide +kernel

theorem tot16274 : totK PD2M8K2 D2M8K2.t16274 = [0, 0, 0, 267220408493, 499351995988, 127383889342, 4166040359, 0] := by
  decide +kernel

theorem rows16275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16275 = true := by
  decide +kernel

theorem tot16275 : totK PD2M8K2 D2M8K2.t16275 = [0, 0, 157261717045, 445800999932, 287690906758, 31100197591, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
