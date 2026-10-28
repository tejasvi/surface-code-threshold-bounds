import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4800 = true := by
  decide +kernel

theorem tot4800 : totK PD2M8K2 D2M8K2.t4800 = [0, 0, 285577972197, 497113701566, 111526776799, 1198073392, 0, 0] := by
  decide +kernel

theorem rows4801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4801 = true := by
  decide +kernel

theorem tot4801 : totK PD2M8K2 D2M8K2.t4801 = [0, 0, 207151033817, 472859595042, 190222049329, 12045711471, 0, 0] := by
  decide +kernel

theorem rows4802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4802 = true := by
  decide +kernel

theorem tot4802 : totK PD2M8K2 D2M8K2.t4802 = [0, 181849194956, 448646012138, 253117704987, 28936672904, 0, 0, 0] := by
  decide +kernel

theorem rows4803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4803 = true := by
  decide +kernel

theorem tot4803 : totK PD2M8K2 D2M8K2.t4803 = [0, 194557189004, 473700988047, 228948314774, 15084605089, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
