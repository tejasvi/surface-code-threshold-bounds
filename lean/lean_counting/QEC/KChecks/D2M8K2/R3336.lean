import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13344 = true := by
  decide +kernel

theorem tot13344 : totK PD2M8K2 D2M8K2.t13344 = [0, 0, 175160423845, 478313420754, 241070114503, 11890891214, 0, 0] := by
  decide +kernel

theorem rows13345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13345 = true := by
  decide +kernel

theorem tot13345 : totK PD2M8K2 D2M8K2.t13345 = [0, 0, 217707717389, 488540524496, 185322425183, 5089243333, 0, 0] := by
  decide +kernel

theorem rows13346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13346 = true := by
  decide +kernel

theorem tot13346 : totK PD2M8K2 D2M8K2.t13346 = [0, 0, 164719616843, 449686259084, 278214463140, 24005077078, 0, 0] := by
  decide +kernel

theorem rows13347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13347 = true := by
  decide +kernel

theorem tot13347 : totK PD2M8K2 D2M8K2.t13347 = [0, 0, 131240093091, 451589535172, 278920214492, 17757030023, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
