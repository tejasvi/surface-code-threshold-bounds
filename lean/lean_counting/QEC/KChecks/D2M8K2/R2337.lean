import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9348 = true := by
  decide +kernel

theorem tot9348 : totK PD2M8K2 D2M8K2.t9348 = [0, 0, 214501974623, 483560328405, 174256365204, 5155785308, 0, 0] := by
  decide +kernel

theorem rows9349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9349 = true := by
  decide +kernel

theorem tot9349 : totK PD2M8K2 D2M8K2.t9349 = [0, 0, 205113701904, 464947651508, 183188288984, 9652099503, 0, 0] := by
  decide +kernel

theorem rows9350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9350 = true := by
  decide +kernel

theorem tot9350 : totK PD2M8K2 D2M8K2.t9350 = [0, 0, 202920585483, 462599146027, 194127078062, 12297602142, 0, 0] := by
  decide +kernel

theorem rows9351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9351 = true := by
  decide +kernel

theorem tot9351 : totK PD2M8K2 D2M8K2.t9351 = [0, 41386975132, 304301547486, 456731710378, 110030298926, 1369587937, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
