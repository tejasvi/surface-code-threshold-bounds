import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11540 = true := by
  decide +kernel

theorem tot11540 : totK PD2M8K2 D2M8K2.t11540 = [0, 0, 211998592428, 486074084948, 178390334181, 8017271805, 0, 0] := by
  decide +kernel

theorem rows11541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11541 = true := by
  decide +kernel

theorem tot11541 : totK PD2M8K2 D2M8K2.t11541 = [0, 162235715068, 445306017370, 284597223362, 37201163166, 0, 0, 0] := by
  decide +kernel

theorem rows11542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11542 = true := by
  decide +kernel

theorem tot11542 : totK PD2M8K2 D2M8K2.t11542 = [0, 173378785273, 448285810236, 253184931211, 19519652623, 0, 0, 0] := by
  decide +kernel

theorem rows11543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11543 = true := by
  decide +kernel

theorem tot11543 : totK PD2M8K2 D2M8K2.t11543 = [0, 93406472932, 349647760579, 377373430543, 88056401541, 1249641317, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
