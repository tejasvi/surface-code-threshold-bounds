import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4588 = true := by
  decide +kernel

theorem tot4588 : totK PD2M8K2 D2M8K2.t4588 = [0, 0, 166094524244, 481793424322, 255770057507, 12344751985, 0, 0] := by
  decide +kernel

theorem rows4589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4589 = true := by
  decide +kernel

theorem tot4589 : totK PD2M8K2 D2M8K2.t4589 = [0, 0, 0, 275774048146, 498484669104, 111444981452, 1240621948, 0] := by
  decide +kernel

theorem rows4590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4590 = true := by
  decide +kernel

theorem tot4590 : totK PD2M8K2 D2M8K2.t4590 = [0, 0, 0, 194912541794, 476404795626, 203164142206, 12488965933, 0] := by
  decide +kernel

theorem rows4591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4591 = true := by
  decide +kernel

theorem tot4591 : totK PD2M8K2 D2M8K2.t4591 = [0, 0, 0, 209050840099, 471173427823, 183738269567, 4708670653, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
