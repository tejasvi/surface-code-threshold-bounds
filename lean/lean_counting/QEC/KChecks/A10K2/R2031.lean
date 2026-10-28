import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8124 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8124 = true := by
  decide +kernel

theorem tot8124 : totK PA10K2 A10K2.t8124 = [0, 0, 249260650121, 1419840680694, 2273576278541, 874203436219, 55662207290, 0, 0, 0] := by
  decide +kernel

theorem rows8125 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8125 = true := by
  decide +kernel

theorem tot8125 : totK PA10K2 A10K2.t8125 = [0, 0, 510873769769, 1862415908339, 2035259554074, 604395077604, 40697140545, 0, 0, 0] := by
  decide +kernel

theorem rows8126 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8126 = true := by
  decide +kernel

theorem tot8126 : totK PA10K2 A10K2.t8126 = [0, 0, 244336036153, 1300455319690, 2135623584698, 1262459638288, 226525493652, 6851704726, 0, 0] := by
  decide +kernel

theorem rows8127 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8127 = true := by
  decide +kernel

theorem tot8127 : totK PA10K2 A10K2.t8127 = [0, 0, 0, 613484598660, 2096622088456, 1967271537181, 408313211275, 6962742351, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
