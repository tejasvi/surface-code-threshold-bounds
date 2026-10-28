import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4736 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4736 = true := by
  decide +kernel

theorem tot4736 : totK PA10K2 A10K2.t4736 = [0, 0, 536875833161, 1895389986713, 1866131813179, 469354615952, 31179179504, 0, 0, 0] := by
  decide +kernel

theorem rows4737 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4737 = true := by
  decide +kernel

theorem tot4737 : totK PA10K2 A10K2.t4737 = [0, 0, 196526118449, 1443443398694, 2239953874272, 776203994408, 58121148856, 0, 0, 0] := by
  decide +kernel

theorem rows4738 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4738 = true := by
  decide +kernel

theorem tot4738 : totK PA10K2 A10K2.t4738 = [0, 316846731414, 1117922312175, 1352382857102, 1107391144817, 674769521841, 133756988527, 5546304973, 0, 0] := by
  decide +kernel

theorem rows4739 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4739 = true := by
  decide +kernel

theorem tot4739 : totK PA10K2 A10K2.t4739 = [0, 519396623446, 1872036644765, 1911159902379, 488857155314, 13227942247, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
