import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6652 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6652 = true := by
  decide +kernel

theorem tot6652 : totK PA10K2 A10K2.t6652 = [0, 291625312176, 1502159605563, 2176157884057, 825253236693, 60544467592, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6653 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6653 = true := by
  decide +kernel

theorem tot6653 : totK PA10K2 A10K2.t6653 = [0, 0, 502191358822, 1753512922679, 1727575004631, 471858129123, 30650496230, 0, 0, 0] := by
  decide +kernel

theorem rows6654 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6654 = true := by
  decide +kernel

theorem tot6654 : totK PA10K2 A10K2.t6654 = [0, 566054583873, 1733640475633, 1790109037328, 607617774673, 54564457130, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6655 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6655 = true := by
  decide +kernel

theorem tot6655 : totK PA10K2 A10K2.t6655 = [0, 0, 947651728781, 2258412535038, 1216852601137, 118453847392, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
