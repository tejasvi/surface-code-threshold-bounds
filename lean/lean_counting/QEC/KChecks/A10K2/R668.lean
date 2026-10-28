import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2672 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2672 = true := by
  decide +kernel

theorem tot2672 : totK PA10K2 A10K2.t2672 = [0, 306047774799, 1170752335787, 1724867471375, 1225858357579, 268150562238, 10760911071, 0, 0, 0] := by
  decide +kernel

theorem rows2673 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2673 = true := by
  decide +kernel

theorem tot2673 : totK PA10K2 A10K2.t2673 = [0, 483623802477, 1808290556305, 1998546294404, 580227768083, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2674 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2674 = true := by
  decide +kernel

theorem tot2674 : totK PA10K2 A10K2.t2674 = [0, 0, 653688652669, 2078608465602, 1750055879378, 410050516217, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows2675 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2675 = true := by
  decide +kernel

theorem tot2675 : totK PA10K2 A10K2.t2675 = [0, 226848922415, 1099051799144, 1838222594008, 1259012983139, 220243798000, 6034215561, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
