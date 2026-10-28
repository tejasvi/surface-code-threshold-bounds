import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7624 = true := by
  decide +kernel

theorem tot7624 : totK PD2M8K2 D2M8K2.t7624 = [0, 201480901650, 478503311116, 219326254090, 12356293777, 0, 0, 0] := by
  decide +kernel

theorem rows7625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7625 = true := by
  decide +kernel

theorem tot7625 : totK PD2M8K2 D2M8K2.t7625 = [0, 34603710897, 323108759764, 452299426877, 92704798122, 1164319620, 0, 0] := by
  decide +kernel

theorem rows7626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7626 = true := by
  decide +kernel

theorem tot7626 : totK PD2M8K2 D2M8K2.t7626 = [0, 0, 198330785667, 474635149341, 191899915284, 11879463720, 0, 0] := by
  decide +kernel

theorem rows7627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7627 = true := by
  decide +kernel

theorem tot7627 : totK PD2M8K2 D2M8K2.t7627 = [0, 164801163194, 447751792585, 271198566553, 31215214646, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
