import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7880 = true := by
  decide +kernel

theorem tot7880 : totK PD2M8K2 D2M8K2.t7880 = [0, 0, 174259487597, 472385852832, 251634635495, 19618674847, 0, 0] := by
  decide +kernel

theorem rows7881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7881 = true := by
  decide +kernel

theorem tot7881 : totK PD2M8K2 D2M8K2.t7881 = [0, 89273601505, 314735557580, 346032343087, 147818812933, 10608652373, 0, 0] := by
  decide +kernel

theorem rows7882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7882 = true := by
  decide +kernel

theorem tot7882 : totK PD2M8K2 D2M8K2.t7882 = [0, 198234855287, 448812503122, 219405310578, 17111997474, 0, 0, 0] := by
  decide +kernel

theorem rows7883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7883 = true := by
  decide +kernel

theorem tot7883 : totK PD2M8K2 D2M8K2.t7883 = [0, 104243526945, 415585367695, 326987092649, 35660815785, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
