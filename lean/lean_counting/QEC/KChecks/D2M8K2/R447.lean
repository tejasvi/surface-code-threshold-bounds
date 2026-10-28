import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1788 = true := by
  decide +kernel

theorem tot1788 : totK PD2M8K2 D2M8K2.t1788 = [0, 167767862951, 432649307953, 265071809760, 30315290444, 0, 0, 0] := by
  decide +kernel

theorem rows1789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1789 = true := by
  decide +kernel

theorem tot1789 : totK PD2M8K2 D2M8K2.t1789 = [0, 183081791668, 457365542918, 230205671023, 17104814242, 0, 0, 0] := by
  decide +kernel

theorem rows1790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1790 = true := by
  decide +kernel

theorem tot1790 : totK PD2M8K2 D2M8K2.t1790 = [0, 55267625348, 340383618659, 406746508347, 78624698947, 1096505104, 0, 0] := by
  decide +kernel

theorem rows1791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1791 = true := by
  decide +kernel

theorem tot1791 : totK PD2M8K2 D2M8K2.t1791 = [0, 22237561286, 272988304248, 471566673058, 121395695765, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
