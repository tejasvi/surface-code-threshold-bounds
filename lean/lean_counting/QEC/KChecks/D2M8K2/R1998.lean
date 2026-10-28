import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7992 = true := by
  decide +kernel

theorem tot7992 : totK PD2M8K2 D2M8K2.t7992 = [0, 0, 67839213440, 331963167371, 407909070778, 101431288408, 1409560813, 0] := by
  decide +kernel

theorem rows7993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7993 = true := by
  decide +kernel

theorem tot7993 : totK PD2M8K2 D2M8K2.t7993 = [0, 0, 188192153266, 463741701603, 249711951529, 19700239858, 0, 0] := by
  decide +kernel

theorem rows7994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7994 = true := by
  decide +kernel

theorem tot7994 : totK PD2M8K2 D2M8K2.t7994 = [0, 0, 179395172564, 483853368889, 230038054908, 12373752831, 0, 0] := by
  decide +kernel

theorem rows7995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7995 = true := by
  decide +kernel

theorem tot7995 : totK PD2M8K2 D2M8K2.t7995 = [0, 0, 0, 288457074272, 502725094152, 101743541312, 1164319620, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
