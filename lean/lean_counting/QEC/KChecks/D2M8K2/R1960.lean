import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7840 = true := by
  decide +kernel

theorem tot7840 : totK PD2M8K2 D2M8K2.t7840 = [0, 0, 171274481493, 469286199895, 240803924455, 12384392272, 0, 0] := by
  decide +kernel

theorem rows7841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7841 = true := by
  decide +kernel

theorem tot7841 : totK PD2M8K2 D2M8K2.t7841 = [0, 0, 160092465416, 443486240548, 282369046951, 30080489471, 0, 0] := by
  decide +kernel

theorem rows7842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7842 = true := by
  decide +kernel

theorem tot7842 : totK PD2M8K2 D2M8K2.t7842 = [0, 0, 172196230041, 465003593181, 235333539979, 13768565698, 0, 0] := by
  decide +kernel

theorem rows7843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7843 = true := by
  decide +kernel

theorem tot7843 : totK PD2M8K2 D2M8K2.t7843 = [0, 0, 0, 340486390316, 505212989640, 58628597476, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
