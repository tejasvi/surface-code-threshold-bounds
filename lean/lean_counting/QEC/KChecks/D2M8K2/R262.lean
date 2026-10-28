import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1048 = true := by
  decide +kernel

theorem tot1048 : totK PD2M8K2 D2M8K2.t1048 = [0, 200064225234, 474968251793, 197652887232, 9740140984, 0, 0, 0] := by
  decide +kernel

theorem rows1049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1049 = true := by
  decide +kernel

theorem tot1049 : totK PD2M8K2 D2M8K2.t1049 = [0, 178446687271, 473381491361, 214702679769, 12421902774, 0, 0, 0] := by
  decide +kernel

theorem rows1050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1050 = true := by
  decide +kernel

theorem tot1050 : totK PD2M8K2 D2M8K2.t1050 = [0, 0, 321535617627, 450239837372, 73947971655, 1138244013, 0, 0] := by
  decide +kernel

theorem rows1051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1051 = true := by
  decide +kernel

theorem tot1051 : totK PD2M8K2 D2M8K2.t1051 = [0, 132395418751, 413305536074, 320306614602, 36800534143, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
