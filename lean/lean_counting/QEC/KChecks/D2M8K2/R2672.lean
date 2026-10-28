import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10688 = true := by
  decide +kernel

theorem tot10688 : totK PD2M8K2 D2M8K2.t10688 = [0, 0, 0, 165149231940, 475112078037, 198221675534, 10918899928, 0] := by
  decide +kernel

theorem rows10689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10689 = true := by
  decide +kernel

theorem tot10689 : totK PD2M8K2 D2M8K2.t10689 = [0, 0, 0, 211443491520, 497236467299, 164615092487, 5265834820, 0] := by
  decide +kernel

theorem rows10690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10690 = true := by
  decide +kernel

theorem tot10690 : totK PD2M8K2 D2M8K2.t10690 = [0, 0, 94305354095, 407524233106, 389513727390, 45204917878, 0, 0] := by
  decide +kernel

theorem rows10691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10691 = true := by
  decide +kernel

theorem tot10691 : totK PD2M8K2 D2M8K2.t10691 = [0, 0, 173860125341, 460418299134, 262194443527, 18442880549, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
